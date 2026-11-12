module

public import Green64.Library.Sieve.Foundations.Part025
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part020
public import Green64.Library.Sieve.Foundations.Part022

@[expose] public section

/-!
# Sieve / Foundations / Part026

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalFullOddDyadicEvents -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The exact REAL h=-2 physical full odd-e original Parity carrier at
fixed e,m,k, BEFORE dyadic Z partition, including every populated
original Q/P/B509 two-endpoint n and m' but NO zero/unsupported n.
This is now allowed for all e in the FULL odd interval, not only
from selected-Q source e. -/
def parityOriginalHistoricalFullOddKPhysicalEvents434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  ((parityOriginalHistoricalKPrimeFibre434 e m K k).product J).filter
    (fun q => parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m q.1 q.2)

/-- Actual ORIGINAL binary z scale for a real physical (m',n)
Q/P source event, at fixed e,m. -/
def parityOriginalHistoricalPhysicalZScaleOfEvent434
    (e m : ℕ) (q : ℕ×ℕ) : ℕ :=
  parityOriginalHistoricalActualZDyadicScale434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)

/-- On the true original h=-2 physical TWO-ENDPOINT carrier and
odd e, EVERY real source canonical z is strictly positive.
Therefore imposing positivity before dyadic Z grouping does NOT
remove a genuine source event or silently add an unsupported one.
The binary Z-fibre is EXACTLY the original already constructed
`ActualKZPhysicalEventCarrier434` used by 3D source Fourier.
This is source-to-Fourier SUPPORT equality, not a cancellation bound. -/
theorem parity_original_historical_full_odd_Z_event_fibre_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) :
    (parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).filter
      (fun q => parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q=Z) =
    parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z := by
  ext q
  constructor
  · intro hq
    obtain ⟨hBase,hScale⟩ := Finset.mem_filter.mp hq
    obtain ⟨hProd,hValid⟩ := Finset.mem_filter.mp hBase
    have hNe : m≠q.1 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hProd).1).1).1.symm
    have hPos := parity_original_historical_supported_canonical_z_positive_shift434
      d L band slot δ Y e m q.1 q.2 he hNe hValid
    exact Finset.mem_filter.mpr ⟨hProd,⟨hValid,hPos.2.1,hScale⟩⟩
  · intro hq
    obtain ⟨hProd,⟨hValid,hPos,hScale⟩⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hProd,hValid⟩,hScale⟩

/-- Original signed complex physical m'×n source partition into
its GENUINE attained binary Z images, preserving exactly one
physical source event per dyadic cell; no #Z or source collision
multiplicity loss, no reweighted Q/P gates or extension to whole
unrestricted z interval. Holds for arbitrary original complex W. -/
theorem parity_original_historical_full_odd_k_Z_image_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (W : (ℕ×ℕ) → ℂ) :
    (∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q) =
    ∑Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,W q := by
  let S := parityOriginalHistoricalFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  have hReindex : (∑q∈S,W q) =
      ∑Z∈S.image g,∑q∈S.filter (fun q=>g q=Z),W q := by
    have h := Finset.sum_image' (s:=S) (g:=g)
      (f:=fun Z => ∑q∈S.filter (fun q=>g q=Z),W q)
      W (by intro q hq; rfl)
    exact h.symm
  calc
    _ = ∑Z∈S.image g,∑q∈S.filter (fun q=>g q=Z),W q := hReindex
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [parity_original_historical_full_odd_Z_event_fibre_exact434
        d L band slot δ Y e m K J k Z he]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddKZSourceFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Complete exact original Parity(4.13) FULL-odd-e, n≤3V
physical signed character fibre at one e,m,k,χ is the sum
of the original physical eta_e,L*eta_n weighted cofactor terms
in ALL attained binary z-dyadic Z cells. Every term keeps its
actual SOURCE Q/P/B509 gates, χ(m') and original b629 alpha.

This is an equality of genuine complex sums, not a majorant,
and no L,|k|,Z or #characters factor is paid. It is the exact
SOURCE link to the pre-existing 3D Fourier theorem for each Z.
The real original selected-Q e restriction was safely enlarged
ONLY before Cauchy, so arbitrary odd e is now permitted here. -/
theorem parity_original_historical_full_odd_k_character_eq_sum_actual_Z434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e) :
    let S := parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
    (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      χ (mp : ZMod (2*k.natAbs)) *
      (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
          d L band slot δ Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434
            d L band slot δ Y e m mp),
          ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp)) =
    ∑Z∈S.image g,
      parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ := by
  dsimp only
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let S := parityOriginalHistoricalFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hL
  let W : ℕ×ℕ → ℂ := fun q =>
    χ (q.1 : ZMod (2*k.natAbs)) *
    (((w e q.2:ℝ):ℂ) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1)
  have hSingle (mp : ℕ) (hmp : mp∈M) :
      (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
          d L band slot δ Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          ((w e n:ℝ):ℂ) *
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) =
      ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp),
        ((w e n:ℝ):ℂ)*
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
    let F : ℕ → ℂ := fun n =>
      ((w e n:ℝ):ℂ) *
        parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp
    have hZ := parity_original_historical_n_sum_eq_canonical_z_fibres434
      e m mp J F
    have hPhysical := parity_original_historical_weighted_z_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp
      (fun n=>((w e n:ℝ):ℂ)) J
    have hFiltered := parity_original_historical_weighted_N_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp
      (fun n=>((w e n:ℝ):ℂ)) J
    exact hPhysical.symm.trans (hZ.symm.trans hFiltered)
  have hFirst :
      (∑mp∈M,χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            ((w e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)) =
      ∑mp∈M,χ (mp : ZMod (2*k.natAbs)) *
        (∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
             d L band slot δ Y e m mp),
          ((w e n:ℝ):ℂ) *
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) := by
    apply Finset.sum_congr rfl
    intro mp hmp
    rw [hSingle mp hmp]
  have hEvents :
      (∑mp∈M,χ (mp : ZMod (2*k.natAbs)) *
        (∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
             d L band slot δ Y e m mp),
          ((w e n:ℝ):ℂ)*
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp)) =
      ∑q∈S,W q := by
    unfold S parityOriginalHistoricalFullOddKPhysicalEvents434
    rw [Finset.sum_filter]
    have hProd :
        (∑q∈M.product J,
          if parityOriginalHistoricalPhysicalValidN434
            d L band slot δ Y e m q.1 q.2 then W q else 0) =
        ∑mp∈M,∑n∈J,
          if parityOriginalHistoricalPhysicalValidN434
            d L band slot δ Y e m mp n then W (mp,n) else 0 :=
      Finset.sum_product M J (fun q : ℕ×ℕ =>
        if parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m q.1 q.2 then W q else 0)
    rw [hProd]
    apply Finset.sum_congr rfl
    intro mp hmp
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hValid : parityOriginalHistoricalPhysicalValidN434
        d L band slot δ Y e m mp n
    · simp only [if_pos hValid]
      dsimp [W]
    · simp only [if_neg hValid, mul_zero]
  have hZ := parity_original_historical_full_odd_k_Z_image_reindex434
    d L band slot δ Y e m K J k he W
  have hLast :
      (∑Z∈S.image g,
        ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
          d L band slot δ Y e m K J k Z,W q) =
      ∑Z∈S.image g,
        parityOriginalHistoricalActualKZPhysicalWeightedSource434
          d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ := by
    apply Finset.sum_congr rfl
    intro Z hZ
    unfold parityOriginalHistoricalActualKZPhysicalWeightedSource434
      parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    apply Finset.sum_congr rfl
    intro q hq
    dsimp [W,w]
    ring
  exact hFirst.trans (hEvents.trans (hZ.trans hLast))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddB633FourierCell -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Literal original Parity (4.14)--(4.16) true physical k/Z Fourier
cell with the SAME constructed moving η_e η_n 3D Euclidean Schwartz
multiplier, real fixed U/U/Z scale phases, and exactly the B633
Parity original complex prime-slot pair at z and z+2k, with actual
SOURCE R20 H0/B509 residual and α/χ/sign. This represents the
original fixed e,m,k,χ physical signed Fourier cell, not an
unrestricted (4.17) saving or a positive surrogate. -/
def parityOriginalHistoricalActualB6333DFourierCell434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L) (Z : ℕ) (k : ℤ)
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
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K α (2*k.natAbs) χ 0 0
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport
  let scale := parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
    parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
    parityOriginalHistoricalFourierScalePhase434 (Z:ℝ) (ζ 2)
  (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * scale *
    (∑q∈S,parityOriginalHistoricalB633PhysicalPairTerm434
      L rho (2*Real.pi*(ζ 0)) (2*Real.pi*(ζ 1))
      (2*Real.pi*(ζ 2)) signed α F.residual (2*k.natAbs) χ F.lo F.hi m q.1
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
      (((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat))

/-- COMPLETE single SOURCE physical e,m,k,Z,χ 3D Fourier
identity including the OUTER Parity(2.6) conjugate χ(m). From the
literal H0/Q/P/B509 r20 h=-2 weighted source and exact smooth
η_e,L η_n normalizations, the complex signed physical χ fibre is
exactly the (non-truncated) Euclidean Fourier integral of the
literal B633 prime-slot Parity(4.16) pair kernel. The 2π, U/U/Z,
signed negative k, ζ frequencies, two P-ordinary parts and both
signs are all retained; no replacement of source z support by an
unrestricted interval nor a spectral estimate is inserted. -/
theorem parity_original_historical_true_k_Z_chi_B633_fourier_integral434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hZ : 0<Z) :
    star (χ (m : ZMod (2*k.natAbs))) *
      parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hBufSmooth hBufSupport ζ := by
  have hSource := parity_original_historical_actual_k_z_physical_fourier434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hBufSmooth hBufSupport hBufOne hZ
  rw [hSource]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ζ
  have hTwist := parity_original_historical_actual_k_z_twisted_physical_factor434
    d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
    buf a b hBufSmooth hBufSupport ζ
  rw [hTwist]
  have hZreal : (0:ℝ)<(Z:ℝ) := by exact_mod_cast hZ
  have hB633 := parity_original_historical_actual_k_z_3d_fourier_eq_B633434
    d L U E V hL band slot δ ξ K J α Y e m he k Z χ rho signed
    hU hZ buf a b hBufSmooth hBufSupport ζ
  dsimp only [parityOriginalHistoricalActualB6333DFourierCell434]
  exact hB633
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddCompleteZFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Every attained TRUE binary Z from the original full odd-e
physical k,m',n source carrier is strictly positive, as forced by
actual h=-2 two-sided Q/P gates and original odd e, not by an
invented positive z window. Makes full 3D Fourier inversion
legitimate on EVERY attained cell. -/
theorem parity_original_historical_full_odd_attained_Z_pos434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k Z : ℕ)
    (he : Odd e)
    (hZ : Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J (k:ℤ)).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)) :
    0<Z := by
  obtain ⟨q,hq,hqZ⟩ := Finset.mem_image.mp hZ
  obtain ⟨hqProduct,hValid⟩ := Finset.mem_filter.mp hq
  have hNe : m≠q.1 :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp
      (Finset.mem_product.mp hqProduct).1).1).1.symm
  have hPositive := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m q.1 q.2 he hNe hValid
  have hDyadic := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hPositive.2.1
  have hscale : parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)=Z := hqZ
  rw [←hscale]
  exact hDyadic.1

/-- ACTUAL ORIGINAL Parity (4.10)--(4.16) one (e,m,k,χ) FULL odd-e,
all n≤3V weighted signed physical cofactor source equals the
sum over ALL and ONLY its physically attained binary dyadic Z
cells of the literal REAL 3D Euclidean Fourier integrals of the
B633 original 2-prime-slot source correlation. Importantly, the
conjugate χ(m) outside the source and χ(m') inside, the original
Q/P/B509 factorization vStar/vpStar and the 2π U/U/Z phases are
kept EXACT. There is no polynomial tail left as a hypothesis here:
it is an exact non-truncated Fourier identity on the source cells.

This *does not* assert that the complex signed finite pair sum on
each attained Z is the unrestricted full Parity(4.17) correlation. That
last full-support/smooth ψ_Z identification and its saving remain
OPEN; however the old sparse selected-Q e obstruction is already
eliminated by the pre-Gram full-odd positive majorant theorem. -/
theorem parity_original_historical_full_odd_k_character_eq_all_Z_B633_fourier434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    let S := parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
    star (χ (m : ZMod (2*k.natAbs))) *
      (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434
              d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)) =
    ∑Z∈S.image g,
      (∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hBufSmooth hBufSupport ζ) := by
  dsimp only
  let S := parityOriginalHistoricalFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  have hSource := parity_original_historical_full_odd_k_character_eq_sum_actual_Z434
    d L E V hL band slot δ ξ rho α signed Y e m K J k χ he
  dsimp only at hSource
  rw [hSource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Z hZ
  have hZPos : 0<Z := by
    obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hZ
    have hQbase := (Finset.mem_filter.mp hq)
    have hQprod := Finset.mem_product.mp hQbase.1
    have hmpMem := Finset.mem_filter.mp hQprod.1
    have hNe : m≠q.1 := (Finset.mem_erase.mp hmpMem.1).1.symm
    have hPos := parity_original_historical_supported_canonical_z_positive_shift434
      d L band slot δ Y e m q.1 q.2 he hNe hQbase.2
    have hdy := parity_original_historical_actual_z_in_own_dyad434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hPos.2.1
    change parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)=Z at hEq
    rw [←hEq]
    exact hdy.1
  have hCell := parity_original_historical_true_k_Z_chi_B633_fourier_integral434
    d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ he
    hU hE hV hmLo hmHi hDyad
    buf a b hBufSmooth hBufSupport hBufOne hZPos
  exact hCell
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddB633FourierOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23500000

/-- The COMPLETE original Parity(4.13)--(4.16) full odd-e FULL
character-outer physical offdiagonal, in its exact Euclidean
3D Fourier form, with every original positive e, true m, nonzero
signed k, original χ mod 2|k|, and genuine attained dyadic Z.
For each Z the kernel is the REAL literal b633/Parity(4.16)
convolution source with original B509 reserved H0, real W1,
epsilon=1/E, alpha and conjugation, 2π phases and fixed U/U/Z.
The original coefficient cχ stays OUTSIDE the whole Fourier
cell and all physical (m',n) sums. No spectral 4.17 cancellation
or imaginary extension to unsupported z has yet been used. -/
def parityOriginalHistoricalFullOddB633FourierOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
              d L band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k).image
                (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
            ∫ζ : EuclideanSpace ℝ (Fin 3),
              parityOriginalHistoricalActualB6333DFourierCell434
                d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) χ
                buf a b hBufSmooth hBufSupport ζ)

/-- FINAL EXACT ORIGINAL Parity (4.10)--(4.16) full-odd-e signed
SOURCE-TO-LITERAL-B633 3D Fourier JOIN, after the LEGITIMATE
pre-Gram enlargement of the Cauchy-positive physical source.

For the ACTUAL constructed moving eta_e,L eta_n, original full
odd e<=2E, all n<=3V, the complex character-outer signed
physical correlation is EQUAL to a sum over real e,m,k,χ, and
ALL attained binary Z cells of 3D Fourier integrals of the literal
original B633/Parity(4.16) TWO-PRIME-SLOT physical correlations.
All original real source Q/P/H0 gates, B509 skipped-Q residual,
alpha, epsilon, chi conjugation and Parity 2.6 mask coefficient are
still present, with correct 2π U/U/Z normalization and physical
z>0,z+2k>0, without phantom source terms or any analytic
hypothesis on a full unrestricted 4.17 correlation.

OPEN: prove cancellation for THESE exact physical Fourier cell
sums from Parity4.17, including ψ_Z smooth cutoff, full two-core
source arithmetic mask and beta/4 gate, then sum losses to
Parity Type II(4.2). The equality below alone does NOT do that. -/
theorem parity_original_historical_full_odd_character_outer_eq_B633_3d_fourier434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    parityOriginalHistoricalFullOddCharacterOuter434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V)
      α signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) =
    parityOriginalHistoricalFullOddB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hBufSmooth hBufSupport := by
  unfold parityOriginalHistoricalFullOddCharacterOuter434
    parityOriginalHistoricalFullOddB633FourierOuter434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  apply Finset.sum_congr rfl
  intro m hm
  have hmD := hDyad m hm
  have hDyad' : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    have h := hDyad mp hmp
    exact ⟨h.1,h.2.le⟩
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ hχ
  have hFour := parity_original_historical_full_odd_k_character_eq_all_Z_B633_fourier434
    d L U E V hL band slot δ ξ rho α signed Y e m K
    (parityOriginalHistoricalFullNEnvelope434 V) k χ heOdd
    hU hE hV hmD.1 hmD.2.le hDyad'
    buf a b hBufSmooth hBufSupport hBufOne
  dsimp only at hFour
  calc
    (parityShiftTwoMaskCoefficient434 k.natAbs χ *
      star (χ (m : ZMod (2*k.natAbs)))) *
      (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        χ (mp : ZMod (2*k.natAbs)) *
          (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
              d L band slot δ Y e m mp
              (parityOriginalHistoricalFullNEnvelope434 V),
            ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434
              e m mp (parityOriginalHistoricalFullNEnvelope434 V) z).filter
                (parityOriginalHistoricalPhysicalValidN434
                  d L band slot δ Y e m mp),
              ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
                parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp)) =
    parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (star (χ (m : ZMod (2*k.natAbs))) *
      (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        χ (mp : ZMod (2*k.natAbs)) *
          (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
              d L band slot δ Y e m mp
              (parityOriginalHistoricalFullNEnvelope434 V),
            ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434
              e m mp (parityOriginalHistoricalFullNEnvelope434 V) z).filter
                (parityOriginalHistoricalPhysicalValidN434
                  d L band slot δ Y e m mp),
              ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
                parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp))) := by ring
    _ = parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑ Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
              d L band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k).image
                (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
          ∫ζ : EuclideanSpace ℝ (Fin 3),
            parityOriginalHistoricalActualB6333DFourierCell434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hBufSmooth hBufSupport ζ) := by rw [hFour]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFourierTypeIIReduction -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- END-TO-END ORIGINAL h=-2 Parity(4.10)--(4.16) honest Fourier
Type-II precursor, with a genuine fixed smooth buffer and FULL
odd-e/n character-outer physical SOURCE after PRE-GRAM Cauchy
positivity enlargement. The ONLY outstanding analytic term is the
NORM of an EXACT Euclidean R³ Fourier sum of literal B633 two-prime-
slot Parity(4.16) pair kernels on ALL physically attained Z cells.

 |A_source|² ≤ (true ORIGINAL Σ|a_e beta_n|²) ×
   (2 Acoef² exp L L^(2CW1+344) + ||B633FullOddFourierOuter||).

No saving on this correlation is claimed. The signed source r0=20,
h=-2, sigma=0, original Q/P/B509 skipped-Q residual, actual
b629 fine cofactor, chi conjugation, both original epsilon=1/E,
three logarithmic Fourier factors at 2π with true U/U/Z normalizing
phase, and exactly the true binary attained Z fibres are retained.
No illicit inequality between subset and full signed sums or extra
number-of-characters factor. This is not Parity TypeII(4.2) or final
Green64.green_64. -/
theorem parity_eventually_original_full_odd_Cauchy_diag_B633_3d_fourier_bound434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma)
    (A : ℝ) (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K J : Finset ℕ) (β : ℕ → ℂ)
        (prime signed : Bool) (lFine uFine : ℕ) (Acoef : ℝ),
      0<U → 0<V → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      let Amass := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
      Amass *
        (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
          ‖parityOriginalHistoricalFullOddB633FourierOuter434
            (sourceOriginalLiteralDepth 20 L) L U E V hLw
            band slot δ ξ rho K alpha signed ⌊2*Real.exp L⌋₊
            buf (-Real.log A) (Real.log A) hSmooth hSupport‖) := by
  filter_upwards [parity_eventually_original_full_odd_Cauchy_diag_character_outer_bound434
    S beta gamma K0 hS hbeta hgamma] with L hOld
  refine ⟨hOld.1,hOld.2.1,?_⟩
  intro hLw band slot δ ξ U E V rho K J betaSeq prime signed lFine uFine Acoef
    hU hV hScale hDyad hNRange hl hFineLow
  dsimp only
  intro hAcoef hAlpha
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  have hOriginal := hOld.2.2 hLw band slot δ ξ U E V rho K J betaSeq
    prime signed lFine uFine Acoef hU hV hScale hDyad hNRange hl hFineLow
    hAcoef hAlpha
  have hEpos : 0<E := by
    rw [hScale]
    have hLpos : 0<L := by linarith [hOld.2.1]
    exact mul_pos hU (Real.rpow_pos_of_pos hLpos _)
  have hFourier := parity_original_historical_full_odd_character_outer_eq_B633_3d_fourier434
    (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
    K alpha signed ⌊2*Real.exp L⌋₊ hU hEpos hV hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport hOne
  dsimp only at hOriginal
  rw [hFourier] at hOriginal
  exact hOriginal

/-- The preceding end-to-end original signed Cauchy-to-3D-Fourier
bound can be formulated with one ACTUALLY CONSTRUCTED log buffer,
chosen globally BEFORE the source large-L limit and all physical
k,Z,χ, and all fine/source allocation choices.

The buffer is fixed independent of L and provides C∞, support in
[-log A,log A] and exact [0,log 2] plateau. No hypothetical fixed
smooth cutoff is supplied externally. The final Parity(4.17) restricted
pair-mask cancellation and Type II saving remain OPEN. -/
theorem parity_original_full_odd_genuine_buffer_B633_fourier_exists434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∃ A : ℝ, 64≤A ∧ ∃ buf : ℝ → ℂ,
      ∃ (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) ∧
      (∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
        ∀ (hLw : 8≤L)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
          (δ : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool)
          (ξ : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → ℝ)
          (U E V rho : ℝ) (K J : Finset ℕ) (β : ℕ → ℂ)
          (prime signed : Bool) (lFine uFine : ℕ) (Acoef : ℝ),
        0<U → 0<V → E=U*L^(-K0) →
        (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
        2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
        let Amass := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ,
          ∑n∈J,‖parityOriginalHistoricalWindowAE434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2
        ‖parityOriginalHistoricalCauchyAtDelta434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
        Amass *
          (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
            ‖parityOriginalHistoricalFullOddB633FourierOuter434
              (sourceOriginalLiteralDepth 20 L) L U E V hLw
              band slot δ ξ rho K alpha signed ⌊2*Real.exp L⌋₊
              buf (-Real.log A) (Real.log A) hSmooth hSupport‖)) := by
  obtain ⟨A,hA,buf,hSmooth,hSupport,hOne,hNorm,K,hK,hBudgets⟩ :=
    parity_original_historical_fixed_log_buffer_exists434
  exact ⟨A,hA,buf,hSmooth,hSupport,hOne,
    parity_eventually_original_full_odd_Cauchy_diag_B633_3d_fourier_bound434
      S beta gamma K0 hS hbeta hgamma A buf hSmooth hSupport hOne⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddSmoothedRanges -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Actual original source moving smoothing η_e(e/E)η_n(n/V)
nonzero at a PHYSICAL e,n in the complete odd e/n Cauchy
rectangle forces BOTH correct smooth-support windows:

 E L^-88/2 < e < 2E,  V/2 < n < 3V.

These constraints are deduced from the constructed smooth bumps;
unlike the old sparse selected-Q source E-window and original n
interval [V,2V] they remain VALID after legal pre-Gram
positive-square enlargement. -/
theorem parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
    (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (e n : ℕ)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0) :
    E*L^(-88:ℝ)/2 < (e:ℝ) ∧ (e:ℝ)<2*E ∧
    V/2 < (n:ℝ) ∧ (n:ℝ)<3*V := by
  have heLeft := parity_original_historical_full_odd_smoothing_nonzero_e_lower434
    L E V hL hE e n hw
  have hReal :
      parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0 ∧
      (parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V)).re≠0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hw
    exact ⟨(left_ne_zero_of_mul hw),(right_ne_zero_of_mul hw)⟩
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hEsupp := parity_original_historical_dyadic_eta_e_support434
    (L^(-88:ℝ)) ha.1 ha.2 ((e:ℝ)/E) hReal.1
  have hNsupp := parity_original_historical_actual_eta_n_support434
    ((n:ℝ)/V) (by
      intro hzero
      exact hReal.2 (by rw [hzero]; rfl))
  have heRight := mul_lt_mul_of_pos_right hEsupp.2 hE
  have hnLeft := mul_lt_mul_of_pos_right hNsupp.1 hV
  have hnRight := mul_lt_mul_of_pos_right hNsupp.2 hV
  refine ⟨heLeft,?_,?_,?_⟩
  · calc
      (e:ℝ) = ((e:ℝ)/E)*E := (div_mul_cancel₀ _ hE.ne').symm
      _ < 2*E := heRight
  · calc
      V/2 = ((1/2:ℝ)*V) := by ring
      _ < ((n:ℝ)/V)*V := hnLeft
      _ = (n:ℝ) := div_mul_cancel₀ _ hV.ne'
  · calc
      (n:ℝ) = ((n:ℝ)/V)*V := (div_mul_cancel₀ _ hV.ne').symm
      _ < 3*V := hnRight
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddSmoothedZScale -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- TRUE physical Parity(4.13) z-scale after the LEGITIMATE full-odd
and full-n positive-Cauchy envelope enlargement, conditional ONLY on
nonzero ACTUAL source smooth weight eta_e,L(e/E) eta_n(n/V):

  (exp L/8) L^K0 < z < 8 exp L L^(K0+88).

The original sparse source e-window E L^-88≤e≤E and original
n dyad [V,2V] are NOT assumed. Instead the correct true bump
supports E L^-88/2<e<2E and V/2<n<3V are proved; original
full Q/P h=-2 physical e*z=m'*(mn-2), original u<=floor2expL,
U*V≥expL and m,m' dyads remain unchanged. This pays the exact
factor 8 due to smoothing (rather than falsely reusing the old
factor 4). All prime-power multiplicities and signed k remain intact. -/
theorem parity_original_historical_full_odd_smoothed_physical_z_scale434
    (L U V E K0 : ℝ) (e m mp n u z : ℕ)
    (hL : 8≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0)
    (hmLo : U≤(m:ℝ)) (hmpLo : U≤(mp:ℝ))
    (hmpHi : (mp:ℝ)<2*U)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434
      ⌊2*Real.exp L⌋₊ m n)
    (hEz : e*z=mp*u) :
    (Real.exp L/8)*L^K0 < (z:ℝ) ∧
    (z:ℝ) < 8*Real.exp L*L^(K0+88) := by
  have hLp : 0<L := by linarith
  have hKpos : 0<L^K0 := Real.rpow_pos_of_pos hLp _
  have hInvpos : 0<L^(-88:ℝ) := Real.rpow_pos_of_pos hLp _
  have hEpos : 0<E := by rw [hE];exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  obtain ⟨heLo,heHi,hnLo,hnHi⟩ :=
    parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
      L E V hL hEpos hV e n hw
  have hePos : 0<(e:ℝ) :=
    (by positivity : 0<E*L^(-88:ℝ)/2).trans heLo
  have hnPos : 0≤(n:ℝ) := Nat.cast_nonneg _
  have huNat := (Finset.mem_filter.mp hu).2.2.2
  have huReal : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast huNat
  have hX8 : (8:ℝ)≤Real.exp L := by
    have hx := Real.add_one_le_exp L
    linarith
  have hMN : (Real.exp L)/2 < (m:ℝ)*(n:ℝ) := by
    have h1 : U*(V/2)<U*(n:ℝ) := mul_lt_mul_of_pos_left hnLo hU
    have h2 : U*(n:ℝ)≤(m:ℝ)*(n:ℝ) :=
      mul_le_mul_of_nonneg_right hmLo hnPos
    have h3 : (Real.exp L)/2≤U*(V/2) := by nlinarith [hUV]
    linarith
  have huLow : Real.exp L/4 < (u:ℝ) := by
    linarith [hMN,huReal,hX8]
  have huHi : (u:ℝ)≤2*Real.exp L := by
    calc
      _ ≤ (⌊2*Real.exp L⌋₊:ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).2
      _ ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hEzReal : (e:ℝ)*(z:ℝ)=(mp:ℝ)*(u:ℝ) := by exact_mod_cast hEz
  have hPair : E*L^K0=U := by
    calc
      _ = U*(L^(-K0)*L^K0) := by rw [hE];ring
      _ = U := by rw [←Real.rpow_add hLp]; simp
  have hTriple : (E*L^(-88:ℝ))*L^(K0+88)=U := by
    calc
      _ = U*(L^(-K0)*L^(-88:ℝ)*L^(K0+88)) := by rw [hE];ring
      _ = U*(L^((-K0)+(-88:ℝ)+(K0+88))) := by
        rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
      _ = U := by
        have hh : (-K0)+(-88:ℝ)+(K0+88)=0 := by ring
        rw [hh,Real.rpow_zero,mul_one]
  have hProdLo : U*(Real.exp L/4) ≤ (mp:ℝ)*(u:ℝ) :=
    mul_le_mul hmpLo huLow.le (by positivity) (by positivity)
  have hLowerMul : ((Real.exp L/8)*L^K0)*(e:ℝ)<(e:ℝ)*(z:ℝ) := by
    calc
      _ < ((Real.exp L/8)*L^K0)*(2*E) :=
        mul_lt_mul_of_pos_left heHi (by positivity)
      _ = U*(Real.exp L/4) := by rw [show ((Real.exp L/8)*L^K0)*(2*E)=
          (Real.exp L/4)*(E*L^K0) by ring,hPair];ring
      _ ≤ (mp:ℝ)*(u:ℝ) := hProdLo
      _ = (e:ℝ)*(z:ℝ) := hEzReal.symm
  have hLower : (Real.exp L/8)*L^K0 < (z:ℝ) := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_comm] using hLowerMul) hePos.le
  have hProdHi : (mp:ℝ)*(u:ℝ) ≤ (2*U)*(2*Real.exp L) :=
    mul_le_mul hmpHi.le huHi (by positivity) (by positivity)
  have hUpperMul : (e:ℝ)*(z:ℝ) <
      (e:ℝ)*(8*Real.exp L*L^(K0+88)) := by
    calc
      _ = (mp:ℝ)*(u:ℝ) := hEzReal
      _ ≤ (2*U)*(2*Real.exp L) := hProdHi
      _ = (E*L^(-88:ℝ)/2)*(8*Real.exp L*L^(K0+88)) := by
        rw [show (E*L^(-88:ℝ)/2)*(8*Real.exp L*L^(K0+88))=
          4*Real.exp L*((E*L^(-88:ℝ))*L^(K0+88)) by ring,hTriple]
        ring
      _ < (e:ℝ)*(8*Real.exp L*L^(K0+88)) :=
        mul_lt_mul_of_pos_right heLo (by positivity)
  have hUpper : (z:ℝ)<8*Real.exp L*L^(K0+88) := by
    exact lt_of_mul_lt_mul_left hUpperMul hePos.le
  exact ⟨hLower,hUpper⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddSmoothedZDyadic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- On a genuine source original full-odd-e/n populated binary
k/Z physical event with NONZERO constructed smoothing weight,
the ACTUAL dyadic Z obeys the correct Fourier growth window

   (exp L/16) L^K0 < Z < 8 exp L L^(K0+88).

This is not the old selected-Q e,n E-window theorem: it derives
from physical e*z=m'*(m*n-2), original B509 two endpoints,
positive u<=floor(2 exp L), U V>=exp L, m,m'∈[U,2U) and
ACTUAL eta_e(e/E) eta_n(n/V) nonzero (giving the CORRECT enlarged
smooth intervals e∈(E L^-88/2,2E), n∈(V/2,3V)). True dyadic
Z is 2^floor(log2 z) and Z≤z<2Z, not a fabricated interval.
In particular, the loss 8 vs the old sparse source constant 4
is paid explicitly rather than using a false E-window assumption. -/
theorem parity_original_historical_full_odd_smoothed_actual_Z_window434
    (d : ℕ) (L U V E K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    (Real.exp L/16)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 8*Real.exp L*L^(K0+88) := by
  let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMp := Finset.mem_filter.mp hProd.1
  have hMpK : q.1∈K := (Finset.mem_erase.mp hMp.1).2
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMp.1).1.symm
  have hValid := hMem.2.1
  have hzPos : 0<z := hMem.2.2.1
  have hzScale : parityOriginalHistoricalActualZDyadicScale434 z=Z := hMem.2.2.2
  have hDy := parity_original_historical_actual_z_in_own_dyad434 z hzPos
  rw [hzScale] at hDy
  have hmD := hDyad m hm
  have hmpD := hDyad q.1 hMpK
  obtain ⟨u,up,hu,hup,hEz,hEzp⟩ :=
    parity_original_historical_supported_z_exact_two_products434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m q.1 q.2 he hNe hValid
  change e*z=q.1*u at hEz
  have hZ := parity_original_historical_full_odd_smoothed_physical_z_scale434
    L U V E K0 e m q.1 q.2 u z hL hU hV hUV hE hw
    hmD.1 hmpD.1 hmpD.2 hu hEz
  have hzReal : (z:ℝ) < 2*(Z:ℝ) := by exact_mod_cast hDy.2.2
  have hZlo : (Real.exp L/16)*L^K0 < (Z:ℝ) := by
    have hLp : 0<L^K0 := Real.rpow_pos_of_pos (by linarith : 0<L) _
    nlinarith [hZ.1,hzReal,hLp]
  have hZR : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hDy.2.1
  exact ⟨hZlo,hZR.trans_lt hZ.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddSmoothedZPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The extra finite factor 16 caused by the genuine wider smooth
η_e and η_n support is absorbed by the OLD Parity(4.17) fixed
polynomial exponent K0+90 whenever L≥8 and K0≥0. This is an
actual inequality, not a false reuse of the sparse source e-window. -/
theorem parity_original_historical_full_odd_smooth_Z_polylog_numeric434
    (L K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0) :
    16*L^(-(K0+90)) ≤ L^K0 ∧
    8*L^(K0+88) ≤ L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hLsq : (16:ℝ)≤L^2 := by nlinarith [hL]
  have hp2 : 0<L^(K0-2) := Real.rpow_pos_of_pos hLp _
  have hsmall : L^(-(K0+90)) ≤ L^(K0-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hpow : L^(K0-2)*L^2=L^K0 := by
    rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
    congr 1
    push_cast
    ring
  have hsmallA : 16*L^(-(K0+90)) ≤ 16*L^(K0-2) :=
    mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hsmallB : 16*L^(K0-2)≤L^2*L^(K0-2) :=
    mul_le_mul_of_nonneg_right hLsq hp2.le
  have hUpper : 8*L^(K0+88)≤L^(K0+90) := by
    have hP : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
    have h8 : (8:ℝ)≤L^2 := by linarith
    have hh : 8*L^(K0+88)≤L^2*L^(K0+88) :=
      mul_le_mul_of_nonneg_right h8 hP.le
    calc
      _ ≤ L^2*L^(K0+88) := hh
      _ = L^(K0+90) := by
        rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
        congr 1
        ring
  constructor
  · calc
      _ ≤ 16*L^(K0-2) := hsmallA
      _ ≤ L^2*L^(K0-2) := hsmallB
      _ = L^K0 := by rw [mul_comm]; exact hpow
  · exact hUpper

/-- The source-correct ACTUAL full odd-e,n smoothed dyadic Z
window is LEGAL in the SAME Parity(4.17) polynomial height range
as the historical selected-Q proof, despite its wider cutoffs:

 exp L L^(-(K0+90)) ≤ Z ≤ exp L L^(K0+90).

No old E-window/n dyad premise is smuggled in: only the genuinely
proved smoother range and a sufficiently large L with K0≥0. -/
theorem parity_original_historical_full_odd_smooth_Z_Parity417_window434
    (L Z K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (hLo : (Real.exp L/16)*L^K0 < Z)
    (hHi : Z < 8*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90))≤Z ∧
      Z≤Real.exp L*L^(K0+90) := by
  obtain ⟨hNumLo,hNumHi⟩ :=
    parity_original_historical_full_odd_smooth_Z_polylog_numeric434 L K0 hL hK0
  have hx : 0≤Real.exp L/16 := by positivity
  have hZlo : Real.exp L*L^(-(K0+90)) ≤ (Real.exp L/16)*L^K0 := by
    have hh := mul_le_mul_of_nonneg_left hNumLo hx
    calc
      _ = (Real.exp L/16)*(16*L^(-(K0+90))) := by ring
      _ ≤ (Real.exp L/16)*L^K0 := hh
  have hZhi : 8*Real.exp L*L^(K0+88) ≤ Real.exp L*L^(K0+90) := by
    have hh := mul_le_mul_of_nonneg_left hNumHi (Real.exp_pos L).le
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  exact ⟨(hZlo.trans_lt hLo).le,(hHi.trans_le hZhi).le⟩

/-- For an ACTUAL populated physical full odd-e,n source k/Z
cell, whenever its original smoothed η_eη_n weight is nonzero,
Parity(4.17)'s true height hypotheses hold with the same fixed
exponent CZ=K0+90 as in the original manuscript source:
 exp L L^(-CZ) ≤ (Z:ℝ) ≤ exp L L^CZ.
This is proved with the corrected factor-eight smoothing support
and exact binary dyadic Z, never by reusing the old sparse E-window. -/
theorem parity_original_historical_full_odd_actual_Z_Parity417_legal434
    (d : ℕ) (L U V E K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
    (Z:ℝ)≤Real.exp L*L^(K0+90) := by
  obtain ⟨hZlo,hZhi⟩ :=
    parity_original_historical_full_odd_smoothed_actual_Z_window434
      d L U V E K0 hL band slot δ K J e m k Z he hU hV hUV
      hE hm hDyad q hq hw
  exact parity_original_historical_full_odd_smooth_Z_Parity417_window434
    L (Z:ℝ) K0 hL hK0 hZlo hZhi
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddEtaN3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The genuine source eta_e,L-positive enlargement costs a factor
2 in the LOWER e/E support and hence a factor 2 in the upper
Z/(UV) Fourier-pullback coefficient. For L≥8, this increased
physical Z≤8exp(L)L^(K0+88) is still bounded by
Z≤4exp(L)L^((K0+1)+88) and so existing exact native Parity(4.14)
three-dimensional Faà di Bruno machinery applies to η_n with
ONE extra fixed power of L. The original E=U L^-K0 is NOT
changed, nor is the nonlinear h=-2 correction 2/(UV) removed. -/
theorem parity_original_historical_full_odd_Z_upper_to_eta_n_extended434
    (L Z K0 : ℝ) (hL : 8≤L)
    (hZ : Z≤8*Real.exp L*L^(K0+88)) :
    Z≤4*Real.exp L*L^((K0+1)+88) := by
  have hLp : 0<L := by linarith
  have hL8 : (2:ℝ)≤L := by linarith
  have hPow : 0≤L^(K0+88) := Real.rpow_nonneg hLp.le _
  have hh : 8*Real.exp L*L^(K0+88) ≤
      4*Real.exp L*L^(K0+88)*L := by
    have hmul := mul_le_mul_of_nonneg_left hL8
      (mul_nonneg (by positivity : 0≤4*Real.exp L) hPow)
    nlinarith [hmul]
  calc
    _ ≤ 8*Real.exp L*L^(K0+88) := hZ
    _ ≤ 4*Real.exp L*L^(K0+88)*L := hh
    _ = 4*Real.exp L*L^((K0+1)+88) := by
      have heq : L^((K0+1)+88)=L^(K0+88)*L := by
        rw [show (K0+1)+88=(K0+88)+1 by ring]
        rw [Real.rpow_add hLp,Real.rpow_one]
      rw [heq]
      ring

/-- The actual original h=-2 η_n(g_n) logarithmic Fourier
three-dimensional derivative on the COMPLETE full-odd e/n source
square, with the correct wider physical Z upper range,
is bounded by J!K^n_J L^((K0+90)(J+1)). The exponent increases
only by ONE relative to the original sparse selected-Q e window.
All constants and source cutoff shapes are independent of k,Z,L. -/
theorem parity_original_historical_full_odd_eta_n_3d_composed_polylog434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A ≤ L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualEtaN434 ∘
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaNLogArg434 U V Z k
            (EuclideanSpace.equiv (Fin 3) ℝ t))) t‖ ≤
    (J.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 J *
      L^((K0+90)*((J:ℝ)+1)) := by
  have hUpper := parity_original_historical_full_odd_Z_upper_to_eta_n_extended434
    L Z K0 hL hZupper
  have hOld := parity_original_historical_actual_eta_n_3d_composed_polylog434
    L U V Z (K0+1) A k hL (by linarith) hU hV hUV hk
    hZ hUpper hA J hLarge t h0 h1 h2
  simpa only [show (K0+1)+89=K0+90 by ring] using hOld
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFiveFactorPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- ALL FIVE actual historical Parity(4.14) three-dimensional SOURCE
cutoff factors admit a common order-r derivative bound on the full
odd-e,n SMOOTHED physical height range Z≤8expL L^(K0+88), not
just the old selected-Q source E-window. The correct +1 exponent
from extending eta_e lower support is paid EXACTLY:
 ||D^r factor_i|| ≤ M_J L^((K0+90)(J+1)) (r≤J).
The fixed M_J consists of genuine eta_e/eta_n/reference buffer
Schwartz seminorms independent of L,k,Z,χ and Fourier accuracy.
The original h=-2 correction and E=U L^-K0 are unchanged. -/
theorem parity_original_historical_full_odd_five_factors_all_order_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ∀ (i : Fin 5) (r : ℕ), r≤J →
      ‖iteratedFDeriv ℝ r
        (parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf i) t‖ ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J *
        L^((K0+90)*((J:ℝ)+1)) := by
  let M := parityOriginalHistoricalFiveFactorFixedBudget434
    A buf hBufSmooth hBufSupport J
  let R := L^((K0+90)*((J:ℝ)+1))
  have hM : 1≤M := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hR : 1≤R := by
    have hh := parity_original_3d_source_log_power_ge_one434 L (K0+1)
      hL (by linarith : 0≤K0+1) J
    simpa only [show (K0+1)+89=K0+90 by ring] using hh
  have hMR : 0≤M := by linarith
  have hRR : 0≤R := by linarith
  have hB (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
        A buf hBufSmooth hBufSupport r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.2
  have hEE (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).1
  have hNN (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.1
  have hPower (r : ℕ) (hr : r≤J) :
      L^((K0+90)*((r:ℝ)+1)) ≤ R := by
    have hh := parity_original_3d_source_log_power_mono434 L (K0+1) hL
      (by linarith : 0≤K0+1) J r hr
    simpa only [show (K0+1)+89=K0+90 by ring] using hh
  have hBase (i : Fin 3) (r : ℕ) (hr : r≤J) :
      ‖iteratedFDeriv ℝ r
        (fun x : EuclideanSpace ℝ (Fin 3) => buf (x i)) t‖ ≤ M*R := by
    have hh := parity_original_historical_fixed_log_buffer_3d_fderiv_le434
      A buf hBufSmooth hBufSupport i r t
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
          A buf hBufSmooth hBufSupport r := hh
      _ ≤ M := hB r hr
      _ = M*1 := by ring
      _ ≤ M*R := mul_le_mul_of_nonneg_left hR hMR
  intro i r hr
  fin_cases i
  · exact hBase 0 r hr
  · exact hBase 1 r hr
  · exact hBase 2 r hr
  · have hThreshold := parity_original_eta_e_threshold_mono434
      A hA.le J r hr L hLargeE
    have hh := parity_original_historical_actual_eta_e_3d_composed_polylog434
      L U E K0 A k hL hK0 hU hE hk hA r hThreshold t h0 h1
    change ‖iteratedFDeriv ℝ r
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaELogArg434 U E k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r *
          L^((K0+89)*((r:ℝ)+1)) := hh
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r *
          L^((K0+90)*((r:ℝ)+1)) := by
            have hExp : (K0+89)*((r:ℝ)+1)≤(K0+90)*((r:ℝ)+1) := by
              have hRp : (0:ℝ)≤(r:ℝ)+1 := by positivity
              nlinarith
            have hPow' := Real.rpow_le_rpow_of_exponent_le
              (by linarith : (1:ℝ)≤L) hExp
            have hCoef : 0≤(r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r := by
              have hh := (parity_original_historical_five_factor_fixed_envelopes_nonneg434
                A buf hBufSmooth hBufSupport r).1
              exact mul_nonneg (Nat.cast_nonneg _) hh
            exact mul_le_mul_of_nonneg_left hPow' hCoef
      _ ≤ M*L^((K0+90)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hEE r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
  · have hThreshold := parity_original_eta_n_threshold_mono434
      A hA.le J r hr L hLargeN
    have hh := parity_original_historical_full_odd_eta_n_3d_composed_polylog434
      L U V Z K0 A k hL hK0 hU hV hUV hk hZ hZupper
      hA r hThreshold t h0 h1 h2
    change ‖iteratedFDeriv ℝ r
      (parityOriginalHistoricalActualEtaN434 ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaNLogArg434 U V Z k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r *
          L^((K0+90)*((r:ℝ)+1)) := hh
      _ ≤ M*L^((K0+90)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hNN r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOdd3DSourceDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Complete original h=-2 three-dimensional source Fourier kernel
full five-factor Fréchet derivative bound on the ACTUAL smoothed
full-odd positive-Cauchy carrier Z≤8expL L^(K0+88), at EVERY fixed
order J in the physical log box [-log A,log A]^3:
 ||D^J F_(L,k,Z)(t)|| ≤ K_J L^(5(K0+90)(J+1)).
K_J is the existing genuine source fixed buffer/eta-e/eta-n
Schwartz reference, independent of L,k,Z and desired precision.
The broader source e-smoothing costs exactly one additional L power
relative to the old original sparse selected-Q E-window theorem. -/
theorem parity_original_historical_full_odd_full_3d_source_derivative_on_box434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
      parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth
        hBufSupport J * L^((5*(K0+90))*((J:ℝ)+1)) := by
  let F := parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf
  let M := parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J
  let R := L^((K0+90)*((J:ℝ)+1))
  have hMR : 0≤M*R := by
    have hm := parity_original_historical_five_factor_fixed_budget_ge_one434 A buf hBufSmooth hBufSupport J
    have hr0 := parity_original_3d_source_log_power_ge_one434 L (K0+1)
      hL (by linarith : 0≤K0+1) J
    have hr : 1≤R := by
      simpa only [R,show (K0+1)+89=K0+90 by ring] using hr0
    exact mul_nonneg (by linarith) (by linarith)
  have hFive := parity_original_3d_five_factor_derivative_le434
    F (parity_original_historical_actual_five_factors_smooth434
      L U E V Z hL k buf hBufSmooth)
    J t (M*R) hMR
    (parity_original_historical_full_odd_five_factors_all_order_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport J hLargeE hLargeN t h0 h1 h2)
  have hEq := parity_original_historical_actual_five_product_eq_schwartz434
    L U E V Z hL k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => ∏i : Fin 5,F i x) =
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) := by
    funext x
    exact hEq x
  rw [hfun] at hFive
  have hPower : R^5=L^((5*(K0+90))*((J:ℝ)+1)) := by
    dsimp [R]
    rw [←Real.rpow_natCast (L^((K0+90)*((J:ℝ)+1))) 5]
    rw [←Real.rpow_mul (by linarith : 0≤L)]
    congr 1
    ring
  calc
    _ ≤ parityOriginal3DFiveFactorDerivativeCombinatorial434 J * (M*R)^5 := hFive
    _ = parityOriginalHistoricalFull3DFixedDerivativeK434 A buf
          hBufSmooth hBufSupport J * L^((5*(K0+90))*((J:ℝ)+1)) := by
        unfold parityOriginalHistoricalFull3DFixedDerivativeK434
        rw [mul_pow,hPower]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOdd3DSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19500000

/-- Genuine ORIGINAL full odd-e/n Parity(4.14) three-dimensional
Schwartz seminorm polynomial estimate, valid for the CORRECT
smoothed Fourier dyadic Z range Z≤8exp L L^(K0+88).
For each polynomial weight p and derivative order J:
 normSchwartz_(p,J)(F_(L,k,Z)) ≤ R^p K_J L^[5(K0+90)(J+1)]
with R,K_J fixed before L,k,Z,χ and Fourier precision. Its proof
uses the SAME original fixed log cube support and native vanishing
outside the support; the original h=-2 eta_n shift is retained.
No artificial source Z lower range or old sparse selected-Q e/n
premises are assumed. -/
theorem parity_original_historical_full_odd_full_3d_source_seminorm_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J p : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    (SchwartzMap.seminorm ℂ p J)
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      R^p * parityOriginalHistoricalFull3DFixedDerivativeK434
        A buf hBufSmooth hBufSupport J *
        L^((5*(K0+90))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let C := parityOriginalHistoricalFull3DFixedDerivativeK434
    A buf hBufSmooth hBufSupport J
  let P := L^((5*(K0+90))*((J:ℝ)+1))
  have hM1 := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hCoeff : 0≤C := mul_nonneg
    (parity_original_3d_five_factor_combinatorial_nonneg434 J)
    (pow_nonneg (by linarith : 0≤parityOriginalHistoricalFiveFactorFixedBudget434
      A buf hBufSmooth hBufSupport J) 5)
  have hP : 0≤P := Real.rpow_nonneg (by linarith : 0≤L) _
  have hRpow : 0≤R^p := pow_nonneg (by linarith) _
  have hM : 0≤R^p*C*P := by positivity
  have hTSupport := parity_original_historical_actual_source_schwartz_tsupport_cube434
    L U E V Z A hL k buf hBufSmooth hBufSupport
  apply SchwartzMap.seminorm_le_bound ℂ p J f hM
  intro t
  by_cases ht : t∈parityOriginalHistoricalEuclideanFixedLogCube434 A
  · have hc := parity_original_historical_fixed_3d_cube_coordinates434 A t ht
    have hD := parity_original_historical_full_odd_full_3d_source_derivative_on_box434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper
      hA buf hBufSmooth hBufSupport J hLargeE hLargeN t
      (hc 0) (hc 1) (hc 2)
    have hNorm : ‖t‖^p≤R^p :=
      pow_le_pow_left₀ (norm_nonneg t) (hCubeR t ht) p
    calc
      ‖t‖^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
        R^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ :=
          mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
      _ ≤ R^p*(C*P) := mul_le_mul_of_nonneg_left hD hRpow
      _ = R^p*C*P := by ring
  · have hnot : t∉tsupport (f : EuclideanSpace ℝ (Fin 3) → ℂ) :=
      fun h => ht (hTSupport h)
    have hNo : (iteratedFDeriv ℝ J
        (f : EuclideanSpace ℝ (Fin 3) → ℂ)) t = 0 := by
      have hs : t∉Function.support (iteratedFDeriv ℝ J
          (f : EuclideanSpace ℝ (Fin 3) → ℂ)) :=
        fun h => hnot (support_iteratedFDeriv_subset J h)
      exact not_not.mp hs
    rw [hNo,norm_zero,mul_zero]
    exact hM
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOdd3DFiniteSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22500000

/-- The ACTUAL original Parity(4.14) full odd-e,n smoothed
three-dimensional finite PRE-FOURIER Schwartz seminorm budget
is controlled by a fixed-source K_J L^[5(K0+90)(J+1)] for every
order N≤J, uniformly in physical source k,Z when
Z≤8exp L L^(K0+88). The real source wide η_e/n smooth support
corrects the earlier sparse-source 4 to 8 height factor rather
than assuming the original E-window after positive Cauchy enlargement.
This is a source-proved finite derivative budget, with no invented
Fourier tail moment hypothesis or Parity(4.17) saving. -/
theorem parity_original_historical_full_odd_3d_finite_seminorm_budget_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J N : ℕ) (hNJ : N≤J)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceFiniteSeminormBudget434 N
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      parityOriginalHistoricalFull3DSourceSeminormFixedK434 A R buf
        hBufSmooth hBufSupport J *
        L^((5*(K0+90))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A)
      hBufSmooth hBufSupport
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let C : ℝ := parityOriginal3DSourceGeometricConstant434
  let K : ℕ → ℝ := fun j =>
    parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth hBufSupport j
  let M : ℝ := ∑j∈Finset.range (J+1),K j
  let Rpow : ℝ := L^((5*(K0+90))*((J:ℝ)+1))
  let D : ℝ := (2:ℝ)^J*C*(1+R^P)*M
  have hK (j : ℕ) : 0≤K j := by
    dsimp [K,parityOriginalHistoricalFull3DFixedDerivativeK434]
    apply mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
    apply pow_nonneg
    have hge := parity_original_historical_five_factor_fixed_budget_ge_one434
      A buf hBufSmooth hBufSupport j
    linarith
  have hM : 0≤M := Finset.sum_nonneg (fun i hi=>hK i)
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hRpos : 0≤R^P := pow_nonneg (by linarith) _
  have hRpow : 0≤Rpow := Real.rpow_nonneg (by linarith) _
  have hD : 0≤D := by dsimp [D]; positivity
  have h0 (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ 0 j) f ≤ K j * Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_full_odd_full_3d_source_seminorm_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport j 0 hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+90))*((j:ℝ)+1) ≤ (5*(K0+90))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    have hm : 0≤K j := hK j
    calc
      _ ≤ R^0*K j*L^((5*(K0+90))*((j:ℝ)+1)) := hs
      _ = K j*L^((5*(K0+90))*((j:ℝ)+1)) := by ring
      _ ≤ K j*Rpow := mul_le_mul_of_nonneg_left hp hm
  have hPbound (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ P j) f ≤ R^P*K j*Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_full_odd_full_3d_source_seminorm_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport j P hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+90))*((j:ℝ)+1) ≤ (5*(K0+90))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    calc
      _ ≤ R^P*K j*L^((5*(K0+90))*((j:ℝ)+1)) := hs
      _ ≤ R^P*K j*Rpow := by
        have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hRpos (hK j))
        exact hh
  have hSum :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      (1+R^P)*M*Rpow := by
    have hs :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      ∑j∈Finset.range (N+1), (1+R^P)*K j*Rpow := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j≤J := Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hNJ
      have hh := add_le_add (h0 j hjJ) (hPbound j hjJ)
      convert hh using 1 <;> ring
    have hSubset : (Finset.range (N+1) : Finset ℕ)⊆Finset.range (J+1) :=
      Finset.range_mono (Nat.succ_le_succ hNJ)
    have hSub : (∑j∈Finset.range (N+1),K j)≤M :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun j hj hnot=>hK j)
    calc
      _ ≤ ∑j∈Finset.range (N+1),(1+R^P)*K j*Rpow := hs
      _ = (1+R^P)*(∑j∈Finset.range (N+1),K j)*Rpow := by
        rw [Finset.mul_sum,Finset.sum_mul]
      _ ≤ (1+R^P)*M*Rpow := by
        have hcoef : 0≤1+R^P := by linarith
        have hm := mul_le_mul_of_nonneg_left hSub hcoef
        exact mul_le_mul_of_nonneg_right hm hRpow
  have hPow : (2:ℝ)^N≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hNJ
  have hFactor : 0≤C*((1+R^P)*M*Rpow) := by positivity
  change (2:ℝ)^N * C *
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f+
         (SchwartzMap.seminorm ℂ P j) f)) ≤ D*Rpow
  calc
    _ ≤ (2:ℝ)^N*C*((1+R^P)*M*Rpow) :=
      mul_le_mul_of_nonneg_left hSum
        (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _) hC)
    _ ≤ (2:ℝ)^J*C*((1+R^P)*M*Rpow) := by
      have h2 : (2:ℝ)^N*C ≤ (2:ℝ)^J*C :=
        mul_le_mul_of_nonneg_right hPow hC
      have hQ : 0≤(1+R^P)*M*Rpow := by positivity
      exact mul_le_mul_of_nonneg_right h2 hQ
    _ = D*Rpow := by dsimp [D]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOdd3DBudgetPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The complete original h=-2 PRE-FOURIER Euclidean 3D source
Schwartz derivative moment B_H for the ACTUAL FULL odd-e,n
positive-Cauchy enlarged source has a fixed polynomial bound
 B_H(F_(L,k,Z)) ≤ C_H L^[5(K0+90)(H+P+1)]
for all k≠0 and the actual height support Z≤8 expL L^(K0+88).
All source buffer constants C_H are fixed independently of L,k,Z,
ψ, Fourier frequency, original Q/P/B509 and b629 fine alpha.
This corrects the former sparse-source E-window bound factor 4
that CANNOT be reused after positive-square carrier enlargement.
No hypothetical Fourier decay or Eq(4.17) saving is assumed. -/
theorem parity_original_historical_full_odd_source_BH_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+90))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hBufSmooth hBufSupport J
  let C := parityOriginal3DSourceGeometricConstant434
  let Q := L^((5*(K0+90))*((J:ℝ)+1))
  have hm0 := parity_original_historical_full_odd_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_full_odd_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J J le_rfl
    hLargeE hLargeN R hR hCubeR
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  change C*(parityOriginal3DSourceFiniteSeminormBudget434 0 f+
      parityOriginal3DSourceFiniteSeminormBudget434 J f) ≤ (2*C*B)*Q
  calc
    _ ≤ C*((B*Q)+(B*Q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hm0 hmJ) hC
    _ = (2*C*B)*Q := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOdd3DFourierMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- ORIGINAL h=-2 Parity(4.14) full odd-e/n smoothed source Fourier
moments and high-frequency tails are UNIFORMLY polynomial in L for
the CORRECT widened height Z≤8expL L^(K0+88), with exponent
5(K0+90)(H+P+1) for any fixed H, P the 3D Lebesgue integrablePower.
The proof uses the same genuine five source factors and fixed log
buffer as the actual full-odd positive-Cauchy Fourier equality,
including true physical 2/(UV) shift correction, and derives Fourier
decay from its full Schwartz seminorms. No old sparse selected-Q
E-window is assumed, no moment or Parity(4.17) saving is postulated. -/
theorem parity_original_historical_full_odd_3d_fourier_moment_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    (∫ζ : EuclideanSpace ℝ (Fin 3),
      ‖ζ‖^H * ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+90))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hBufSmooth hBufSupport J
  let C := parityOriginal3DSourceGeometricConstant434
  let Q := L^((5*(K0+90))*((J:ℝ)+1))
  have hm0 := parity_original_historical_full_odd_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_full_odd_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J J le_rfl
    hLargeE hLargeN R hR hCubeR
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hB : 0≤B := by
    dsimp [B,parityOriginalHistoricalFull3DSourceSeminormFixedK434]
    have hg := parity_original_3d_source_geometric_constant_nonneg434
    have hr : 0≤R^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower) := by positivity
    have hkSum : 0≤∑j∈Finset.range (J+1),
        parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth hBufSupport j := by
      apply Finset.sum_nonneg
      intro j hj
      unfold parityOriginalHistoricalFull3DFixedDerivativeK434
      have hGe := parity_original_historical_five_factor_fixed_budget_ge_one434
        A buf hBufSmooth hBufSupport j
      exact mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
        (pow_nonneg (by linarith : 0≤parityOriginalHistoricalFiveFactorFixedBudget434
           A buf hBufSmooth hBufSupport j) 5)
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg
      (by norm_num : (0:ℝ)≤2) _) hg)
      (by linarith : 0≤1+R^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower))) hkSum
  have hQ : 0≤Q := Real.rpow_nonneg (by linarith : 0≤L) _
  have hMom := parity_original_real_3d_fourier_moment_le_original_source_finite434 H f
  change (∫ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖^H *
      ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤ (2*C*B)*Q
  calc
    _ ≤ C*(parityOriginal3DSourceFiniteSeminormBudget434 0 f+
      parityOriginal3DSourceFiniteSeminormBudget434 J f) := hMom
    _ ≤ C*((B*Q)+(B*Q)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hm0 hmJ) hC
    _ = (2*C*B)*Q := by ring

/-- Exact physical original Parity (4.15) high-frequency Fourier L1
TAIL bound of arbitrary polynomial order, with the formerly UNKNOWN
source B_H uniformly paid in a fixed polynomial in L. For all T>0:

 tail(‖ζ‖>T) ≤ C_H L^[5(K0+90)(H+P+1)]/T^H.

All original source eta_e, eta_n, 3D log pullbacks, k≠0 and
h=-2 correction, true SOURCE dyadic geometry and fixed buffer
are retained. No 4.17 core cancellation or full TypeII assumed. -/
theorem parity_original_historical_full_odd_3d_fourier_tail_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤8*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _)ᶜ,
      ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+90))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) / T^H := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  have ht := parity_original_historical_3d_fourier_tail_le_moment434
    H U E V Z k buf (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
    parityOriginalHistoricalActualEtaN434 (-Real.log A) (Real.log A)
    hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport T hT
  have hm := parity_original_historical_full_odd_3d_fourier_moment_uniform_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport H hLargeE hLargeN R hR hCubeR
  exact ht.trans (div_le_div_of_nonneg_right hm (pow_nonneg hT.le H))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddKZMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The POSITIVE source e-fixed diagonal is one genuine summand of
the FULL ODD-E original extended Cauchy diagonal whenever that e
belongs to its actual finite envelope. This is a legitimate
nonnegative-summand comparison, not a complex offdiagonal subset
inequality, and no sparse selected-Q e membership remains. -/
theorem parity_original_historical_full_odd_e_fixed_diagonal_le_full434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e : ℕ) (he : e∈Eenv) :
    (∑n∈Nenv,∑r∈K,
      ‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n r‖^2) ≤
    parityOriginalHistoricalExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  let F : ℕ → ℝ := fun e0 =>
    ∑n∈Nenv,∑r∈K,
      ‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e0 n r‖^2
  have hF : ∀e0∈Eenv, 0≤F e0 := by
    intro e0 he0
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro r hr
    exact sq_nonneg _
  change F e≤∑e0∈Eenv,F e0
  exact Finset.single_le_sum hF he

/-- For ANY original h=-2 populated physical canonical k/Z cell
at e∈FULL ODD-E envelope, its exact source signed/chi cofactor ℓ1
mass is bounded by the FULL enlarged positive source diagonal.
This uses the actual Q/P/B509 two-ended source, χ norm≤1 and
unique physical m' per e,m,k, no alpha proxy and no #characters.
It works even when the eta_e,n smoothing weight is zero: the
coefficient mass itself is unweighted and always nonnegative. -/
theorem parity_original_historical_full_odd_k_z_mass_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (heFull : e∈Eenv) (hm : m∈K)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K Nenv k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    parityOriginalHistoricalExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  exact (parity_original_historical_actual_k_z_physical_l1_mass_le_e_diagonal434
    d L band slot δ ξ rho α signed Y e m K Nenv k Z he hm χ).trans
    (parity_original_historical_full_odd_e_fixed_diagonal_le_full434
      d L band slot δ ξ rho K Eenv Nenv α signed Y e heFull)

/-- The entire full-odd-e original signed χ cofactor k/Z ℓ1
mass is SOURCE-unconditionally bounded by one FIXED power of L
times x=e^L, no matter which odd e from the enlarged positive
Cauchy support and which original physical k,Z. This uses the
true original eighth shifted divisor moment, not a stronger
unproved fourth divisor moment or a synthetic SourceComparisonData. -/
theorem parity_eventually_original_historical_full_odd_k_z_mass_X434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈Eenv → m∈K →
      ∀χ : DirichletCharacter ℂ (2*k.natAbs),
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K Nenv k Z)
        (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
          ⌊2*Real.exp L⌋₊ e m k χ) ≤
      Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_extended_diagonal_polylog434]
    with L hDiag
  refine ⟨hDiag.1,?_⟩
  intro band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hAlpha
    e m k Z he heFull hm χ
  exact (parity_original_historical_full_odd_k_z_mass_le_diagonal434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K Eenv Nenv α signed ⌊2*Real.exp L⌋₊ e m k Z
    he heFull hm χ).trans
    (hDiag.2 band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hAlpha)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddKZMassZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- TRUE ORIGINAL Parity(4.15) full-odd-e/n χ k/Z coefficient
ℓ1 mass polynomial on a PHYSICAL source cell with at least one
NONZERO actual η_e,L(e/E)η_n(n/V) weight. This is the correct
post-positive-Cauchy full-odd source replacement of the old
selected-Q e-window mass lemma:

  mass_(e,m,k,Z,χ) ≤ Acoef² Z L^(2*C_W1+256+K0+90).

The mass itself is unweighted; the actual nonzero-weight source
event is used ONLY to derive the correct height window
exp L L^(-(K0+90))≤Z≤exp L L^(K0+90). The source full-odd
positive diagonal and original shifted τ eighth moment establish
the coefficient majorant, with no guessed β/Ppart Fourier saving.
Cells whose source smoothing weight vanishes identically can
instead be kept as zero exact source contribution and should NOT
be included in the truncated Fourier family without a separate
tail argument. -/
theorem parity_eventually_original_full_odd_k_z_l1_mass_Z434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀χ : DirichletCharacter ℂ (2*k.natAbs),
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k Z)
        (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
          ⌊2*Real.exp L⌋₊ e m k χ) ≤
      Acoef^2*(Z:ℝ)*
        L^(2*parityOriginalW1PolylogExponent434+256+K0+90) := by
  filter_upwards [parity_eventually_original_historical_full_odd_k_z_mass_X434,
    eventually_ge_atTop (8:ℝ)] with L hMass hL8
  refine ⟨hMass.1,hL8,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hA hα
    hU hV hUV hScale hDyad e m k Z he heMem hm q hq hw χ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Eenv := parityOriginalHistoricalFullOddEEnvelope434 E
  have hLpos : 0<L := by linarith
  have hZ := parity_original_historical_full_odd_actual_Z_Parity417_legal434
    (sourceOriginalLiteralDepth 20 L) L U V E K0 hL8 hK0
    band slot δ K J e m k Z he hU hV hUV hScale hm hDyad q hq hw
  have hMassBound := hMass.2 band slot δ ξ rho K Eenv J α signed Acoef
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

/-! ## OriginalHistoricalFullOddKZ416TailUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- COMPLETE original Parity(4.15)--(4.16) Fourier low-frequency
truncation error on an ACTUAL full-odd-e,n source k/Z PHYSICAL cell
with at least one genuinely nonzero constructed η_e(e/E)η_n(n/V):

 |Err_(e,m,k,Z,χ)| ≤ Acoef² Z L^M × C_H L^X/T^H,
 M=2*C_W1+256+K0+90, X=5(K0+90)(H+P+1),

where C_H is one truly fixed source logarithmic buffer / Euclidean
R³ Schwartz derivative constant independent of L,k,Z,χ, α or
Fourier cutoff T; P is the fixed Euclidean Lebesgue integrablePower.
All named quantities on RHS have been PROVED from the actual source
and are NOT free analytic assumptions: the e/n smooth widening,
Z≤8expL L^(K0+88), native original signed coefficient ℓ1 via
full positive eighth τ divisor moment, full 3D Faà di Bruno and
source H0/B509, exact 2π Fourier integral have been separately
checked. The cells whose η_eη_n vanishes on all genuine source
events are not included in this truncation estimate; their exact
weighted source sum vanishes, but truncated high-frequency tails
cannot be discarded without a separate argument.

This is still per original physical k/Z, not an estimate of the
full signed B633 two-core correlation nor Parity Type II (4.2). -/
theorem parity_eventually_original_full_odd_k_z_416_tail_uniform434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs))
        (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      parityOriginalHistoricalActualKZ416FourierError434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
        rho α signed ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      Acoef^2*(Z:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256+K0+90) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := by
  filter_upwards [parity_eventually_original_full_odd_k_z_l1_mass_Z434 K0 hK0]
    with L hMass
  refine ⟨hMass.1,hMass.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad e m k Z he heMem hm q hq hw
    χ A R hA hR buf hSmooth hSupport hOne hCubeR H hLargeE hLargeN T hT
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let mass := parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let Q : ℝ := Acoef^2*(Z:ℝ)*
      L^(2*parityOriginalW1PolylogExponent434+256+K0+90)
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Power : ℝ := L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))
  have hLp : 0<L := by linarith [hMass.2.1]
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hmDyad := hDyad m hm
  have hZrange := parity_original_historical_full_odd_smoothed_actual_Z_window434
    d L U V E K0 hLw band slot δ K J e m k Z he hU hV hUV hScale
    hm hDyad q hq hw
  have hZlegal := parity_original_historical_full_odd_smooth_Z_Parity417_window434
    L (Z:ℝ) K0 hLw hK0 hZrange.1 hZrange.2
  have hZreal : (0:ℝ)<(Z:ℝ) :=
    (mul_pos (Real.exp_pos L)
      (Real.rpow_pos_of_pos hLp (-(K0+90)))).trans_le hZlegal.1
  have hZ : 0<Z := by exact_mod_cast hZreal
  have hk : k≠0 := parity_original_historical_nonempty_actual_k_z_nonzero434
    d L band slot δ Y e m K J k Z he ⟨q,hq⟩
  have hMassBound : mass≤Q := hMass.2.2 hLw band slot δ ξ rho U V E K
    α signed Acoef hAcoef hAlpha hU hV hUV hScale hDyad
    e m k Z he heMem hm q hq hw χ
  have hBH := parity_original_historical_full_odd_source_BH_uniform_polylog434
    L U E V (Z:ℝ) K0 A hLw hK0 k hk hU hV hUV hScale
    (by exact_mod_cast (Nat.zero_le Z)) hZrange.2.le
    hA buf hSmooth hSupport H hLargeE hLargeN R hR hCubeR
  have hTbound : parityOriginalHistoricalActualKZ416FourierError434
    d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
    buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
    mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) :=
    parity_original_historical_actual_k_z_416_error_le_mass434
      d L hLw band slot δ ξ rho α signed Y e m K J k Z χ he
      U E V hU hEpos hV hmDyad.1 hmDyad.2.le
      (by intro mp hmp;exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩)
      buf (-Real.log A) (Real.log A) hSmooth hSupport hOne hZ H T hT
  have hBpos : 0≤parityOriginal3DSourceMomentFiniteBudget434 H f :=
    parity_original_3d_actual_source_finite_B_nonneg434 H f
  have hDiv : parityOriginal3DSourceMomentFiniteBudget434 H f/T^H ≤
      C*Power/T^H :=
    div_le_div_of_nonneg_right hBH (pow_pos hT H).le
  have hM : 0≤Q := by
    dsimp [Q]
    positivity
  calc
    _ ≤ mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := hTbound
    _ ≤ Q*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) :=
      mul_le_mul_of_nonneg_right hMassBound (div_nonneg hBpos (pow_pos hT H).le)
    _ ≤ Q*(C*Power/T^H) := mul_le_mul_of_nonneg_left hDiv hM
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddNonzeroWeightCells -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The **ONLY** physically attained original h=-2 binary dyadic
k/Z cells which contain at least one nonzero source smoothing
weight eta_e(e/E)*eta_n(n/V) on its actual Q/P/B509 m'×n event.
Choosing these cells before frequency truncation avoids silently
throwing away a nonzero truncated Fourier integral on an EXACTLY
zero source cell; every cell excluded has its entire original
weighted signed physical character sum identically zero. -/
def parityOriginalHistoricalFullOddNonzeroWeightZCells434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset ℕ :=
  ((parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter
    (fun Z => ∃q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0)

/-- Every source-physically attained k/Z cell excluded by the
nonzero-weight selection has zero original eta_e,n weighted signed
character sum for ALL complex H0, alpha, χ and epsilon branches.
Proof is direct finite sum vanishing on the *exact original events*;
this is not a falsely inferred cancellation of a signed superset. -/
theorem parity_original_historical_full_odd_zero_weight_cell_source_zero434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hNo : ∀q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 = 0)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ = 0 := by
  unfold parityOriginalHistoricalActualKZPhysicalWeightedSource434
  apply Finset.sum_eq_zero
  intro q hq
  rw [hNo q hq]
  simp

/-- Any attained binary Z which is absent from the original actual
nonzero-smoothed-cell support contributes EXACTLY ZERO to the
original source complex character sum. In particular no extra
#Z factor is introduced or guessed from a larger Z interval. -/
theorem parity_original_historical_full_odd_nonselected_Z_source_zero434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hNot : Z∉parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ = 0 := by
  have hNo : ∀q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
       d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 = 0 := by
    intro q hq
    by_contra hne
    have hnon : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0 := hne
    apply hNot
    unfold parityOriginalHistoricalFullOddNonzeroWeightZCells434
    have hsrc := Finset.mem_filter.mp hq
    have hbase := Finset.mem_product.mp hsrc.1
    have hEvent : q∈parityOriginalHistoricalFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k :=
      Finset.mem_filter.mpr ⟨hsrc.1,hsrc.2.1⟩
    have hZscale := hsrc.2.2.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨q,hEvent,hZscale⟩,⟨q,hq,hnon⟩⟩
  exact parity_original_historical_full_odd_zero_weight_cell_source_zero434
    d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNo χ

/-- Exact full-odd h=-2 physical original k,χ source signed
character is unchanged by discarding those physically attained Z
cells whose *ENTIRE original weighted source is identically zero*.
This is a legitimate COMPLEX finite summation identity, not a
subset absolute-value inequality; it is applied to the original
UNTRUNCATED weighted Cauchy source, before any Fourier cutoff. -/
theorem parity_original_historical_full_odd_k_sum_only_nonzero_Z434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    (∑Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ) =
    ∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k,
      parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ := by
  let S := (parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let F : ℕ → ℂ := fun Z => parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ
  change ∑Z∈S,F Z = ∑Z∈S.filter P,F Z
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z hZ
  change F Z = if P Z then F Z else 0
  by_cases hp : P Z
  · simp only [if_pos hp]
  · have hNot : Z∉parityOriginalHistoricalFullOddNonzeroWeightZCells434
        d L E V hL band slot δ Y e m K J k := by
      intro hmem
      exact hp (Finset.mem_filter.mp hmem).2
    have hF : F Z=0 :=
      parity_original_historical_full_odd_nonselected_Z_source_zero434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNot χ
    simp only [if_neg hp,hF]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddZeroWeightFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- If the real original full-odd-e Q/P physical k/Z cell was
attained, but contains NO nonzero actual eta_e,L*eta_n source
weight, its COMPLETE UNTRUNCATED B633 3D Fourier integral is 0,
by the exact SOURCE Fourier inversion identity. Crucially this
does NOT say the truncated ball integral of the same kernel is 0.

This provides the missing mathematically valid justification for
selecting only nonzero-weight source cells BEFORE Fourier frequency
truncation. Neither complex subset monotonicity nor an artificial
Fourier assumption is used. -/
theorem parity_original_historical_full_odd_zero_weight_B633_full_fourier434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (hZImage : Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k).image
        (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m))
    (hNot : Z∉parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    (∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hBufSmooth hBufSupport ζ) = 0 := by
  obtain ⟨q,hq,hZscale⟩ := Finset.mem_image.mp hZImage
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hProd.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hVal := hMem.2
  have hzpos := (parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m q.1 q.2 he hNe hVal).2.1
  have hdy := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hzpos
  have hZpos : 0<Z := by
    rw [←hZscale]
    exact hdy.1
  have hW := parity_original_historical_full_odd_nonselected_Z_source_zero434
    d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNot χ
  have hFourier := parity_original_historical_true_k_Z_chi_B633_fourier_integral434
    d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ he
    hU hE hV hmLo hmHi hDyad buf a b hBufSmooth hBufSupport hBufOne hZpos
  rw [hW,mul_zero] at hFourier
  exact hFourier.symm
end Green64Analytic.Parity

end

end

