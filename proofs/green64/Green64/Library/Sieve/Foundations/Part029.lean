module

public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part025
public import Green64.Library.Sieve.Foundations.Part020
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part026

@[expose] public section

/-!
# Sieve / Foundations / Part029

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalUngatedSourceToB633 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- EXACT ORIGINAL h=-2 Parity(4.10) TRUE *UNGATED* Cauchy-to-B633
SIGNED PAIR connection at one TWO-ENDED physically supported
source u=m*n-2 and u'=m'*n-2. The e,n SOURCE is now allowed to
contain ANY original P-group prime factor after the legal
pre-Cauchy expansion; only e|u,e|u' and the original reserved
prime-slot H0 source supports are required.

The COMPLETE original α_m αbar_m', H0 skipped-Q factorials,
complex χ(m')conjχ(m), W1, two epsilon signs, rho and three source
m,m',z imaginary powers equal the ACTUAL LITERAL B633 original
(4.16) two-ordinary-core summand at z=m'*(u/e), z'=m*(u'/e).
The separate proven ungated determinant theorem guarantees their
signed shift z+2k=z'. No arbitrary source-support extension is
made, and no Parity(4.17) cancellation theorem is assumed. -/
theorem parity_original_historical_ungated_two_endpoint_source_eq_B633434
    (d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (Y e n m mp u up : ℕ)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n)
    (hup : up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n)
    (hDiv : e∣u) (hDivp : e∣up)
    (hVS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ)
    (hVPS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (up/e) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool) :
    let v := u/e
    let vp := up/e
    let z := mp*v
    let zp := m*vp
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    chi (mp:ZMod q)*star (chi (m:ZMod q)) *
      imaginaryPower m xi1*imaginaryPower mp xi2*imaginaryPower z xi3 *
      ((alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (alpha mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp)) =
    parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
      alpha F.residual q chi F.lo F.hi m mp z zp := by
  dsimp only
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let v := u/e
  let vp := up/e
  have hm : 0 < m := (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := (Finset.mem_filter.mp hup).2.1
  have huPos : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0 < up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hUEq : u=e*v := (Nat.mul_div_cancel_left' hDiv).symm
  have hUPEq : up=e*vp := (Nat.mul_div_cancel_left' hDivp).symm
  have hv : 0 < v := by
    have hh := huPos
    rw [hUEq] at hh
    exact Nat.pos_of_mul_pos_left hh
  have hvp : 0 < vp := by
    have hh := hupPos
    rw [hUPEq] at hh
    exact Nat.pos_of_mul_pos_left hh
  have hM := parity_original_historical_ungated_Cauchy_ENM_eq_physical_AV434
    d L band slot δ ξ rho signed Y e n m u hu hDiv hVS
  have hMp := parity_original_historical_ungated_Cauchy_ENM_eq_physical_AV434
    d L band slot δ ξ rho signed Y e n mp up hup hDivp hVPS
  have hPair := parity_original_historical_ungated_intrinsic_pair_eq_B633434
    d L band slot δ ξ K alpha q chi m mp v vp hm hmp hv hvp
    rho xi1 xi2 xi3 signed
  dsimp only at hPair
  rw [hM,hMp]
  exact hPair
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedSupportedN -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Source natural e|u B509 H0 support for ONE original
h=-2 endpoint m*n=u+2. Unlike the old allocated-e gate, this
may be inhabited when e contains a P-group prime. -/
def parityOriginalHistoricalUngatedPhysicalValidM434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m n : ℕ) : Prop :=
  ∃u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
    e∣u ∧
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e) ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ

/-- The CORRECTED ungated original two-source endpoint support at
fixed e,m,m',n is EXACTLY simultaneous validity of both natural
individual h=-2 B509 prime-slot endpoints. No artificial e-Pfree
condition and no complex signed cancellation assumption. -/
theorem parity_original_historical_ungated_physical_valid_iff_two_rows434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) :
    parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n ↔
    parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e m n ∧
    parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e mp n := by
  constructor
  · rintro ⟨u,hu,up,hup,hdiv,hdivp,hvs,hvps⟩
    exact ⟨⟨u,hu,hdiv,hvs⟩,⟨up,hup,hdivp,hvps⟩⟩
  · rintro ⟨⟨u,hu,hdiv,hvs⟩,⟨up,hup,hdivp,hvps⟩⟩
    exact ⟨u,hu,up,hup,hdiv,hdivp,hvs,hvps⟩

/-- The actual original corrected ungated B509 H0 endpoint at
fixed e,u vanishes if either e does not divide u OR its unique
natural vStar=ordinary_P(u/e) does not belong to the ORIGINAL
reserved Q skip-prime source carrier. The entire H0 convolution,
not an arbitrarily chosen summand, vanishes exactly. -/
theorem parity_original_historical_ungated_fixedEU_zero_without_support434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ)
    (hBad : ¬(e∣u ∧
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e)∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ)) :
    parityOriginalHistoricalUngatedFixedEU434
      d L band slot δ ξ rho signed e u=0 := by
  unfold parityOriginalHistoricalUngatedFixedEU434
  apply Finset.sum_eq_zero
  intro vs hvs
  unfold parityOriginalHistoricalUngatedEVStarAtU434
  have hGuard : ¬(e∣u ∧ vs=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e)) := by
    intro hh
    exact hBad ⟨hh.1,hh.2 ▸ hvs⟩
  simp only [if_neg hGuard]

/-- On an arbitrary original odd-e or non-odd-e post-Cauchy
physical row, the corrected natural a_v(u/e) Cauchy coefficient
is EXACTLY ZERO outside the SOURCE u, B509 prime-slot carrier.
No smoothness or analytic bound is used to remove unsupported n. -/
theorem parity_original_historical_ungated_Cauchy_ENM_zero_without_support434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ)
    (hBad : ¬parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e m n) :
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m=0 := by
  rw [parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434]
  apply Finset.sum_eq_zero
  intro u hu
  apply parity_original_historical_ungated_fixedEU_zero_without_support434
  intro hh
  exact hBad ⟨u,hu,hh.1,hh.2⟩

/-- The COMPLETE actual corrected ungated signed Cauchy h=-2
cofactor pair is zero outside the genuine TWO endpoint B509 natural
prime-slot source carrier. This justifies restricting all later
signed k/Z/χ Fourier sums to the REAL SOURCE image, not a fabricated
formal support or positive majorant. -/
theorem parity_original_historical_ungated_pair_zero_without_physical_N434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ)
    (hBad : ¬parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n) :
    ((α m * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m) *
      star (α mp * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp))=0 := by
  have hNot : ¬(parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e m n ∧
    parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e mp n) := by
    intro hh
    exact hBad ((parity_original_historical_ungated_physical_valid_iff_two_rows434
      d L band slot δ Y e m mp n).mpr hh)
  by_cases hm : parityOriginalHistoricalUngatedPhysicalValidM434
      d L band slot δ Y e m n
  · have hmp : ¬parityOriginalHistoricalUngatedPhysicalValidM434
        d L band slot δ Y e mp n := by
      intro hvalid
      exact hNot ⟨hm,hvalid⟩
    have hz := parity_original_historical_ungated_Cauchy_ENM_zero_without_support434
      d L band slot δ ξ rho signed Y e n mp hmp
    rw [hz]
    simp
  · have hz := parity_original_historical_ungated_Cauchy_ENM_zero_without_support434
      d L band slot δ ξ rho signed Y e n m hm
    rw [hz]
    simp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedOffdiagSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- EXACT original corrected UNGATED Parity(4.10)--(4.13) h=-2
signed physical pair source on arbitrary (e,n,m,m') after
replacing original allocated-Q shortcut by genuine a_v(u/e)
BEFORE Cauchy. This is precisely the offdiagonal pair in the
NATURAL full odd-e positive Gram, not the former gated one. -/
def parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) : ℂ :=
  (α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
    d L band slot δ ξ rho signed Y e n m) *
  star (α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
    d L band slot δ ξ rho signed Y e n mp)

/-- The ACTUAL new full odd-e signed source pair is ZERO unless both
natural e|u and e|u', u=m*n-2,u'=m'*n-2 positive original H0
prime-slot carriers contain the source ordinary_P(u/e).
There is no Pfree-e source gate. This removes all imaginary support
terms before 3D Fourier or χ and does not use any cancellation. -/
theorem parity_original_historical_ungated_offdiag_zero_without_physical_n434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ)
    (hBad : ¬parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n) :
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp=0 := by
  exact parity_original_historical_ungated_pair_zero_without_physical_N434
    d L band slot δ ξ rho α signed Y e n m mp hBad

/-- Corrected ungated original source offdiagonal at fixed odd e
and distinct m,m' is ZERO when the arbitrary formal integer
quotient k=(m'-m)/e is zero: a real physical event would instead
force the exact nonzero determinant m'-m=e*k, an impossibility.
This is essential for correct χ modulus q=2|k| in Parity(2.6).
It does not assume e Pfree or any source k-window bound. -/
theorem parity_original_historical_ungated_zero_k_physical_source_vanishes434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) (he : Odd e) (hne : m≠mp)
    (hkZero : parityOriginalHistoricalOffdiagK434 e m mp=0) :
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp=0 := by
  by_cases hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n
  · have hReal := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m mp n he hne hValid
    dsimp only at hReal
    exact False.elim (hReal.1 hkZero)
  · exact parity_original_historical_ungated_offdiag_zero_without_physical_n434
      d L band slot δ ξ rho α signed Y e n m mp hValid

/-- EXACT signed finite sum for every fixed full-odd e,m,m' after
restricting n to the REAL corrected H0 physical support. The
ungated original η_eη_n weight stays inside the actual n fibre,
not replaced by a triangle inequality or a guessed large z set. -/
theorem parity_original_historical_ungated_weighted_n_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (w : ℕ → ℂ) (J : Finset ℕ) :
    (∑n∈J,w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp) =
    ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp),
      w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n
  · simp only [if_pos hValid]
  · have hh := parity_original_historical_ungated_offdiag_zero_without_physical_n434
      d L band slot δ ξ rho α signed Y e n m mp hValid
    simp [hValid,hh]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedSupportedKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- CORRECTED ungated physical ORIGINAL Parity(4.13) true canonical z
source, at fixed arbitrary all-odd e,m,m' and real B509 n source:
only natural e|u,e|u' and vStar=ordinaryP(u/e) H0 actual support,
NOT the old e*vStar=ordinaryP(u) Pfree-e gate. A source term at
z is retained iff at least one actual n has those two original
prime-slot source supports and canonical z=m'*(mn-2)/e. -/
def parityOriginalHistoricalUngatedPhysicalValidZSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (parityOriginalHistoricalCanonicalZSupport434 e m mp J).filter
    (fun z => ((parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp)).Nonempty)

/-- Exact complex SOURCE ungated n filter: all nonphysical n vanish
by their complete natural a_v(u/e) original B509 endpoints. -/
theorem parity_original_historical_ungated_weighted_N_source_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (w : ℕ → ℂ) (J : Finset ℕ) :
    (∑n∈J,w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp) =
    ∑n∈J.filter
      (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp),
      w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hv : parityOriginalHistoricalUngatedPhysicalValidN434
    d L band slot δ Y e m mp n
  · simp only [if_pos hv]
  · have hh := parity_original_historical_ungated_offdiag_zero_without_physical_n434
      d L band slot δ ξ rho α signed Y e n m mp hv
    simp [hv,hh]

/-- The source-signed weighted original n -> z image reindex, with
every actual e,n smooth weight STILL INSIDE the unique n fibre.
It does not incorrectly pull eta_n(n/V) outside the source z sum. -/
theorem parity_original_historical_ungated_weighted_z_source_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (w : ℕ → ℂ) (J : Finset ℕ) :
    (∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
      ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
        w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp) =
    ∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
      ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp),
        w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  let NF : ℕ → Finset ℕ :=
    parityOriginalHistoricalCanonicalZNFibre434 e m mp J
  let V : ℕ → Prop :=
    parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp
  have hOne (z : ℕ) :
    (∑n∈NF z,w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp) =
    ∑n∈(NF z).filter V,
      w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp :=
    parity_original_historical_ungated_weighted_N_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp w (NF z)
  calc
    _ = ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        ∑n∈(NF z).filter V,
          w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hOne z
    _ = ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        if ((NF z).filter V).Nonempty then
          (∑n∈(NF z).filter V,
            w n*parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hv : ((NF z).filter V).Nonempty
      · simp only [if_pos hv]
      · have hempty : (NF z).filter V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
        simp [hv,hempty]
    _ = _ := by
      unfold parityOriginalHistoricalUngatedPhysicalValidZSupport434
      rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullOddOffdiagKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- SOURCE-correct original full all-odd e×n h=-2 SIGNED
UN-GATED k,z physical reindex: all full-odd e (including Pbad e)
use their NATURAL a_v(u/e) B509 H0 prime slots, not the old
selected-Q e*vStar=ordinary_P(u) shortcut. Unpopulated source
n and z vanish exactly, and canonical k=0 is excluded only after
proving its physical impossibility for odd e and m≠m'.
This is the first exact signed k/Z reindex of the CORRECTED original
Parity(4.10) source, and does NOT itself assert the 4.17 saving. -/
def parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑e∈Eenv,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
            d L band slot δ Y e m mp Nenv,
            ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
              (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp),
              ((w e n:ℝ):ℂ) *
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

theorem parity_original_historical_ungated_weighted_full_odd_offdiag_k_z_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hOdd : ∀ e∈Eenv, Odd e) :
    parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w =
    parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := Eenv
  let F : ℕ → ℕ → ℕ → ℕ → ℂ := fun e n m mp =>
    ((w e n:ℝ):ℂ) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  have hPoint (e n m mp : ℕ) :
      ((w e n:ℝ):ℂ) *
      ((α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m) *
       star (α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)) = F e n m mp := by
    rfl
  have hZero (e n m : ℕ) (he : e∈Q) :
      (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K 0,F e n m mp)=0 := by
    apply Finset.sum_eq_zero
    intro mp hmp
    have hp := Finset.mem_filter.mp hmp
    have hne : m≠mp := (Finset.mem_erase.mp hp.1).1.symm
    have hz := parity_original_historical_ungated_zero_k_physical_source_vanishes434
      d L band slot δ ξ rho α signed Y e n m mp
      (hOdd e he) hne hp.2
    dsimp [F]
    rw [hz,mul_zero]
  unfold parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
  simp_rw [Finset.mul_sum]
  change (∑e∈Q,∑n∈Nenv,∑m∈K,∑mp∈K.erase m,
      ((w e n:ℝ):ℂ)*
      ((α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
       star (α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp))) = _
  calc
    _ = ∑e∈Q,∑n∈Nenv,∑m∈K,∑mp∈K.erase m,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hPoint e n m mp
    _ = ∑e∈Q,∑n∈Nenv,∑m∈K,
        ∑k∈parityOriginalHistoricalKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact parity_original_historical_cofactor_sum_eq_k_fibres434 e m K (F e n m)
    _ = ∑e∈Q,∑n∈Nenv,∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      let S := parityOriginalHistoricalKSupport434 e m K
      let H : ℤ → ℂ := fun k =>
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp
      change (∑k∈S,H k)=(∑k∈S.filter (·≠0),H k)
      calc
        _ = ∑k∈S,if k≠0 then H k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : k=0
          · subst k
            simpa only [if_neg (by decide : ¬ ((0:ℤ) ≠ 0))] using (hZero e n m he)
          · simp [h]
        _ = _ := by rw [Finset.sum_filter]
    _ = ∑e∈Q,∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
            ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp Nenv,
              ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z,
              F e n m mp :=
      parity_original_historical_k_then_z_source_reindex434 Q K Nenv F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro mp hmp
      exact parity_original_historical_ungated_weighted_z_source_filter_exact434
        d L band slot δ ξ rho α signed Y e m mp
        (fun n => ((w e n:ℝ):ℂ)) Nenv
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedMaskInsert -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- TRUE ORIGINAL UNGATED Parity(2.6) χ-character mask, inserted
BEFORE summing any B633(4.17) source terms into the corrected
full odd-e signed physical k,z,n fibre. Every source e may
contain original P group primes, unlike the old gated branch.
A character identity is applied ONLY when the FULL actual
η_e(e/E)η_n(n/V) signed source is nonzero. -/
theorem parity_eventually_original_ungated_supported_z_fine_mask_insert434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (signed prime : Bool) (lFine uFine e m mp z : ℕ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalFullOddEEnvelope434 E →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp Nenv →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      let W := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434
        e m mp Nenv z).filter
          (parityOriginalHistoricalUngatedPhysicalValidN434
            (sourceOriginalLiteralDepth 20 L) L band slot δ
            ⌊2*Real.exp L⌋₊ e m mp),
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
            ⌊2*Real.exp L⌋₊ e n m mp
      W = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        (parityShiftTwoMaskCoefficient434 k.natAbs χ *
          χ (mp : ZMod (2*k.natAbs)) *
          star (χ (m : ZMod (2*k.natAbs)))) * W := by
  filter_upwards [parity_eventually_original_ungated_full_odd_smooth_fine_mask434
    S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv signed prime lFine uFine
    e m mp z hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    hl hFineLow
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let N := (parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
    (parityOriginalHistoricalUngatedPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp)
  let W : ℂ := ∑n∈N,
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
        ⌊2*Real.exp L⌋₊ e n m mp
  change W = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
    (parityShiftTwoMaskCoefficient434 k.natAbs χ *
      χ (mp : ZMod (2*k.natAbs)) *
      star (χ (m : ZMod (2*k.natAbs)))) * W
  by_cases hW : W=0
  · rw [hW]
    simp
  have hAm : alpha m ≠ 0 := by
    intro ham
    have hZero : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      simp [ham]
    exact hW hZero
  have hAmp : alpha mp ≠ 0 := by
    intro hamp
    have hZero : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      simp [hamp]
    exact hW hZero
  obtain ⟨n,hn,hTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp n := (Finset.mem_filter.mp hn).2
  have hWeight : parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n ≠ 0 := by
    intro hw0
    apply hTerm
    rw [hw0]
    simp
  have hEta : parityOriginalHistoricalDyadicEtaEAtLReal434 L hLw ((e:ℝ)/E) ≠ 0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hWeight
    intro h0
    exact hWeight (by rw [h0,zero_mul])
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  have hNe : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have hFull := hMask.2 hLw band slot δ U E K prime lFine uFine
    hU hScale hl hFineLow e m mp n heOdd hNe
    hmLo hmHi hmpLo hmpHi hEta hValid hAm hAmp
  dsimp only at hFull
  exact parity_original_exact_mask_insert_complex434 k m mp W hFull.2.2.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCharacterOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Genuine CORRECTED natural ungated full-odd signed (4.13)
physical source after exact Parity(2.6) χ mask, and exact finite
χ-OUTER reindex cχ*conjχ(m) outside the mp,z,n sum. The actual
source e may contain any P-group prime, including its full power;
the true original B509 natural a_v(u/e), η_eη_n, and odd e are
unmodified. No analytic 4.17 saving is assumed. -/
def parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑e∈Eenv,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
            d L band slot δ Y e m mp Nenv,
            ∑chi : DirichletCharacter ℂ (2*k.natAbs),
              (parityShiftTwoMaskCoefficient434 k.natAbs chi *
                chi (mp : ZMod (2*k.natAbs)) *
                star (chi (m : ZMod (2*k.natAbs)))) *
              (∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
                (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp),
                ((w e n:ℝ):ℂ)*
                parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp)


def parityOriginalHistoricalUngatedFullOddCharacterOuter434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e∈Eenv,
    ∑ m∈K,
      ∑ k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          (parityShiftTwoMaskCoefficient434 k.natAbs chi *
            star (chi (m : ZMod (2*k.natAbs)))) *
          (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
            chi (mp : ZMod (2*k.natAbs)) *
              (∑ z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
                d L band slot δ Y e m mp Nenv,
                ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
                  (parityOriginalHistoricalUngatedPhysicalValidN434
                    d L band slot δ Y e m mp),
                  ((w e n:ℝ):ℂ) * parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                    d L band slot δ ξ rho α signed Y e n m mp))

/-- Source-faithful original signed after-mask finite Fubini. In
particular the Dirichlet character is NOT applied to the unsigned
odd-parity projector and no character count is paid before using the
source-proven (2.6) ℓ1 mask bound. -/
theorem parity_original_historical_ungated_full_odd_masked_k_z_eq_character_outer434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w =
    parityOriginalHistoricalUngatedFullOddCharacterOuter434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  unfold parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
    parityOriginalHistoricalUngatedFullOddCharacterOuter434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let Q : Finset (DirichletCharacter ℂ (2*k.natAbs)) := Finset.univ
  let Z : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalUngatedPhysicalValidZSupport434
      d L band slot δ Y e m mp Nenv
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      star (chi (m : ZMod (2*k.natAbs)))
  let f : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
    fun chi mp => chi (mp : ZMod (2*k.natAbs))
  let Wfz : ℕ → ℕ → ℂ := fun mp z =>
    ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
      (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp),
      ((w e n:ℝ):ℂ) * parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  change (∑mp∈M,∑z∈Z mp,∑chi∈Q,
    (parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) * Wfz mp z) =
    ∑chi∈Q,c chi*(∑mp∈M,f chi mp*(∑z∈Z mp,Wfz mp z))
  calc
    _ = ∑mp∈M,∑z∈Z mp,∑chi∈Q,(c chi*f chi mp)*Wfz mp z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro chi hchi
      dsimp [c,f]
      ring
    _ = _ := parity_original_character_outer_finite_fubini434 M Q Z c f Wfz
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCharacterJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- FULL CORRECTED original Parity (4.10)--(4.13) signed h=-2
UNGATED source Cauchy offdiagonal EXACTLY equals its Dirichlet
character-outer k,z physical sum, for every original B509 natural
a_v(u/e) even when e has P-group primes. This is a SOURCE
identity derived from source true η_eη_n nonzero weighting and
original fine b629 W-rough α; neither χ count nor formal original
unrestricted (4.17) cancellation was assumed. -/
theorem parity_eventually_original_ungated_full_odd_fine_offdiag_masked434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_ungated_supported_z_fine_mask_insert434
      S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  have hOdd : ∀e∈parityOriginalHistoricalFullOddEEnvelope434 E,Odd e := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  rw [parity_original_historical_ungated_weighted_full_odd_offdiag_k_z_exact434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    alpha signed ⌊2*Real.exp L⌋₊ w hOdd]
  unfold parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
    parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro z hz
  have hmpMem : mp∈K.erase m := (Finset.mem_filter.mp hmp).1
  have hkCanon : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    (Finset.mem_filter.mp hmp).2
  have hmD := hDyad m hm
  have hmpD := hDyad mp (Finset.mem_erase.mp hmpMem).2
  have hPoint := hMask.2 hLw band slot δ ξ U E V rho K Nenv signed prime
    lFine uFine e m mp z hU hScale hmD.1 hmD.2 hmpD.1 hmpD.2
    he hm hmpMem hz hl hFineLow
  dsimp only at hPoint
  rw [hkCanon] at hPoint
  exact hPoint


theorem parity_eventually_original_ungated_full_odd_fine_offdiag_eq_character_outer434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalUngatedFullOddCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_ungated_full_odd_fine_offdiag_masked434
      S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [hMask.2 hLw band slot δ ξ U E V rho K Nenv prime signed
    lFine uFine hU hScale hDyad hl hFineLow]
  exact parity_original_historical_ungated_full_odd_masked_k_z_eq_character_outer434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed ⌊2*Real.exp L⌋₊
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedSourceLogPullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- TRUE corrected Parity §4.14 ungated source pullback at physical
m*n=e*v+2, m'*n=e*v'+2, with source u>0, e|u and original
B509 Vstar=ordinary_P(u/e) support. This is the original h=-2,
full r20 two-coordinate identity INCLUDING +2/(U*V)*exp(-t1)
from the genuine shared n; it holds even when e contains group-P
prime factors. Neither the previous source Q-selected e nor its
e*vStar=ordinary_P(u) shortcut appears. The exact canonical k and
z are used in all three source log coordinates. -/
theorem parity_original_historical_ungated_source_log_cutoff_pullbacks434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E)
    (hV : 0<V) (hZ : 0<Z) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let t1 := Real.log ((m:ℝ)/U)
    let t2 := Real.log ((mp:ℝ)/U)
    let t3 := Real.log ((z:ℝ)/Z)
    (e:ℝ)/E=(U/((k:ℝ)*E))*(Real.exp t2-Real.exp t1) ∧
    (n:ℝ)/V=(Z/((k:ℝ)*U*V))*Real.exp t3 *
      (Real.exp (-t1)-Real.exp (-t2))+
      (2/(U*V))*Real.exp (-t1) := by
  dsimp only
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hValid
  have hm : 0 < m := (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := (Finset.mem_filter.mp hup).2.1
  have hmn : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hUeq : u=e*(u/e) := (Nat.mul_div_cancel_left' hDiv).symm
  have hZeq : parityOriginalHistoricalCanonicalZ434 e m mp n=mp*(u/e) := by
    unfold parityOriginalHistoricalCanonicalZ434 parityOriginalHistoricalCanonicalV434
    have hMN : m*n-2=u := by omega
    rw [hMN]
  have hEz : e*parityOriginalHistoricalCanonicalZ434 e m mp n=mp*u := by
    calc
      _ = e*(mp*(u/e)) := by rw [hZeq]
      _ = mp*(e*(u/e)) := by ring
      _ = mp*u := by rw [←hUeq]
  have hPhys := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m mp n he hneq
    ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩
  dsimp only at hPhys
  obtain ⟨hk,hz,hzp,hDet,hZShift⟩ := hPhys
  constructor
  · exact parity_original_historical_log_dyadic_e_pullback434
      U E e m mp (parityOriginalHistoricalOffdiagK434 e m mp)
      hU hE hm hmp hk hDet
  · exact parity_original_historical_log_dyadic_n_pullback434
      U V Z e m mp n u (parityOriginalHistoricalCanonicalZ434 e m mp n)
      (parityOriginalHistoricalOffdiagK434 e m mp)
      hU hV hZ hm hmp hz hk hmn hDet hEz
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFourier3DSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- True corrected UNGATED original Parity (4.14) physical eta_e(e/E)
eta_n(n/V) logarithmic pullback including exact h=-2 correction
and true k=(m'-m)/e, no selected-Q/Pfree e gate. -/
theorem parity_original_historical_ungated_supported_eta_e_eta_n_pullback434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z)
    (etaE etaN : ℝ → ℂ) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let t1 := Real.log ((m:ℝ)/U)
    let t2 := Real.log ((mp:ℝ)/U)
    let t3 := Real.log ((z:ℝ)/Z)
    etaE ((e:ℝ)/E)*etaN ((n:ℝ)/V) =
      etaE ((U/((k:ℝ)*E))*(Real.exp t2-Real.exp t1)) *
      etaN ((Z/((k:ℝ)*U*V))*Real.exp t3 *
        (Real.exp (-t1)-Real.exp (-t2))+
        (2/(U*V))*Real.exp (-t1)) := by
  dsimp only
  have hOriginal := parity_original_historical_ungated_source_log_cutoff_pullbacks434
    d L band slot δ Y e m mp n he hneq hValid U E V Z hU hE hV hZ
  dsimp only at hOriginal
  rw [hOriginal.1,hOriginal.2]


/-- True 3D Schwartz source at ORIGINAL natural ungated e|u,
vs=ordinary_P(u/e) B509 real endpoints, valid also for e with
original P-group primes. No Fourier truncation assumed. -/
theorem parity_original_historical_ungated_source_eta_equals_euclidean_3d434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z)
    (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    parityOriginalHistoricalPulledEuclidean3D434 U E V Z
      (parityOriginalHistoricalOffdiagK434 e m mp)
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp
         (parityOriginalHistoricalCanonicalZ434 e m mp n)) =
      buf (Real.log ((m:ℝ)/U)) * buf (Real.log ((mp:ℝ)/U)) *
      buf (Real.log ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z)) *
      (etaE ((e:ℝ)/E)*etaN ((n:ℝ)/V)) := by
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  have hEta := parity_original_historical_ungated_supported_eta_e_eta_n_pullback434
    d L band slot δ Y e m mp n he hneq hValid U E V Z hU hE hV hZ
    etaE etaN
  dsimp only at hEta
  rw [parity_original_historical_pulled_euclidean_3d_apply434]
  unfold parityOriginalHistoricalPulledBuffered3D434
    parityOriginalHistoricalPulledCutoff3D434
    parityOriginalHistoricalEtaELogArg434
    parityOriginalHistoricalEtaNLogArg434
    parityOriginalHistoricalRealLogTriple434
  simp only [ContinuousLinearEquiv.apply_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  dsimp [Matrix.vecHead, Matrix.vecTail]
  rw [← hEta]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPhysicalFiniteFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- **TRUE ORIGINAL UNGATED Parity (4.14)** exact pulled 3D η_eη_n
Schwartz at actual B509 source e|u,u' and real k,Z dyadic support,
even when e contains original P primes. Original Fourier 2π phase
and fixed buffers 1 on true source dyads. -/
theorem parity_original_historical_ungated_dyadic_eta_physical_point_3d434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ))
    (hzHi : (parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)≤2*Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1) :
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ)=
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp
        (parityOriginalHistoricalCanonicalZ434 e m mp n)) := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  have hSource := parity_original_historical_ungated_source_eta_equals_euclidean_3d434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ buf etaE etaN a b
    hBufSmooth
    (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport
  rw [hk] at hSource
  have hBox := parity_original_historical_log_three_coordinate_box434
    U Z m mp (parityOriginalHistoricalCanonicalZ434 e m mp n)
    hU hZ hmLo hmHi hmpLo hmpHi hzLo hzHi
  have hb0 := hBufOne (Real.log ((m:ℝ)/U)) ⟨hBox.1,hBox.2.1⟩
  have hb1 := hBufOne (Real.log ((mp:ℝ)/U))
    ⟨hBox.2.2.1,hBox.2.2.2.1⟩
  have hb2 := hBufOne (Real.log ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z))
    ⟨hBox.2.2.2.2.1,hBox.2.2.2.2.2⟩
  rw [hb0,hb1,hb2] at hSource
  have hWeight := parity_original_historical_dyadic_eta_weight_is_complex_product434
    L E V hL e n
  simp only [one_mul] at hSource
  exact hWeight.trans hSource.symm

/-- EXACT FULL REAL original source finite physical Fourier identity
on one fixed selected e,m,k,Z and dyadic U,E,V. Every actual
physical (m',n) event is source-valid; each canonical z=m'v is in
its true Z-dyad, and every m' belongs to the SAME canonical k-fibre.
The arbitrary complex W includes true original signed H0, reserved
Q/P, fine b629 alpha, parity and characters; no independence of W
or spectral saving is assumed. The Fourier transform is ONE COMMON
source-constructed η_e,L*η_n Schwartz kernel for all physical events.
This is the precise finite SOURCE pre-(4.16) Fourier factorization. -/
theorem parity_original_historical_ungated_source_physical_finite_3d_fourier434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (mp n : ι → ℕ)
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (he : Odd e)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hPhysical : ∀ i∈S, m≠mp i ∧
      parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m (mp i) (n i) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp i)=k ∧
      U≤(mp i:ℝ) ∧ (mp i:ℝ)≤2*U ∧
      Z≤(parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)≤2*Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1) :
    (∑i∈S,W i*((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) =
    ∫ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W
        (parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n)
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let t : ι → EuclideanSpace ℝ (Fin 3) :=
    parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  have hTerm (i : ι) (hi : i∈S) :
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)=f (t i) := by
    obtain ⟨hNe,hValid,hK,hMpLo,hMpHi,hZLo,hZHi⟩ := hPhysical i hi
    exact parity_original_historical_ungated_dyadic_eta_physical_point_3d434
      d L hL band slot δ Y e m (mp i) (n i) he hNe hValid
      U E V Z hU hE hV hZ k hK hmLo hmHi hMpLo hMpHi hZLo hZHi
      buf a b hBufSmooth hBufSupport hBufOne
  calc
    _ = parityOriginal3DPhysicalFiniteSignal434 S W t f := by
      unfold parityOriginal3DPhysicalFiniteSignal434
      apply Finset.sum_congr rfl
      intro i hi
      rw [hTerm i hi]
    _ = _ := parity_original_3d_physical_finite_source_fourier_fubini434 S W t f
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedActualKZFourierCarrier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23500000

/-- Genuine full-odd source B509 natural e|u original H0 physical
k/Z carrier, χ-weighted true h=-2 signed α/ε/W1 coefficient, and
exact 3D Fourier transform of actual smoothed η_eη_n SOURCE for
any e including group P factors. All finite physical q=(m',n)
are sourced from the new ungated 4.10 Cauchy, never imported from
the old selected-Q Pfree-e carrier. -/
def parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ) :
    Finset (ℕ × ℕ) :=
  ((parityOriginalHistoricalKPrimeFibre434 e m K k).product J).filter
    (fun q =>
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m q.1 q.2 ∧
      0 < parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 ∧
      parityOriginalHistoricalActualZDyadicScale434
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) = Z)

/-- Every element of the REAL canonical source k/Z carrier satisfies
all hypotheses of the genuine original 3D Fourier physical event:
common k and Z, original m'∈K.erase m, populated Q/P n gates and
positive z∈[Z,2Z]. No unsupported formal n or a distinct synthetic
z is admitted. The cofactor m' dyad is an external original K input. -/
theorem parity_original_historical_ungated_actual_k_z_event_physical434
    (d : ℕ) (L U : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z) :
    m≠q.1 ∧
    parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 ∧
    parityOriginalHistoricalOffdiagK434 e m q.1=k ∧
    U≤(q.1:ℝ) ∧ (q.1:ℝ)≤2*U ∧
    (Z:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤2*(Z:ℝ) := by
  have hMem := Finset.mem_filter.mp hq
  have hPr := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hPr.1
  have hNe := (Finset.mem_erase.mp hMP.1).1.symm
  have hMPK := (Finset.mem_erase.mp hMP.1).2
  have hR := hDyad q.1 hMPK
  obtain ⟨hValid,hZpos,hZscale⟩ := hMem.2
  have hD := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hZpos
  rw [hZscale] at hD
  refine ⟨hNe,hValid,hMP.2,hR.1,hR.2,?_,?_⟩
  · exact_mod_cast hD.2.1
  · have hh : (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) <
      2*(Z:ℝ) := by exact_mod_cast hD.2.2
    exact hh.le

/-- Real original full h=-2 Parity source cofactor coefficient with
true physical H0 two-endpoint signed epsilon, full original b629
fine alpha and Dirichlet character modulo 2|k|. The source eta_e/n
weight is intentionally NOT part of W: it is the actual common
3D Schwartz Fourier multiplier on the k/Z physical fibre. -/
def parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (q : ℕ×ℕ) : ℂ :=
  χ (q.1 : ZMod (2*k.natAbs)) *
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1

/-- EXACT physical SOURCE signed character k/Z Cauchy sub-fibre
with original n-dependent smoothing weight. No ℓ1 bound or Fourier
saving is applied in this definition. -/
def parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) : ℂ :=
  ∑q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
    parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
      d L band slot δ ξ rho α signed Y e m k χ q *
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ)

/-- **SOURCE ORIGINAL (4.13)-(4.15) FINITE 3D FOURIER JOIN**.
The literal original Q/P supported k/Z fibre of m' and n, with
canonical z and original signed H0/b629 fine alpha/χ pair, equals
one genuine Euclidean 3D Fourier integral for the quantitatively
constructed original η_e(e/E)η_n(n/V) smoothed Cauchy weight.
No synthetic or additional physical term or Fourier multiplier is
assumed. This closes the exact SOURCE finite k/Z Fourier algebra
before the still-open 4.17 endpoint identification. -/
theorem parity_original_historical_ungated_actual_k_z_physical_fourier434
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
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1)
    (hZ : 0<Z) :
    parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y e m K J k Z)
        (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
          d L band slot δ ξ rho α signed Y e m k χ)
        (parityOriginalHistoricalPhysicalFourierEventTriple434
          (U:ℝ) (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ := by
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let mp : (ℕ×ℕ)→ℕ := fun q=>q.1
  let n : (ℕ×ℕ)→ℕ := fun q=>q.2
  have hPhysical : ∀q∈S,
      m≠mp q ∧ parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m (mp q) (n q) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp q)=k ∧
      U≤(mp q:ℝ) ∧ (mp q:ℝ)≤2*U ∧
      (Z:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ)≤2*(Z:ℝ) := by
    intro q hq
    exact parity_original_historical_ungated_actual_k_z_event_physical434
      d L U band slot δ Y e m K J k Z hDyad q hq
  have h := parity_original_historical_ungated_source_physical_finite_3d_fourier434
    S W mp n d L hL band slot δ Y e m he
    U E V (Z:ℝ) hU hE hV (by exact_mod_cast hZ)
    k hmLo hmHi hPhysical buf a b hBufSmooth hBufSupport hBufOne
  exact h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedActualKZB633Finite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The original Parity(4.16) B633 TWO-PRIME-SLOT finite SUM on the
NEW natural UNGATED r20 h=-2 physical e,m,k,Z source is exactly
its actual source signed χ-weighted Cauchy pair kernel with
original B509/H0 W1, eps=1/E, b629 α, 2π Fourier powers,
Pparts, and original u=m*n-2, even when e contains P-group
prime factors. No fake negative-k source or unbounded 4.17
correlation and no analytic estimate. -/
theorem parity_original_historical_ungated_actual_k_z_full_finite_eq_B633434
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
    let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
    (∑q∈S,
      star (chi (m : ZMod (2*k.natAbs))) *
      imaginaryPower m xi1 * imaginaryPower q.1 xi2 *
      imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) xi3 *
      parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho alpha signed Y e m k chi q) =
    ∑q∈S,
      parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
        alpha F.residual (2*k.natAbs) chi F.lo F.hi m q.1
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
        (((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat) := by
  dsimp only
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
  apply Finset.sum_congr rfl
  intro q hq
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hProd.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 := hMem.2.1
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hValid
  have huMN : m*q.2=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hupMN : q.1*q.2=up+2 := (Finset.mem_filter.mp hup).2.2.2
  have hUEq : u=e*(u/e) := (Nat.mul_div_cancel_left' hDiv).symm
  have hUPEq : up=e*(up/e) := (Nat.mul_div_cancel_left' hDivp).symm
  have hMN : m*q.2=e*(u/e)+2 := by
    calc
      _ = u+2 := huMN
      _ = e*(u/e)+2 := congrArg (fun t:ℕ=>t+2) hUEq
  have hMpN : q.1*q.2=e*(up/e)+2 := by
    calc
      _ = up+2 := hupMN
      _ = e*(up/e)+2 := congrArg (fun t:ℕ=>t+2) hUPEq
  have hKData := parity_original_historical_ungated_two_endpoint_signed_k_exists434
    e q.2 m q.1 (u/e) (up/e) he hMN hMpN
  obtain ⟨k0,hDet,hVShift,hShift⟩ := hKData
  have hKCan : parityOriginalHistoricalOffdiagK434 e m q.1=k0 :=
    parity_original_historical_physical_k_eq_quotient434 e m q.1 he.pos k0 hDet
  have hZpoint : parityOriginalHistoricalCanonicalZ434 e m q.1 q.2=q.1*(u/e) := by
    unfold parityOriginalHistoricalCanonicalZ434 parityOriginalHistoricalCanonicalV434
    have hU : m*q.2-2=u := by omega
    rw [hU]
  have hZpPoint : ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat=
      m*(up/e) := by
    have hsh : ((q.1*(u/e):ℕ):ℤ)+2*k=((m*(up/e):ℕ):ℤ) := by
      have hk0 : k0=k := by rw [←hKCan]; exact hMP.2
      rw [hk0] at hShift
      simpa only [Nat.cast_mul] using hShift
    rw [hZpoint]
    have hh := congrArg Int.toNat hsh
    simpa only [Int.toNat_natCast] using hh
  have hPoint := parity_original_historical_ungated_two_endpoint_source_eq_B633434
    d L band slot δ ξ K alpha (2*k.natAbs) chi
    Y e q.2 m q.1 u up hu hup hDiv hDivp hVS hVPS
    rho xi1 xi2 xi3 signed
  dsimp only at hPoint
  have hk : parityOriginalHistoricalOffdiagK434 e m q.1=k := hMP.2
  unfold parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
  rw [hZpPoint,hZpoint]
  calc
    _ = chi (q.1 : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))) *
          imaginaryPower m xi1 * imaginaryPower q.1 xi2 *
          imaginaryPower (q.1*(u/e)) xi3 *
          ((alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
             d L band slot δ ξ rho signed Y e q.2 m) *
           star (alpha q.1*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
             d L band slot δ ξ rho signed Y e q.2 q.1)) := by ring
    _ = parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
        alpha F.residual (2*k.natAbs) chi F.lo F.hi m q.1
        (q.1*(u/e)) (m*(up/e)) := hPoint
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedActualKZUniqueCofactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- True corrected natural UNGATED physical original h=-2
B509 source e,m,m' with two positive endpoint u,u' and H0,
canonical signed k=(m'-m)/e exactly, and k-fibre cofactor m'
UNIQUE even if original e has P-group prime divisors. Source
N and z may have multiple terms but unique m' for one e,m,k.
No arbitrary signed-complex subset majorization or original
selected-Q e prime-free shortcut is used. -/
theorem parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n) :
    (mp:ℤ)-(m:ℤ)=(e:ℤ)*parityOriginalHistoricalOffdiagK434 e m mp := by
  have hActual := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m mp n he hneq hValid
  dsimp only at hActual
  exact hActual.2.2.2.1

/-- At fixed ORIGINAL selected e,m and canonical integer k,
there is at most ONE real physical m' on ANY genuinely populated
h=-2 source data, even if source n and canonical z vary.
This is purely arithmetic m'=m+e*k; it does not assert a singleton
for every formal quotient fibre outside physical Q/P support. -/
theorem parity_original_historical_ungated_physical_same_k_cofactor_unique434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp mp' n n' : ℕ) (k : ℤ) (he : Odd e)
    (hneq : m≠mp) (hneq' : m≠mp')
    (hn : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hn' : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp' n')
    (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hk' : parityOriginalHistoricalOffdiagK434 e m mp'=k) : mp=mp' := by
  have h := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hneq hn
  have h' := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
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
theorem parity_original_historical_ungated_actual_k_z_physical_cofactor_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) :
    ((parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
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
  have hUnique := parity_original_historical_ungated_physical_same_k_cofactor_unique434
    d L band slot δ Y e m x x' n n' k he hneq hneq'
    hData.2.1 hData'.2.1 hXM.2 hXM'.2
  calc
    mp = x := hxEq.symm
    _ = x' := hUnique
    _ = mp' := hxEq'
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedDyadicEvents -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Original full odd-e corrected natural Parity(4.10) real h=-2
Q/B509 physical k,m',n events partition into their GENUINE
binary Z image with exact 1:1 finite SOURCE cofactor and n entries.
No e P-free gate, no imaginary Z and no complex-subset inequality.
The new full odd-e SOURCE valid n determines positive z and z+2k. -/
def parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  ((parityOriginalHistoricalKPrimeFibre434 e m K k).product J).filter
    (fun q => parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m q.1 q.2)

/-- On the true original h=-2 physical TWO-ENDPOINT carrier and
odd e, EVERY real source canonical z is strictly positive.
Therefore imposing positivity before dyadic Z grouping does NOT
remove a genuine source event or silently add an unsupported one.
The binary Z-fibre is EXACTLY the original already constructed
`ActualKZPhysicalEventCarrier434` used by 3D source Fourier.
This is source-to-Fourier SUPPORT equality, not a cancellation bound. -/
theorem parity_original_historical_ungated_full_odd_Z_event_fibre_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) :
    (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).filter
      (fun q => parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q=Z) =
    parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z := by
  ext q
  constructor
  · intro hq
    obtain ⟨hBase,hScale⟩ := Finset.mem_filter.mp hq
    obtain ⟨hProd,hValid⟩ := Finset.mem_filter.mp hBase
    have hNe : m≠q.1 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hProd).1).1).1.symm
    have hPos := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 he hNe hValid
    dsimp only at hPos
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
theorem parity_original_historical_ungated_full_odd_k_Z_image_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (W : (ℕ×ℕ) → ℂ) :
    (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q) =
    ∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      ∑q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,W q := by
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
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
      rw [parity_original_historical_ungated_full_odd_Z_event_fibre_exact434
        d L band slot δ Y e m K J k Z he]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedKZFourierSourceJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24500000

/-- On the CORRECTED real full-odd-e B509 source, the original
signed physical m'→canonical z→actual n sum at fixed e,m,k,χ
is IDENTICAL to the original signed finite m'×n event carrier,
then to its exact attained binary Z image, including every source
P-bad e. This statement is about the full signed complex sum,
never a positive or unrestricted-Parity4.17 correlation estimate.
The source η_eη_n weight stays inside n and no Fourier cutoff is
introduced or moved across source support. -/
theorem parity_original_historical_ungated_character_k_z_eq_binary_events434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e) :
    (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
          d L band slot δ Y e m mp J,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalUngatedPhysicalValidN434
              d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)) =
    ∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
        (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ := by
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  let W : (ℕ×ℕ) → ℂ := fun q =>
    χ (q.1 : ZMod (2*k.natAbs)) *
      (((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ) *
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1)
  have hPerMp (mp : ℕ) (hmp : mp∈M) :
      (∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
          d L band slot δ Y e m mp J,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalUngatedPhysicalValidN434
              d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp) =
      ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp),
          ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp := by
    let v : ℕ → ℂ := fun n =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp
    have hZ := parity_original_historical_ungated_weighted_z_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp
      (fun n => ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ)) J
    have hN := parity_original_historical_ungated_weighted_N_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp
      (fun n => ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ)) J
    have hRe := parity_original_historical_n_sum_eq_canonical_z_fibres434 e m mp J v
    change (∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
      ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),v n) =
      ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),v n
    calc
      _ = ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
            ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,v n := hZ.symm
      _ = ∑n∈J,v n := hRe.symm
      _ = _ := hN
  have hProduct :
      (∑mp∈M,∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp),W (mp,n)) =
      ∑q∈S,W q := by
    unfold S parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    calc
      _ = ∑mp∈M,∑n∈J,
            if parityOriginalHistoricalUngatedPhysicalValidN434
                d L band slot δ Y e m mp n then W (mp,n) else 0 := by
          apply Finset.sum_congr rfl
          intro mp hmp
          exact (Finset.sum_filter (s:=J)
            (p:=parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp)
            (f:=fun n => W (mp,n)))
      _ = ∑q∈M.product J,
            if parityOriginalHistoricalUngatedPhysicalValidN434
                d L band slot δ Y e m q.1 q.2 then W q else 0 :=
          (Finset.sum_product M J (fun q : ℕ×ℕ =>
            if parityOriginalHistoricalUngatedPhysicalValidN434
                d L band slot δ Y e m q.1 q.2 then W q else 0)).symm
      _ = _ := (Finset.sum_filter (s:=M.product J)
          (p:=fun q : ℕ×ℕ=>parityOriginalHistoricalUngatedPhysicalValidN434
             d L band slot δ Y e m q.1 q.2) (f:=W)).symm
  calc
    _ = ∑mp∈M,∑n∈J.filter
        (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),W (mp,n) := by
      apply Finset.sum_congr rfl
      intro mp hmp
      rw [hPerMp mp hmp,Finset.mul_sum]
    _ = ∑q∈S,W q := hProduct
    _ = ∑Z∈S.image g,
        ∑q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y e m K J k Z,W q :=
      parity_original_historical_ungated_full_odd_k_Z_image_reindex434
        d L band slot δ Y e m K J k he W
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      unfold parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [W,parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFourierOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- The LITERAL corrected original h=-2 Parity(4.13)--(4.15)
UNGATED B509 natural two-endpoint physical 3D Fourier kernel
at one actual (e,m,k,Z,chi), with real Euclidean Schwartz
eta_e,L(e/E)*eta_n(n/V) and physical source B509 H0,
original alpha_m, conjugate alpha_mp and chi(mp).
This is a source-defined Fourier integrand: equality to Parity's
literal B633 two-prime-slot sum is a SEPARATE theorem, not an
unchecked reinterpretation of the gated earlier kernel. -/
def parityOriginalHistoricalUngatedActual3DFourierCell434
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
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (ζ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  parityOriginal3DPhysicalFiniteTwistedSource434
    (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z)
    (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
      d L band slot δ ξ rho α signed Y e m k χ)
    (parityOriginalHistoricalPhysicalFourierEventTriple434
      U (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
    (parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V (Z:ℝ) k buf a b hSmooth hSupport) ζ

/-- WHOLE CORRECTED Parity(4.15) full odd-e, nonzero signed k,
real character-outer B509 natural a_v(u/e) SOURCE as ONE exact
sum of Euclidean R³ Fourier integrals, indexed by genuine
physically attained binary Z (not a synthetic unrestricted Z
range). The original 2|k| character coefficient cchi, conjugate
chi(m), original b629 fine alpha, H0 signed and 2π phases are
preserved. The SOURCE e may contain original P primes. -/
def parityOriginalHistoricalUngatedFullOdd3DFourierOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          (parityShiftTwoMaskCoefficient434 k.natAbs χ *
            star (χ (m : ZMod (2*k.natAbs)))) *
          (∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k).image
                (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
            ∫ζ : EuclideanSpace ℝ (Fin 3),
              parityOriginalHistoricalUngatedActual3DFourierCell434
                d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) χ
                buf a b hSmooth hSupport ζ)

/-- This is the exact CORRECTED real manuscript Parity (4.10)--(4.15)
post-Cauchy full odd-e signed source equality to 3D Fourier.
The proof uses only the newly PROVED ungated natural endpoint
logarithmic h=-2 pullback and exact finite m'→z→n→Z image
reindex, not the old artificially P-free-e-gated Fourier branch.
All true η_eη_n source weights, original B509 H0 and skipped-Q
coefficient signs, actual 2π Fourier phases, odd-e window, and
real signed k and χ are retained. There is no assumed Parity4.17
saving and no illegitimate signed-subset comparison. -/
theorem parity_original_historical_ungated_full_odd_character_outer_eq_3d_fourier434
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
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    parityOriginalHistoricalUngatedFullOddCharacterOuter434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V)
      α signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) =
    parityOriginalHistoricalUngatedFullOdd3DFourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport := by
  unfold parityOriginalHistoricalUngatedFullOddCharacterOuter434
    parityOriginalHistoricalUngatedFullOdd3DFourierOuter434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  apply Finset.sum_congr rfl
  intro m hm
  have hmDyad := hDyad m hm
  have hAllDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ hχ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  have hBridge := parity_original_historical_ungated_character_k_z_eq_binary_events434
    d L E V hL band slot δ ξ rho α signed Y e m K J k χ heOdd
  have hFour (Z : ℕ) (hZ : Z∈S.image g) :
      parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
      ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalUngatedActual3DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hSmooth hSupport ζ := by
    obtain ⟨q,hq,hScale⟩ := Finset.mem_image.mp hZ
    have hqData := Finset.mem_filter.mp hq
    have hp := Finset.mem_product.mp hqData.1
    have hmpData := Finset.mem_filter.mp hp.1
    have hneq : m≠q.1 := (Finset.mem_erase.mp hmpData.1).1.symm
    have hPhysical := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 heOdd hneq hqData.2
    dsimp only at hPhysical
    have hPos : 0<parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 :=
      hPhysical.2.1
    have hZOwn := (parity_original_historical_actual_z_in_own_dyad434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hPos).1
    have hZPos : 0<Z := by
      change 0<parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q at hZOwn
      have hScale' : parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q=Z := hScale
      rw [hScale'] at hZOwn
      exact hZOwn
    have hh := parity_original_historical_ungated_actual_k_z_physical_fourier434
      d L hL band slot δ ξ rho α signed Y e m K J k Z χ heOdd
      U E V hU hE hV hmDyad.1 hmDyad.2.le hAllDyad
      buf a b hSmooth hSupport hOne hZPos
    exact hh
  rw [hBridge]
  congr 1
  apply Finset.sum_congr rfl
  intro Z hZ
  exact hFour Z hZ
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedActualKZB633Fourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The genuine corrected original h=-2 r20 B509 natural a_v(u/e)
**LITERAL B633 physical two-prime-slot** Fourier integrand on one
actual e,m,k,Z,χ. Source e may carry original P-group primes;
α, χ(m'), H0, W1, signed epsilon, 2π shifts and U,U,Z
normalization are unchanged. No spectral estimate is hidden here. -/
def parityOriginalHistoricalUngatedActualB6333DFourierCell434
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
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
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


/-- TRUE ORIGINAL Parity(4.16) Fourier integrand equality on
corrected ungated physical k/Z B509 source, χ(m) outside,
original 2π normalization and literal two-prime-slot pair sum,
including P-bad e. No Parity(4.17) saving. -/
theorem parity_original_historical_ungated_actual_k_z_3d_fourier_eq_B633434
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
    let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport
    let scale := parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
      parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
      parityOriginalHistoricalFourierScalePhase434 (Z:ℝ) (ζ 2)
    star (chi (m : ZMod (2*k.natAbs))) *
      parityOriginalHistoricalUngatedActual3DFourierCell434
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
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho alpha signed Y e m k chi
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport
  let scale := parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
      parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
      parityOriginalHistoricalFourierScalePhase434 (Z:ℝ) (ζ 2)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
  have hZreal : 0<(Z:ℝ) := by exact_mod_cast hZ
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
    have hPhys : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 := hMem.2.1
    obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hPhys
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
  have hB633 := parity_original_historical_ungated_actual_k_z_full_finite_eq_B633434
    d L (by linarith : (1:ℝ)≤L) band slot δ ξ K J alpha Y e m he k Z chi
    rho (2*Real.pi*(ζ 0)) (2*Real.pi*(ζ 1)) (2*Real.pi*(ζ 2)) signed
  dsimp only at hB633
  change (∑q∈S,
    star (chi (m:ZMod (2*k.natAbs))) *
    imaginaryPower m (2*Real.pi*(ζ 0)) *
    imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
    imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
       (2*Real.pi*(ζ 2)) * W q) = _ at hB633
  unfold parityOriginalHistoricalUngatedActual3DFourierCell434
    parityOriginal3DPhysicalFiniteTwistedSource434
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

/-! ## OriginalHistoricalUngatedB633FourierIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- **LITERAL original Parity(4.16) non-truncated R³ Fourier equality**
for one true corrected UNGATED physical h=-2 B509 e,m,k,Z,χ
source. Its conjugate chi(m) sits at the same exact position
as Parity(2.6), source chi(m') inside the real finite B633 cores,
and the original eta_e,L(e/E)eta_n(n/V) physical source equals
the B633 integrand with correct 2π U/U/Z phase and original
H0/W1/epsilon/alpha. e may have any original P-group factors.
This is a source identity, NOT a Parity (4.17) saving. -/
theorem parity_original_historical_ungated_true_k_Z_chi_B633_fourier_integral434
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
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hZ : 0<Z) :
    star (χ (m : ZMod (2*k.natAbs))) *
      parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalUngatedActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ := by
  have hSource := parity_original_historical_ungated_actual_k_z_physical_fourier434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hSmooth hSupport hOne hZ
  rw [hSource]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ζ
  have hPoint := parity_original_historical_ungated_actual_k_z_3d_fourier_eq_B633434
    d L U E V hL band slot δ ξ K J α Y e m he k Z χ rho signed
    hU hZ buf a b hSmooth hSupport ζ
  exact hPoint
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedB633FourierOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- THE **CORRECTED** original Parity(4.10)--(4.16) NATURAL UNGATED
full odd-e FULL physical B633-PAIR Fourier outer, over all e,m,
nonzero signed k, original χ mod 2|k|, and ONLY genuine attained
binary Z. Here the Fourier integrand is the LITERAL Parity(4.16)
B633 two-prime-slot physical pair at z=m'*(mn-2)/e and z+2k,
with the original skipped-Q B509 H0, W1, signed ε=1/E and b629
fine α and real 2π/U/U/Z phases.
Unlike the historical previous gated object, this new source
includes e divisible by primes of the original P groups. -/
def parityOriginalHistoricalUngatedFullOddB633FourierOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k).image
                (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
            ∫ζ : EuclideanSpace ℝ (Fin 3),
              parityOriginalHistoricalUngatedActualB6333DFourierCell434
                d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) χ
                buf a b hSmooth hSupport ζ)

/-- EXACT end-to-end CORRECTED original Parity(4.10)--(4.16)
full-odd signed natural a_v(u/e) CHARACTER-OUTER = literal
B633 two-prime-slot 3D Fourier outer, at every genuine physical
source binary Z and both signed k branches, INCLUDING P-bad e.
The original conjugate χ(m) is moved only by exact linearity
of the Lebesgue integral; original χ(m') stays inside the B633
finite physical sum. The source total Fourier cutoff, 2π phases,
original ε, W1, and B509 Q/P/H0 are preserved on the nose.
This is an algebraic source result; neither unrestricted 4.17
spectral cancellation nor TypeII/Green64 is assumed. -/
theorem parity_original_historical_ungated_full_odd_character_outer_eq_B633_fourier434
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
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    parityOriginalHistoricalUngatedFullOddCharacterOuter434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V)
      α signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) =
    parityOriginalHistoricalUngatedFullOddB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport := by
  rw [parity_original_historical_ungated_full_odd_character_outer_eq_3d_fourier434
    d L U E V hL band slot δ ξ rho K α signed Y
    hU hE hV hDyad buf a b hSmooth hSupport hOne]
  unfold parityOriginalHistoricalUngatedFullOdd3DFourierOuter434
    parityOriginalHistoricalUngatedFullOddB633FourierOuter434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  apply Finset.sum_congr rfl
  intro m hm
  have hmD := hDyad m hm
  have hAllDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ hχ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  let c : ℂ := parityShiftTwoMaskCoefficient434 k.natAbs χ
  let bχ : ℂ := star (χ (m : ZMod (2*k.natAbs)))
  let aZ : ℕ → ℂ := fun Z =>
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalUngatedActual3DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ
  let fZ : ℕ → ℂ := fun Z =>
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalUngatedActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ
  have hEach (Z : ℕ) (hZ : Z∈S.image g) : bχ * aZ Z = fZ Z := by
    obtain ⟨q,hq,hQZ⟩ := Finset.mem_image.mp hZ
    obtain ⟨hProd,hValid⟩ := Finset.mem_filter.mp hq
    have hMpM := Finset.mem_filter.mp (Finset.mem_product.mp hProd).1
    have hNe : m≠q.1 := (Finset.mem_erase.mp hMpM.1).1.symm
    have hPos := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 heOdd hNe hValid
    dsimp only at hPos
    have hzPos : 0<parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 :=
      hPos.2.1
    have hZOwn := (parity_original_historical_actual_z_in_own_dyad434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hzPos).1
    have hZPos : 0<Z := by
      change 0<parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q at hZOwn
      have hScale : parityOriginalHistoricalPhysicalZScaleOfEvent434 e m q=Z := hQZ
      rw [hScale] at hZOwn
      exact hZOwn
    dsimp only [bχ,aZ,fZ]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact parity_original_historical_ungated_actual_k_z_3d_fourier_eq_B633434
      d L U E V hL band slot δ ξ K J α Y e m heOdd k Z χ rho signed
      hU hZPos buf a b hSmooth hSupport ζ
  have hSum : (∑Z∈S.image g,bχ*aZ Z)=(∑Z∈S.image g,fZ Z) :=
    Finset.sum_congr rfl hEach
  change (c*bχ)*(∑Z∈S.image g,aZ Z) = c*(∑Z∈S.image g,fZ Z)
  calc
    _ = c * (∑Z∈S.image g,bχ*aZ Z) := by
      rw [←Finset.mul_sum]
      ring
    _ = _ := by rw [hSum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullTypeIIFourierJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- END TO END **SOURCE-CORRECTED** Parity(4.10)-(4.16) signed
TypeII Cauchy precursor. The ORIGINAL allocated-Q e source
Cauchy norm² is ≤ original a_e beta_n L2 mass times the PROVED
full-odd ungated positive diagonal 2 Acoef² exp L L^(2CW1+344)
plus the norm of ONE literal real physically supported B633 two-
prime-slot 3D Fourier outer. This genuine natural a_v(u/e) kernel
includes e with original P-group prime factors after Cauchy;
no inequality between complex signed subset and full 4.17 sum.
Original r0=20 h=-2 sigma=0, ε=1/E, W1, B509 H0, fine α,
Dirichlet cχ and 2π Fourier U/U/Z all verified in native Lean.
The unrestricted low-frequency Parity4.17 saving and TypeII(4.2)
remain OPEN. -/
theorem parity_eventually_original_ungated_full_odd_Cauchy_diag_B633_fourier434
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
          ‖parityOriginalHistoricalUngatedFullOddB633FourierOuter434
            (sourceOriginalLiteralDepth 20 L) L U E V hLw
            band slot δ ξ rho K alpha signed ⌊2*Real.exp L⌋₊
            buf (-Real.log A) (Real.log A) hSmooth hSupport‖) := by
  filter_upwards [parity_eventually_original_ungated_full_odd_Cauchy_diag_offdiag434,
    parity_eventually_original_ungated_full_odd_fine_offdiag_eq_character_outer434
      S beta gamma K0 hS hbeta hgamma] with L hC hMask
  refine ⟨hC.1,hC.2.1,?_⟩
  intro hLw band slot δ ξ U E V rho K J betaSeq prime signed lFine uFine Acoef
    hU hV hScale hDyad hNRange hl hFineLow
  dsimp only
  intro hAcoef hAlpha
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  have hLp : 0<L := by linarith [hC.2.1]
  have hE : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hOriginal := hC.2.2 hLw band slot δ ξ E V rho K J alpha betaSeq
    signed Acoef hE hV hNRange hAcoef hAlpha
  have hMasked := hMask.2 hLw band slot δ ξ U E V rho K
    (parityOriginalHistoricalFullNEnvelope434 V) prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  have hB633 := parity_original_historical_ungated_full_odd_character_outer_eq_B633_fourier434
    (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
    K alpha signed ⌊2*Real.exp L⌋₊ hU hE hV hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport hOne
  dsimp only at hOriginal
  rw [hMasked,hB633] at hOriginal
  exact hOriginal
end Green64Analytic.Parity

end

end

