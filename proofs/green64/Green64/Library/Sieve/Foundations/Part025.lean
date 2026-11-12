module

public import Green64.Library.Sieve.Foundations.Part024
public import Mathlib.Data.Nat.PrimeFin
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part022
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Sieve.Foundations.Part020

@[expose] public section

/-!
# Sieve / Foundations / Part025

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalPhysicalENZImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Complete real ORIGINAL SOURCE selected-e,shared-n carrier at
FIXED actual h=-2 cofactor pair (m,m') and nonzero k, with BOTH
physical B509/Q/P source gate witnesses. The selected Eset and J
are the literal externally supplied original finite index supports,
not an artificial image over all positive integers. -/
def parityOriginalHistoricalPhysicalENKCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp : ℕ) (Eset J : Finset ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  (Eset.product J).filter (fun en =>
    Odd en.1 ∧
    parityOriginalHistoricalOffdiagK434 en.1 m mp=k ∧
    parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y en.1 m mp en.2)

/-- Native original canonical source map (selected e,n) ↦ z=m'v
on the same actual signed h=-2 Q/P physical source carrier. -/
def parityOriginalHistoricalPhysicalENZMap434
    (m mp : ℕ) (en : ℕ×ℕ) : ℕ :=
  parityOriginalHistoricalCanonicalZ434 en.1 m mp en.2

/-- THE SAME original Parity (4.13) physical source pair cannot be
counted twice by changing the selected e or shared n while fixing
m,m',k,z. On the actual source supported selected-e×J carrier, the
canonical map (e,n)→z is injective by the two determinant equations.
This discharges the full multiplicity concern when later commuting
original e,n sums with the genuine (4.17) z-sum; it does NOT prove
surjectivity onto every full B633 divisor-pair source core term. -/
theorem parity_original_historical_true_ENZ_map_injOn434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp : ℕ) (Eset J : Finset ℕ) (k : ℤ)
    (hneq : m≠mp) (hk : k≠0) :
    Set.InjOn (parityOriginalHistoricalPhysicalENZMap434 m mp)
      (parityOriginalHistoricalPhysicalENKCarrier434
        d L band slot δ Y m mp Eset J k : Set (ℕ×ℕ)) := by
  intro en hen en' hen' heq
  obtain ⟨e,n⟩ := en
  obtain ⟨e',n'⟩ := en'
  have hData := (Finset.mem_filter.mp hen).2
  have hData' := (Finset.mem_filter.mp hen').2
  obtain ⟨he,hK,hV⟩ := hData
  obtain ⟨he',hK',hV'⟩ := hData'
  have hZ : parityOriginalHistoricalCanonicalZ434 e m mp n =
      parityOriginalHistoricalCanonicalZ434 e' m mp n' := heq
  have hp := parity_original_historical_true_source_e_n_to_z_injective434
    d L band slot δ Y m mp n n' e e' k
    (parityOriginalHistoricalCanonicalZ434 e m mp n)
    he he' hneq hV hV' hK hK' hk rfl hZ.symm
  exact Prod.ext hp.1 hp.2

/-- SOURCE-TO-TARGET z IMAGE reindex with NO hidden coefficient
multiplicity: for arbitrary complex physical z-term F (e.g. the
actual literal B633 two-core individual summand), summing over the
original distinct selected e and n equals the sum over DISTINCT
canonical positive z in their true supported image. This is a
SIGNED exact equality, not an ℓ1 domination of a larger sum. -/
theorem parity_original_historical_true_EN_sum_eq_supported_z_image434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp : ℕ) (Eset J : Finset ℕ) (k : ℤ)
    (hneq : m≠mp) (hk : k≠0)
    (F : ℕ → ℂ) :
    (∑en∈parityOriginalHistoricalPhysicalENKCarrier434
       d L band slot δ Y m mp Eset J k,
       F (parityOriginalHistoricalPhysicalENZMap434 m mp en)) =
    ∑z∈(parityOriginalHistoricalPhysicalENKCarrier434
       d L band slot δ Y m mp Eset J k).image
         (parityOriginalHistoricalPhysicalENZMap434 m mp),F z := by
  exact (Finset.sum_image
    (parity_original_historical_true_ENZ_map_injOn434
       d L band slot δ Y m mp Eset J k hneq hk)).symm

/-- Every image z of the real original selected-e×J physical source
has an actual positive z AND z+2k and therefore lies in the TRUE
shifted domain of Parity (4.17). The image is not replaced by the
whole unsigned z interval or by a positive majorant. -/
theorem parity_original_historical_true_ENZ_image_positive_shift434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp : ℕ) (Eset J : Finset ℕ) (k : ℤ)
    (hneq : m≠mp) (z : ℕ)
    (hz : z∈(parityOriginalHistoricalPhysicalENKCarrier434
       d L band slot δ Y m mp Eset J k).image
         (parityOriginalHistoricalPhysicalENZMap434 m mp)) :
    0<z ∧ 0<(z:ℤ)+2*k := by
  obtain ⟨⟨e,n⟩,hen,hzeq⟩ := Finset.mem_image.mp hz
  obtain ⟨he,hK,hV⟩ := (Finset.mem_filter.mp hen).2
  have hP := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m mp n he hneq hV
  dsimp only at hP
  change parityOriginalHistoricalCanonicalZ434 e m mp n=z at hzeq
  rw [hK] at hP
  rw [←hzeq]
  exact ⟨hP.2.1,hP.2.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualENSignedZB633 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- GENUINE HISTORICAL ORIGINAL Parity(4.13)-(4.17) integrated
signed source-to-z image bridge, at a fixed (m,m',k,χ) but SUMMING
all original selected Q-e and all shared n in their actual finite
supports. The complete signed source Cauchy cofactor—with all
original u,up,vStar,vpStar physical Q/P/B509 sums and real source
chi(mp)*conjchi(m), m/m'/z separated Fourier characters—is
EXACTLY a complex sum over DISTINCT positive physical z of
LITERAL original Parity(4.16) B633 two-core pair summands.

No #e, #n or Q-factorial auxiliary-source multiplicity appears:
e is unique from m'-m=e*k, n from the physical canonical z.
All complex cancellations are retained as EQUALITY; no unsupported
term is included in its restricted *source image* of z.

This is NOT yet the entire unrestricted Parity(4.17) z-sum over
all (m,m') divisors; proving the source image equals its complete
needed carrier and the smooth dyadic ψ_Z partition remains OPEN. -/
theorem parity_original_historical_actual_EN_full_signed_eq_source_z_B633434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K Eset J : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (Y m mp : ℕ) (k : ℤ) (hneq : m≠mp) (hk : k≠0)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool) :
    let S := parityOriginalHistoricalPhysicalENKCarrier434
      d L band slot δ Y m mp Eset J k
    let f := parityOriginalHistoricalPhysicalENZMap434 m mp
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    (∑en∈S,
      chi (mp : ZMod q)*star (chi (m : ZMod q))*
      imaginaryPower m xi1*imaginaryPower mp xi2*imaginaryPower (f en) xi3*
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y en.1 en.2 m mp) =
    ∑z∈S.image f,
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual q chi F.lo F.hi
        m mp z (((z:ℤ)+2*k).toNat) := by
  dsimp only
  let S := parityOriginalHistoricalPhysicalENKCarrier434
    d L band slot δ Y m mp Eset J k
  let f := parityOriginalHistoricalPhysicalENZMap434 m mp
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  let W : ℕ → ℂ := fun z =>
      parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
        alpha F.residual q chi F.lo F.hi m mp z (((z:ℤ)+2*k).toNat)
  have hPoint (en : ℕ×ℕ) (hen : en∈S) :
      chi (mp : ZMod q)*star (chi (m : ZMod q))*
      imaginaryPower m xi1*imaginaryPower mp xi2*imaginaryPower (f en) xi3*
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y en.1 en.2 m mp = W (f en) := by
    obtain ⟨e,n⟩ := en
    obtain ⟨he,hK,hV⟩ := (Finset.mem_filter.mp hen).2
    have hSource := parity_original_historical_actual_source_coeff_eq_B633_term434
      d L hL band slot δ ξ K alpha q chi Y e m mp n
      he hneq hV rho xi1 xi2 xi3 signed
    dsimp only at hSource
    rw [hK] at hSource
    exact hSource
  calc
    _ = ∑en∈S,W (f en) := by
      apply Finset.sum_congr rfl
      intro en hen
      exact hPoint en hen
    _ = ∑z∈S.image f,W z :=
      parity_original_historical_true_EN_sum_eq_supported_z_image434
        d L band slot δ Y m mp Eset J k hneq hk W
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalReverseSharedN -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual SOURCE W-rough cofactor m is coprime to the genuine
small integer Parity shift k whenever |k|<W< minFac(m). This is the
missing Euclidean cancellation input for reversing Parity (4.16)
from a physical divisor pair back to ONE shared n. -/
theorem parity_original_historical_rough_coprime_small_shift434
    (m : ℕ) (k : ℤ) (W : ℝ)
    (hm : sourceD20Rough W m) (hk : k≠0)
    (hkW : (k.natAbs:ℝ) < W) : m.Coprime k.natAbs := by
  have hkNat : k.natAbs ≠ 0 := by omega
  have hkMinR : (k.natAbs:ℝ) < (m.minFac:ℝ) :=
    lt_trans hkW hm.2
  have hkMin : k.natAbs < m.minFac := by exact_mod_cast hkMinR
  exact Nat.coprime_of_lt_minFac hkNat hkMin

/-- REVERSE ORIGINAL GUARANTEED SOURCE SHARED-N ARITHMETIC.
Assume true h=-2 physical two-core data z=m'v and z+2k=mv',
genuine integral determinant m'-m=e*k, and m coprime to k.
Then there exists an actual SHARED integer n such that BOTH
endpoint source equations hold simultaneously:

   m*n=e*v+2,  m'*n=e*v'+2.

This is not a mere application of the source-to-target implication:
it proves the *reverse* integer divisibility by Euclid's lemma,
including signed negative k, and produces n without assuming it.
Further original n dyad, u<=2exp L, P/Q e selection and smooth
ψ_Z support gates must still be verified before complete (4.17)
source carrier equivalence. -/
theorem parity_original_historical_reverse_shared_n_from_417434
    (m mp e v vp : ℕ) (k : ℤ)
    (hm : 0 < m) (hCop : m.Coprime k.natAbs)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ)) :
    ∃ n : ℕ, m*n=e*v+2 ∧ mp*n=e*vp+2 := by
  have hCross : (m:ℤ)*((vp:ℤ)-(v:ℤ)) =
      k*((e:ℤ)*(v:ℤ)+2) := by
    linear_combination (v:ℤ)*hDet - hShift
  have hDivInt : (m:ℤ) ∣ k*((e:ℤ)*(v:ℤ)+2) :=
    ⟨(vp:ℤ)-(v:ℤ),hCross.symm⟩
  have hCopInt : IsCoprime (m:ℤ) k := by
    rw [Int.isCoprime_iff_gcd_eq_one,Int.gcd_eq_natAbs]
    simpa only [Int.natAbs_natCast] using hCop.gcd_eq_one
  have hDivInt' : (m:ℤ) ∣ (e:ℤ)*(v:ℤ)+2 :=
    hCopInt.dvd_of_dvd_mul_left hDivInt
  have hDiv : m ∣ e*v+2 := by
    exact Int.natCast_dvd_natCast.mp (by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hDivInt')
  obtain ⟨n,hn⟩ := hDiv
  have hN : m*n=e*v+2 := hn.symm
  have hNInt : (m:ℤ)*(n:ℤ)=(e:ℤ)*(v:ℤ)+2 := by exact_mod_cast hN
  have hSecondInt : (m:ℤ)*((mp:ℤ)*(n:ℤ)-((e:ℤ)*(vp:ℤ)+2))=0 := by
    linear_combination (mp:ℤ)*hNInt + (e:ℤ)*hShift + 2*hDet
  have hMNz : (m:ℤ)≠0 := by exact_mod_cast hm.ne'
  have hSecond : (mp:ℤ)*(n:ℤ)=(e:ℤ)*(vp:ℤ)+2 := by
    have hh := (mul_eq_zero.mp hSecondInt).resolve_left hMNz
    exact sub_eq_zero.mp hh
  refine ⟨n,hN,?_⟩
  exact_mod_cast hSecond
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalReverse417Divisors -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- REVERSE ARITHMETIC OF THE ACTUAL ORIGINAL Parity(4.17)
TWO-PRIME-SLOT DIVISOR PAIR. Given positive z,z'=z+2k and
cofactors m'|ordinary_P(z), m|ordinary_P(z') and the original
nonzero-det e from m'-m=e*k, with gcd(m,k)=1, the genuine
physical v=z/m', v'=z'/m are positive INTEGERS and the SAME
physical n exists at both shifted source endpoints:

  z=m'v, z'=mv',  mn=e v+2, m'n=e v'+2.

No hypothetical source physical n or enlarged m/m' or prime-slot
support is assumed. This is the genuine *converse arithmetic*
missing from the source-to-B633 carrier inclusion proof. To get
complete equality with the SOURCE finite sum one still must
recover selected e/n dyad, P/Q gates, and the allowed smooth
z-window, plus character orthogonality for the odd e residue. -/
theorem parity_original_historical_reverse_417_divisor_pair_to_source_n434
    (P : Finset ℕ) (m mp e z zp : ℕ) (k : ℤ)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp ∣ sourceOriginalOrdinaryPart P z)
    (hDivM : m ∣ sourceOriginalOrdinaryPart P zp) :
    ∃ v vp n : ℕ,
      0 < v ∧ 0 < vp ∧ z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 := by
  have hZFactor := source_original_ordinary_times_P_part P z hz.ne'
  have hZpFactor := source_original_ordinary_times_P_part P zp hzp.ne'
  have hZDiv : mp ∣ z :=
    hDivMp.trans ⟨sourceOriginalPPrimePart P z,hZFactor.symm⟩
  have hZpDiv : m ∣ zp :=
    hDivM.trans ⟨sourceOriginalPPrimePart P zp,hZpFactor.symm⟩
  obtain ⟨v,hZ⟩ := hZDiv
  obtain ⟨vp,hZp⟩ := hZpDiv
  have hv : 0 < v := by
    have hh : 0 < mp*v := by rw [←hZ]; exact hz
    exact Nat.pos_of_mul_pos_left hh
  have hvp : 0 < vp := by
    have hh : 0 < m*vp := by rw [←hZp]; exact hzp
    exact Nat.pos_of_mul_pos_left hh
  have hShiftV : (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
    have hzi : (z:ℤ)=(mp:ℤ)*(v:ℤ) := by exact_mod_cast hZ
    have hzpi : (zp:ℤ)=(m:ℤ)*(vp:ℤ) := by exact_mod_cast hZp
    rw [hzi,hzpi] at hShift
    exact hShift
  obtain ⟨n,hn,hnp⟩ := parity_original_historical_reverse_shared_n_from_417434
    m mp e v vp k hm hCop hDet hShiftV
  exact ⟨v,vp,n,hv,hvp,hZ,hZp,hn,hnp⟩

/-- SOURCE-SPECIFIC reverse (4.17) arithmetic: original m is
W-rough and |k|<W, so coprimality is PROVED, not a hypothesis.
Thus any ordinary-part divisor pair at genuine z and z+2k with
odd source e satisfying m'-m=e*k reconstructs a common integer n.
Neither the true Q/P source gate nor source dyad of n is assumed
as a conclusion; these are the remaining separate analytic masks. -/
theorem parity_original_historical_reverse_417_rough_divisor_pair434
    (P : Finset ℕ) (m mp e z zp : ℕ) (k : ℤ) (W : ℝ)
    (hm : sourceD20Rough W m) (hmp : 0 < mp)
    (hz : 0 < z) (hzp : 0 < zp)
    (hk : k≠0) (hkW : (k.natAbs:ℝ)<W)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hDivMp : mp ∣ sourceOriginalOrdinaryPart P z)
    (hDivM : m ∣ sourceOriginalOrdinaryPart P zp) :
    ∃ v vp n : ℕ,
      0 < v ∧ 0 < vp ∧ z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 := by
  have hc := parity_original_historical_rough_coprime_small_shift434
    m k W hm hk hkW
  have hmPos : 0 < m := by
    have hM : 2 ≤ m := hm.1
    omega
  exact parity_original_historical_reverse_417_divisor_pair_to_source_n434
    P m mp e z zp k hmPos hmp hz hzp hDet hShift hc hDivMp hDivM
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalReverseQPGates -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- REVERSE ORIGINAL Parity (4.17) TWO-ENDPOINT P/Q ALGEBRA.
Starting from a true signed shifted B633 divisor pair at z,z+2k,
if original selected e is P-prime-free and m,k are coprime, recover
an actual SHARED positive integer n and both original physical Q/P
gate equations, with NO lost valuation of repeated P primes:

  u=m*n-2=e*v,  u'=m'*n-2=e*v',
  e*vStar=ordinary_P(u), e*vpStar=ordinary_P(u'),
  v=vStar*Ppart_P(u), v'=vpStar*Ppart_P(u').

The witness vStar is NOT arbitrary: it is literally ordinary_P(v).
This closes the reverse SOURCE Q/P DIVISIBILITY EQUATIONS from the
full B633 divisor core, assuming genuine e P-free as required in
the original source. It does not automatically prove vStar lies in
the actual reserved B509 core-support set, nor that e belongs to
the source selected-e window, n the original dyadic window, or
psi_Z compatibility. Those are separate OPEN support obligations. -/
theorem parity_original_historical_reverse_417_two_endpoint_QP_equations434
    (P : Finset ℕ) (m mp e z zp : ℕ) (k : ℤ)
    (hm : 0 < m) (hmp : 0 < mp) (he : 0 < e)
    (hz : 0 < z) (hzp : 0 < zp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp ∣ sourceOriginalOrdinaryPart P z)
    (hDivM : m ∣ sourceOriginalOrdinaryPart P zp)
    (hEfree : ∀p∈P, ¬p∣e) :
    ∃ n v vp vStar vpStar : ℕ,
      0<n ∧ 0<v ∧ 0<vp ∧ 0<vStar ∧ 0<vpStar ∧
      z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      e*vStar=sourceOriginalOrdinaryPart P (m*n-2) ∧
      e*vpStar=sourceOriginalOrdinaryPart P (mp*n-2) ∧
      v=vStar*sourceOriginalPPrimePart P (m*n-2) ∧
      vp=vpStar*sourceOriginalPPrimePart P (mp*n-2) := by
  obtain ⟨v,vp,n,hv,hvp,hZ,hZp,hN,hNp⟩ :=
    parity_original_historical_reverse_417_divisor_pair_to_source_n434
      P m mp e z zp k hm hmp hz hzp hDet hShift hCop hDivMp hDivM
  let vs := sourceOriginalOrdinaryPart P v
  let vps := sourceOriginalOrdinaryPart P vp
  have hVS : 0<vs := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P v hv.ne')
  have hVPS : 0<vps := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P vp hvp.ne')
  have hnPos : 0<n := by
    have hh : 0 < m*n := by rw [hN]; omega
    exact Nat.pos_of_mul_pos_left hh
  have huEq : m*n-2=e*v := by omega
  have hupEq : mp*n-2=e*vp := by omega
  have hGate : e*vs=sourceOriginalOrdinaryPart P (m*n-2) := by
    rw [huEq]
    exact (parity_original_ordinary_part_mul_prime_free434
      P e v he.ne' hv.ne' hEfree).symm
  have hGatep : e*vps=sourceOriginalOrdinaryPart P (mp*n-2) := by
    rw [hupEq]
    exact (parity_original_ordinary_part_mul_prime_free434
      P e vp he.ne' hvp.ne' hEfree).symm
  have hPP : sourceOriginalPPrimePart P (m*n-2)=
      sourceOriginalPPrimePart P v := by
    rw [huEq]
    exact parity_original_P_prime_part_mul_prime_free434
      P e v he.ne' hv.ne' hEfree
  have hPPp : sourceOriginalPPrimePart P (mp*n-2)=
      sourceOriginalPPrimePart P vp := by
    rw [hupEq]
    exact parity_original_P_prime_part_mul_prime_free434
      P e vp he.ne' hvp.ne' hEfree
  have hV : v=vs*sourceOriginalPPrimePart P (m*n-2) := by
    rw [hPP]
    exact (source_original_ordinary_times_P_part P v hv.ne').symm
  have hVp : vp=vps*sourceOriginalPPrimePart P (mp*n-2) := by
    rw [hPPp]
    exact (source_original_ordinary_times_P_part P vp hvp.ne').symm
  exact ⟨n,v,vp,vs,vps,hnPos,hv,hvp,hVS,hVPS,hZ,hZp,
    hN,hNp,hGate,hGatep,hV,hVp⟩

/-- From genuine original W-rough m and |k|<W, the coprimality
hypothesis in the full reverse Q/P construction is discharged.
Only the *real mathematical* remaining prime-slot/P-free-e and
source window assumptions are retained. -/
theorem parity_original_historical_reverse_417_rough_two_QP_equations434
    (P : Finset ℕ) (m mp e z zp : ℕ) (k : ℤ) (W : ℝ)
    (hm : sourceD20Rough W m) (hmp : 0 < mp) (he : 0 < e)
    (hz : 0 < z) (hzp : 0 < zp)
    (hk : k≠0) (hkW : (k.natAbs:ℝ)<W)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hDivMp : mp ∣ sourceOriginalOrdinaryPart P z)
    (hDivM : m ∣ sourceOriginalOrdinaryPart P zp)
    (hEfree : ∀p∈P, ¬p∣e) :
    ∃ n v vp vs vps : ℕ,
      0<n ∧ 0<v ∧ 0<vp ∧ 0<vs ∧ 0<vps ∧
      z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      e*vs=sourceOriginalOrdinaryPart P (m*n-2) ∧
      e*vps=sourceOriginalOrdinaryPart P (mp*n-2) ∧
      v=vs*sourceOriginalPPrimePart P (m*n-2) ∧
      vp=vps*sourceOriginalPPrimePart P (mp*n-2) := by
  have hc := parity_original_historical_rough_coprime_small_shift434
    m k W hm hk hkW
  have hmPos : 0 < m := by
    have h2 : 2 ≤ m := hm.1
    omega
  exact parity_original_historical_reverse_417_two_endpoint_QP_equations434
    P m mp e z zp k hmPos hmp he hz hzp hDet hShift
    hc hDivMp hDivM hEfree
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSelectedEPFree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Every ACTUALLY SELECTED source e in Parity's original indexed
Q-products is prime-factor-free for the entire genuine P-band
collection. This is a source theorem, not an external hypothesis:
Q and P prime bands are disjoint, and every selected-Q product
may contain repeated prime factors with their true multiplicities.

Unlike the weaker source P-parity=0 statement, this proves each
individual P-prime cannot divide the actual selected e. -/
theorem parity_original_historical_actual_selected_e_P_free434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e : ℕ)
    (he : e∈parityOriginalReservedCartesianESupport434 d L band slot δ) :
    ∀p∈Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L),
      ¬p∣e := by
  unfold parityOriginalReservedCartesianESupport434
    paritySourceQSelectedESupport434 at he
  obtain ⟨a,ha,hProd⟩ := Finset.mem_image.mp he
  intro p hp
  obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
  have hNo := parity_actual_source_selected_e_no_P_divisor434
    d L hL band slot δ a g p hpg
  simpa only [hProd] using hNo

/-- The actual original Parity (4.5) selected-e ACTIVE window does
not alter the disjoint Q/P origin: its every e is P-prime-free,
even if its Fourier coefficient could vanish by cancellation. -/
theorem parity_original_historical_actual_active_e_P_free434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e : ℕ)
    (he : e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ) :
    ∀p∈Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L),
      ¬p∣e := by
  have hSource := (Finset.mem_filter.mp he).1
  exact parity_original_historical_actual_selected_e_P_free434
    d L hL band slot δ e hSource

/-- No abstract e-P-free assumption remains in the reverse
SOURCE Q/P arithmetic, provided the candidate odd e belongs
to the ACTUAL originally selected-Q active e window: the
source Q/P disjointness theorem discharges it automatically.
This is a substantive reverse inclusion component, but it does
not assert that EVERY full Parity(4.17) divisor pair produces an e
in the original selected-Q support. That remaining support/filter
condition must still be controlled before deriving cancellation. -/
theorem parity_original_historical_reverse_417_actual_selected_e_QP434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (m mp e z zp : ℕ) (k : ℤ) (W : ℝ)
    (hm : sourceD20Rough W m) (hmp : 0 < mp) (he : 0 < e)
    (heSupport : e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ)
    (hz : 0 < z) (hzp : 0 < zp)
    (hk : k≠0) (hkW : (k.natAbs:ℝ)<W)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hDivMp : mp ∣ sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m ∣ sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    ∃ n v vp vs vps : ℕ,
      0<n ∧ 0<v ∧ 0<vp ∧ 0<vs ∧ 0<vps ∧
      z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      e*vs=sourceOriginalOrdinaryPart P (m*n-2) ∧
      e*vps=sourceOriginalOrdinaryPart P (mp*n-2) ∧
      v=vs*sourceOriginalPPrimePart P (m*n-2) ∧
      vp=vps*sourceOriginalPPrimePart P (mp*n-2) := by
  dsimp only
  have hNoP := parity_original_historical_actual_active_e_P_free434
    d L E hL band slot δ e heSupport
  exact parity_original_historical_reverse_417_rough_two_QP_equations434
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
    m mp e z zp k W hm hmp he hz hzp hk hkW hDet hShift
    hDivMp hDivM hNoP
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPositiveCarrierEnlarge -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- ORIGINAL Parity (4.10) positive Cauchy square on ANY finite
superset Eenv×Nenv of the real original source selected-e×J
carrier. This extension is made ONLY for the positive square,
NEVER for its signed complex offdiagonal after Gram expansion. -/
def parityOriginalHistoricalWeightedExtendedCauchySquare434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑e∈Eenv,∑n∈Nenv,w e n *
    ‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2

/-- Exact mathematically VALID enlargement of the original
smoothing-weighted positive Cauchy square to arbitrary finite
e,n supercarriers: if w≥0 on the large domain, the Cauchy square
on the true source-support is ≤ the large-domain square.
This keeps complex cancellation under each inner m sum, and does
NOT assert inequality between different signed OFFDIAGONAL sums. -/
theorem parity_original_historical_positive_square_carrier_enlarge434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hEsub : parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆ Eenv)
    (hNsub : J ⊆ Nenv)
    (hw : ∀e∈Eenv, ∀n∈Nenv,0≤w e n) :
    parityOriginalHistoricalWeightedActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y w ≤
    parityOriginalHistoricalWeightedExtendedCauchySquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot δ
  let H : ℕ×ℕ → ℝ := fun en => w en.1 en.2 *
      ‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y en.1 en.2 m‖^2
  have hProd : Q.product J ⊆ Eenv.product Nenv := by
    intro p hp
    obtain ⟨hqe,hqn⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hEsub hqe,hNsub hqn⟩
  have hNonneg : ∀p∈Eenv.product Nenv, 0≤H p := by
    intro p hp
    obtain ⟨he,hn⟩ := Finset.mem_product.mp hp
    exact mul_nonneg (hw p.1 he p.2 hn) (sq_nonneg _)
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hProd
    (fun en hen hnot => hNonneg en hen)
  unfold parityOriginalHistoricalWeightedActiveCauchySquare434
    parityOriginalHistoricalWeightedExtendedCauchySquare434
  change (∑e∈Q,∑n∈J,H (e,n)) ≤ ∑e∈Eenv,∑n∈Nenv,H (e,n)
  rw [←Finset.sum_product, ←Finset.sum_product]
  exact hSum

/-- THE original SOURCE (4.10) Cauchy inequality remains correct
when the actual selected-e×n carrier is enlarged BEFORE Gram.
No illegitimate bound on a restricted complex (4.17) correlation
is used. This is the exact correct entrypoint to replace sparse
e-selected Q support by a full odd integer e interval, and n
dyads by their smooth support, then rederive the signed offdiag. -/
theorem parity_original_historical_signed_weighted_extended_Cauchy434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J Eenv Nenv : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hMajor : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ, ∀n∈J,1≤w e n)
    (hEsub : parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆ Eenv)
    (hNsub : J ⊆ Nenv)
    (hw : ∀e∈Eenv, ∀n∈Nenv,0≤w e n) :
    ‖parityOriginalHistoricalCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∑n∈J,
      ‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
    parityOriginalHistoricalWeightedExtendedCauchySquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  have hCauchy := parity_original_historical_signed_weighted_active_Cauchy434
    d L E band slot δ ξ rho K J α β signed Y w hMajor
  have hSub := parity_original_historical_positive_square_carrier_enlarge434
    d L E band slot δ ξ rho K J Eenv Nenv α signed Y w
    hEsub hNsub hw
  have hCoef : 0 ≤ (∑e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∑n∈J,
      ‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) := by
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact hCauchy.trans (mul_le_mul_of_nonneg_left hSub hCoef)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddEnvelope -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The first TRUE fully enlarged e domain for original Parity (4.10)
positive Cauchy: ALL odd positive integer e≤floor(2E). The
original sparse selected-Q product support is only a subset.
The factor 2 covers the compact support of genuine η_e(e/E),
which vanishes for e/E≥2, not a postulated e frequency gate. -/
def parityOriginalHistoricalFullOddEEnvelope434 (E : ℝ) : Finset ℕ :=
  (Finset.range (⌊2*E⌋₊+1)).filter Odd

/-- The TRUE full finite n-range containing the original dyadic
[V,2V] and the entire actual fixed eta_n support n/V<3. -/
def parityOriginalHistoricalFullNEnvelope434 (V : ℝ) : Finset ℕ :=
  Finset.range (⌊3*V⌋₊+1)

/-- The original sparse moving-Q selected-e support in the
historical e-window lies INSIDE the full odd e≤floor(2E)
carrier, provided every original selected e is actually odd.
This lemma makes NO claim that signed offdiagonal correlations
are bounded by the unrestricted signed full correlation. -/
theorem parity_original_historical_active_selected_e_sub_full_odd434
    (d : ℕ) (L E : ℝ) (hE : 0≤E)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (hOdd : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,Odd e) :
    parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆
    parityOriginalHistoricalFullOddEEnvelope434 E := by
  intro e he
  have hWindow := (Finset.mem_filter.mp he).2
  have hEe : (e:ℝ)≤2*E := by linarith [hWindow.2]
  have hFloor : e≤⌊2*E⌋₊ := Nat.le_floor hEe
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hFloor),hOdd e he⟩

/-- The genuine original source n-dyad [V,2V] is a subset of
ALL nonnegative integers n≤floor(3V). The expanded n endpoint
has exactly the compact support height of the TRUE eta_n, not a
hypothetical unbounded n summation. -/
theorem parity_original_historical_actual_n_dyad_sub_full_envelope434
    (V : ℝ) (hV : 0≤V) (J : Finset ℕ)
    (hnRange : ∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) :
    J ⊆ parityOriginalHistoricalFullNEnvelope434 V := by
  intro n hn
  have hnTop : (n:ℝ)≤3*V := by linarith [(hnRange n hn).2]
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hnTop))

/-- MATHEMATICALLY CORRECT ORIGINAL Parity (4.10) smoothing and
PRE-GRAM full-interval enlargement. The original Cauchy norm,
on the sparse selected-Q e source and true dyadic n source,
obeys the positive square bound over ALL odd e≤2E and ALL
n≤3V. The weight is the ACTUAL constructed C∞
eta_e,L(e/E)*eta_n(n/V), nonnegative on the entire enlarged
rectangle, ≥1 on the original true source rectangle and with
all-order native polynomial derivative bounds already proved.

This is the first SOURCE bridge making original selected-Q e
restrictions unnecessary on the square side: the extension is
justified by positivity BEFORE Gram and before insertion of
characters; never compare two nested signed complex sums.
The new full odd-e/n square can legitimately be opened and
Fourier-reindexed, retaining all physical u/u'/vStar gates.
This is NOT yet the final Parity Type II (4.2) estimate. -/
theorem parity_original_historical_actual_full_odd_envelope_Cauchy434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hOdd : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,Odd e)
    (hnRange : ∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∑n∈J,
      ‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
    parityOriginalHistoricalWeightedExtendedCauchySquare434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V)
      α signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) := by
  have hEsub := parity_original_historical_active_selected_e_sub_full_odd434
    d L E hE.le band slot δ hOdd
  have hNsub := parity_original_historical_actual_n_dyad_sub_full_envelope434
    V hV.le J hnRange
  apply parity_original_historical_signed_weighted_extended_Cauchy434
    d L E band slot δ ξ rho K J
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V)
    α β signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hL)
  · intro e he n hn
    exact parity_original_historical_dyadic_eta_weight_source_ge_one434
      L E V hL hE hV e n (Finset.mem_filter.mp he).2
      (hnRange n hn).1 (hnRange n hn).2
  · exact hEsub
  · exact hNsub
  · intro e he n hn
    exact (parity_original_historical_dyadic_eta_weight_polylog434
      L E V hL e n).1
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddGram -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

def parityOriginalHistoricalWeightedExtendedDiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e∈Eenv,
    ∑ n∈Nenv,w e n *
      ∑ m∈K,‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- Exact ORIGINAL smooth-weighted complex signed Parity (4.13)
OFFDIAGONAL, with η_e(e/E)η_n(n/V) outside the genuine m,m' pair.
Critically it is NOT assumed nonnegative, bounded by the raw
unweighted offdiagonal, or equal to the ungated physical source. -/
def parityOriginalHistoricalWeightedExtendedOffdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e∈Eenv,
    ∑ n∈Nenv,((w e n:ℝ):ℂ) *
      (∑ m∈K,∑ mp∈K.erase m,
        (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp))

/-- TRUE original Parity(4.10) weighted Gram identity. The smooth
majorant weights are introduced on the positive Cauchy square BEFORE
splitting into m=m' diagonal and m≠m' complex offdiagonal.
Every source h=-2 signed H0 coefficient is kept exact, even for
weights >1. This prevents invalid signed-offdiagonal monotonicity. -/
theorem parity_original_historical_weighted_extended_square_diag_offdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    ((parityOriginalHistoricalWeightedExtendedCauchySquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w:ℝ):ℂ) =
    ((parityOriginalHistoricalWeightedExtendedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w:ℝ):ℂ) +
      parityOriginalHistoricalWeightedExtendedOffdiag434
        d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := Eenv
  let F : ℕ → ℕ → ℕ → ℂ := fun e n m =>
    α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  have hOne (e n : ℕ) :
      ((‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
        ∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp) :=
    parity_original_historical_actual_e_n_square_diag_offdiag434
      d L band slot δ ξ rho K α signed Y e n
  unfold parityOriginalHistoricalWeightedExtendedCauchySquare434
    parityOriginalHistoricalWeightedExtendedDiagonal434
    parityOriginalHistoricalWeightedExtendedOffdiag434
  change ((∑e∈Q,∑n∈Nenv,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
    ((∑e∈Q,∑n∈Nenv,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
      (∑e∈Q,∑n∈Nenv,((w e n:ℝ):ℂ)*
        (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp)))
  have hCastL : ((∑e∈Q,∑n∈Nenv,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ∑e∈Q,∑n∈Nenv,((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  have hCastD : ((∑e∈Q,∑n∈Nenv,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) =
      ∑e∈Q,∑n∈Nenv,((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  rw [hCastL,hCastD]
  calc
    _ = ∑e∈Q,∑n∈Nenv,
      (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
        ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      calc
        ((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
          ((w e n:ℝ):ℂ)*((‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by push_cast; rfl
        _ = ((w e n:ℝ):ℂ) *
          (((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
            (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
              rw [hOne e n]
        _ = (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
          ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
            push_cast
            ring
    _ = _ := by simp_rw [Finset.sum_add_distrib]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddCauchyGramJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- END-TO-END MATHEMATICALLY VALID original Parity(4.10)--(4.13)
positive Cauchy and complex Gram on the FULL odd e≤2E,
ALL n≤3V physical SOURCE rectangle.

The ORIGINAL selected-Q e and original n dyad are used only in
the Cauchy coefficient L2 mass. The SECOND quadratic factor is
legitimately enlarged while NONNEGATIVE, *before* the signed
m≠m' offdiagonal is formed. Both real source η_e,L and fixed
η_n are the ACTUALLY constructed native C∞ cutoffs, with proved
positive majorization, compact support and all-order derivative
budgets. The source alpha and complete h=-2 signed H0/Q/P/B509
physical endpoints remain unchanged.

Now the signed offdiagonal is generated from the full finite odd-e
and n carrier, which is a necessary step for achieving the true
converse onto original Parity(4.17) restricted-mask support. This
still does NOT assume an estimate on an arbitrary subset of a
complex signed correlation, and it does NOT prove Type II (4.2). -/
theorem parity_eventually_original_actual_full_odd_Cauchy_Gram434 :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      0<E → 0<V →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      let EFull := parityOriginalHistoricalFullOddEEnvelope434 E
      let NFull := parityOriginalHistoricalFullNEnvelope434 V
      let S := parityOriginalHistoricalWeightedExtendedCauchySquare434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K EFull NFull α signed Y w
      let D := parityOriginalHistoricalWeightedExtendedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K EFull NFull α signed Y w
      let OD := parityOriginalHistoricalWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K EFull NFull α signed Y w
      (‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed Y‖^2 ≤
       (∑e∈parityOriginalHistoricalCauchyActiveESupport434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2)*S)
       ∧ (((S:ℝ):ℂ)=((D:ℝ):ℂ)+OD) := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434,
    eventually_ge_atTop (8:ℝ)] with L hOdd hL8
  refine ⟨hL8,?_⟩
  intro hLw band slot δ ξ E V rho K J α β signed Y hE hV hnRange
  dsimp only
  have hOddActive : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
       (sourceOriginalLiteralDepth 20 L) L E band slot δ,Odd e := by
    intro e he
    exact (hOdd.2 band slot δ e (Finset.mem_filter.mp he).1).1
  have hCauchy := parity_original_historical_actual_full_odd_envelope_Cauchy434
    (sourceOriginalLiteralDepth 20 L) L E V hLw hE hV band slot δ ξ
    rho K J α β signed Y hOddActive hnRange
  have hGram := parity_original_historical_weighted_extended_square_diag_offdiag434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V)
    α signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
  exact ⟨hCauchy,hGram⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalExtendedDiagonalFinite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- TRUE original h=-2 positive Cauchy diagonal over ARBITRARY
integer finite e and n supports. After legitimate pre-Gram e/n
carrier enlargement the old selected-Q e support does not appear. -/
def parityOriginalHistoricalExtendedUnweightedDiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑ e∈Eenv,∑n∈Nenv,∑m∈K,
    ‖α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2

/-- Unconditional original positive diagonal physical divisor
bound over ANY finite e,n rectangles: the original source e|u,
u=mn-2 and τ(u)τ(u+2) count retain the exact full Q/P/B509
H0, with no extra cardinality of e support. -/
theorem parity_original_historical_extended_unweighted_diagonal_finite_tau_moment434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C)
    (hα : ∀m∈K,‖α m‖≤A)
    (hPhysical : ∀ e u : ℕ, 0<u → 0<e →
      ‖parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ)) :
    parityOriginalHistoricalExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y ≤
      A^2*C^2*(∑u∈Finset.Ioc 0 Y,
        (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := by
  let Q := Eenv
  let U := Finset.Ioc 0 Y
  let w : ℕ → ℝ := fun u => A^2*C^2*(u.divisors.card:ℝ)^2
  have hw (u : ℕ) (hu : u∈U) : 0≤w u := by
    dsimp [w]
    positivity
  have hEach (e n m : ℕ) (hm : m∈K) :
      ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2 ≤
      ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0 := by
    rw [norm_mul, mul_pow]
    rw [parity_original_historical_actual_ENM_norm_sq_eq_U434]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have huPos : 0<u :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
    by_cases hdiv : e∣u
    · have hePos : 0<e := by
        rcases hdiv with ⟨t,ht⟩
        by_contra hn
        have he0 : e=0 := Nat.eq_zero_of_not_pos hn
        rw [he0,zero_mul] at ht
        omega
      have hv := hPhysical e u huPos hePos
      have hASq : ‖α m‖^2 ≤ A^2 :=
        (sq_le_sq₀ (norm_nonneg _) hA).mpr (hα m hm)
      have hCSq : ‖parityOriginalHistoricalFixedEU434
          d L band slot δ ξ rho signed e u‖^2 ≤
          (C*(u.divisors.card:ℝ))^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Nat.cast_nonneg _))).mpr hv
      simp only [if_pos hdiv]
      calc
        _ ≤ A^2*(C*(u.divisors.card:ℝ))^2 :=
          mul_le_mul hASq hCSq (sq_nonneg _) (sq_nonneg _)
        _ = w u := by dsimp [w]; ring
    · have hz := parity_original_historical_fixed_e_u_zero_unless_divisor434
        d L band slot δ ξ rho signed e u huPos hdiv
      simp [hz,hdiv]
  unfold parityOriginalHistoricalExtendedUnweightedDiagonal434
  change (∑ e∈Q,∑ n∈Nenv,∑ m∈K,
    ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2) ≤ _
  calc
    _ ≤ ∑e∈Q,∑n∈Nenv,∑m∈K,
      ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0 := by
          apply Finset.sum_le_sum
          intro e he
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro m hm
          exact hEach e n m hm
    _ = ∑u∈U,∑e∈Q,
      ∑z∈parityOriginalShiftTwoPositivePairFibre434 K Nenv u,
        if e∣u then w u else 0 :=
      parity_original_historical_diagonal_ENM_u_reindex434 Q K Nenv Y w
    _ ≤ ∑u∈U,((u.divisors.card:ℝ)*((u+2).divisors.card:ℝ))*w u :=
      parity_original_historical_actual_e_and_pair_divisor_count434 Q K Nenv Y w hw
    _ = A^2*C^2*(∑u∈U,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [w]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddDiagonalPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Original Parity (4.11) TRUE diagonal of the fully enlarged
positive Cauchy square: any 0≤w(e,n)≤C has cost ≤C times the
UNWEIGHTED enlarged diagonal. This is a valid pointwise positive
comparison. Unlike the original signed offdiagonal, the diagonal
has ONLY nonnegative squares even for arbitrary new e and n. -/
theorem parity_original_historical_extended_diagonal_weight_le434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) (C : ℝ)
    (hw : ∀e∈Eenv,∀n∈Nenv,w e n ≤ C) :
    parityOriginalHistoricalWeightedExtendedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w ≤
    C*parityOriginalHistoricalExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  let F : ℕ → ℕ → ℝ := fun e n =>
    ∑m∈K,‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2
  have hF : ∀e n, 0≤F e n := by
    intro e n
    apply Finset.sum_nonneg
    intro m hm
    exact sq_nonneg _
  have hS : (∑e∈Eenv,∑n∈Nenv,w e n*F e n) ≤
      ∑e∈Eenv,∑n∈Nenv,C*F e n := by
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (hw e he n hn) (hF e n)
  unfold parityOriginalHistoricalWeightedExtendedDiagonal434
    parityOriginalHistoricalExtendedUnweightedDiagonal434
  change (∑e∈Eenv,∑n∈Nenv,w e n*F e n) ≤
    C*(∑e∈Eenv,∑n∈Nenv,F e n)
  calc
    _ ≤ ∑e∈Eenv,∑n∈Nenv,C*F e n := hS
    _ = C*(∑e∈Eenv,∑n∈Nenv,F e n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]

/-- UNIVERSAL original Parity (4.11) unconditional physical shifted
τ(u)^3 τ(u+2) bound for arbitrary finite e,n supports after
PRE-GRAM Cauchy expansion. In particular, extending the selected
Q-e support to ALL odd e does NOT introduce any factor E, Q-depth,
or more than the original fixed divisor exponent:

  D_full(e,n) ≤ Acoef² exp L L^(2 C_W1+256).

This is proved from the native ORIGINAL fixed-e,u full H0 bound
and the genuine original shifted eighth divisor moment. It does
not require e to be selected-Q or the original n-dyad. -/
theorem parity_eventually_original_historical_extended_diagonal_polylog434 :
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
      parityOriginalHistoricalExtendedUnweightedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K Eenv Nenv α signed ⌊2*Real.exp L⌋₊ ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_fixed_e_u_physical_norm_le_tau434,
    eventually_ge_atTop ((3:ℝ)^256)] with L hPhys hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hα
  let C : ℝ := L^parityOriginalW1PolylogExponent434
  have hLp : 0<L := by nlinarith [hL]
  have hC : 0≤C := Real.rpow_nonneg hLp.le _
  have hFixed (e u : ℕ) (hu : 0<u) (he : 0<e) :
      ‖parityOriginalHistoricalFixedEU434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ) := by
    simpa only [parityOriginalHistoricalFixedEU434,C] using
      (hPhys.2 band slot δ ξ rho signed u e hu he)
  have hFinite := parity_original_historical_extended_unweighted_diagonal_finite_tau_moment434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K Eenv Nenv α signed ⌊2*Real.exp L⌋₊
    Acoef C hAcoef hC hα hFixed
  have hMoment := parity_original_shift_two_tau_cube_moment_original_x_scale434 L hL
  calc
    _ ≤ Acoef^2*C^2*(∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := hFinite
    _ ≤ Acoef^2*C^2*(Real.exp L*L^256) :=
      mul_le_mul_of_nonneg_left hMoment (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := by
      have hPower : C^2*L^256 = L^(2*parityOriginalW1PolylogExponent434+256) := by
        dsimp [C]
        simp only [pow_two,←Real.rpow_add hLp]
        rw [←Real.rpow_natCast L 256]
        rw [←Real.rpow_add hLp]
        congr 1
        ring
      rw [←hPower]
      ring

/-- The ACTUAL original dyadic SOURCE η_e,L η_n positive full
odd e,n Cauchy diagonal is bounded with the precise fixed exponent
2 C_W1+344 after the legitimate sparse-support enlargement:

  D_full_odd(e,n;eta_e eta_n) ≤ 2 Acoef² exp L L^(2CW1+344).

This remains valid for ALL e∈odd≤2E and ALL n≤3V,
not only original selected e and n dyads, and for BOTH signed
ε branches. Neither the target Fourier precision nor K0 affects
the fixed diagonal exponent. The source 4.17 restricted complex
offdiagonal is NOT bounded by this theorem. -/
theorem parity_eventually_original_historical_full_odd_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      parityOriginalHistoricalWeightedExtendedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V)
          α signed ⌊2*Real.exp L⌋₊
          (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) ≤
      2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) := by
  filter_upwards [parity_eventually_original_historical_extended_diagonal_polylog434,
    eventually_ge_atTop (8:ℝ)] with L hDiag hLw
  refine ⟨hDiag.1,hLw,?_⟩
  intro hL band slot δ ξ E V rho K α signed Acoef hA hα
  have hLp : 0<L := by linarith
  let D := parityOriginalHistoricalExtendedUnweightedDiagonal434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed ⌊2*Real.exp L⌋₊
  have hBound := parity_original_historical_extended_diagonal_weight_le434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed ⌊2*Real.exp L⌋₊
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) (2*L^(88:ℝ))
      (by intro e he n hn; exact (parity_original_historical_dyadic_eta_weight_polylog434 L E V hL e n).2)
  have hD := hDiag.2 band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V)
    α signed Acoef hA hα
  have hC : 0≤2*L^(88:ℝ) := by positivity
  have hMultiply := mul_le_mul_of_nonneg_left hD hC
  have hPower : L^(88:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256)=
      L^(2*parityOriginalW1PolylogExponent434+344) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (2*L^(88:ℝ))*D := hBound
    _ ≤ (2*L^(88:ℝ)) * (Acoef^2*Real.exp L*
       L^(2*parityOriginalW1PolylogExponent434+256)) := hMultiply
    _ = 2*Acoef^2*Real.exp L*
       L^(2*parityOriginalW1PolylogExponent434+344) := by
         rw [←hPower]
         ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddOffdiagKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Native true original source k/z physical signed offdiagonal after
PRE-GRAM nonnegative enlarged Cauchy e/n supports. No selected-Q
sparsity survives in Eenv or Nenv, but original two endpoint B509
Q/P physical gates remain LITERAL. -/
def parityOriginalHistoricalWeightedExtendedPhysicalKZ434
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
          ∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp Nenv,
            ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
              (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
              ((w e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

theorem parity_original_historical_weighted_full_odd_offdiag_k_z_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hOdd : ∀ e∈Eenv, Odd e) :
    parityOriginalHistoricalWeightedExtendedOffdiag434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w =
    parityOriginalHistoricalWeightedExtendedPhysicalKZ434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := Eenv
  let F : ℕ → ℕ → ℕ → ℕ → ℂ := fun e n m mp =>
    ((w e n:ℝ):ℂ) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  have hPoint (e n m mp : ℕ) :
      ((w e n:ℝ):ℂ) *
      ((α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m) *
       star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)) = F e n m mp := by
    exact congrArg (fun t : ℂ => ((w e n:ℝ):ℂ)*t)
      (parity_original_historical_actual_ENM_pair_eq_gated_source434
        d L band slot δ ξ rho α signed Y e n m mp)
  have hZero (e n m : ℕ) (he : e∈Q) :
      (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K 0,F e n m mp)=0 := by
    apply Finset.sum_eq_zero
    intro mp hmp
    have hp := Finset.mem_filter.mp hmp
    have hz := parity_original_historical_actual_zero_k_physical_source_vanishes434
      d L band slot δ ξ rho K α signed Y e n m mp
      (hOdd e he) hp.1 hp.2
    dsimp [F]
    rw [hz,mul_zero]
  unfold parityOriginalHistoricalWeightedExtendedOffdiag434
    parityOriginalHistoricalWeightedExtendedPhysicalKZ434
  simp_rw [Finset.mul_sum]
  change (∑e∈Q,∑n∈Nenv,∑m∈K,∑mp∈K.erase m,
      ((w e n:ℝ):ℂ)*
      ((α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
       star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
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
      exact parity_original_historical_weighted_z_source_filter_exact434
        d L band slot δ ξ rho α signed Y e m mp
        (fun n => ((w e n:ℝ):ℂ)) Nenv
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddKCutoff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The true constructed moving source η_e,L has support
 e/E > (1/2)L^-88, even after PRE-GRAM enlargement to ALL odd e.
This provides the required LOWER bound e≫E L^-88 for every
nonzero full-odd physical Fourier coefficient and not merely
for the historical sparse selected-Q e carrier. -/
theorem parity_original_historical_full_odd_eta_e_nonzero_lower434
    (L E : ℝ) (hL : 8≤L) (hE : 0<E)
    (e : ℕ)
    (hw : parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0) :
    E*L^(-88:ℝ)/2 < (e:ℝ) := by
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hSupport := parity_original_historical_dyadic_eta_e_support434
    (L^(-88:ℝ)) ha.1 ha.2 ((e:ℝ)/E) hw
  have hh := mul_lt_mul_of_pos_left hSupport.1 hE
  calc
    _ = (L^(-88:ℝ)/2)*E := by ring
    _ < ((e:ℝ)/E)*E := by simpa only [mul_comm] using hh
    _ = (e:ℝ) := div_mul_cancel₀ _ hE.ne'

/-- If the SOURCE e,n two-factor moving smoothing weight is
nonzero, then e lies in the actual e-window buffer and obeys
the same explicit lower e bound, regardless of e's membership
in selected-Q carrier. This avoids exploiting nonvanishing
of complex offdiagonal without an actual nonzero smoothing weight. -/
theorem parity_original_historical_full_odd_smoothing_nonzero_e_lower434
    (L E V : ℝ) (hL : 8≤L) (hE : 0<E)
    (e n : ℕ)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0) :
    E*L^(-88:ℝ)/2 < (e:ℝ) := by
  unfold parityOriginalHistoricalDyadicEtaWeight434 at hw
  have he : parityOriginalHistoricalDyadicEtaEAtLReal434
      L hL ((e:ℝ)/E) ≠ 0 := by
    intro hzero
    exact hw (by rw [hzero,zero_mul])
  exact parity_original_historical_full_odd_eta_e_nonzero_lower434 L E hL hE e he

/-- The actual moving SOURCE e-window positive weight support,
not the original sparse selected-Q band, forces a true canonical
nonzero physical k to be polynomial in L after full odd-e/n
positive Cauchy enlargement. EXACT explicit cost 2L^(K0+88),
with no assumption that selected e belongs to original Q tuple.

The argument is the genuine determinant m'-m=e*k, m,m'∈[U,2U),
E=U L^-K0 and eta_e(e/E)≠0. No character mask or desired
Parity (4.17) bound is used. -/
theorem parity_original_historical_full_odd_eta_e_physical_k_bound434
    (L U E K0 : ℝ) (e m mp : ℕ) (k : ℤ)
    (hL : 8≤L) (hU : 0<U)
    (hScale : E=U*L^(-K0))
    (hNonzero : parityOriginalHistoricalDyadicEtaEAtLReal434
      L hL ((e:ℝ)/E)≠0)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hShift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k) :
    (k.natAbs:ℝ) < 2*L^(K0+88) := by
  have hLp : 0<L := by linarith
  have hE : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have heLower := parity_original_historical_full_odd_eta_e_nonzero_lower434
    L E hL hE e hNonzero
  have hInverse : L^(-(K0+88))*L^(K0+88)=1 := by
    rw [←Real.rpow_add hLp]
    simp
  have hLower : (U*L^(-(K0+88)))/2 < (e:ℝ) := by
    have hp : L^(-K0)*L^(-88:ℝ)=L^(-(K0+88)) := by
      rw [←Real.rpow_add hLp]
      congr 1
      ring
    calc
      _ = (U*L^(-K0))*L^(-88:ℝ)/2 := by rw [←hp]; ring
      _ = E*L^(-88:ℝ)/2 := by rw [hScale]
      _ < (e:ℝ) := heLower
  have hePos : 0<(e:ℝ) :=
    (by positivity : 0<(U*L^(-(K0+88)))/2).trans hLower
  have hDiff : |(mp:ℝ)-(m:ℝ)|<U := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hShiftR : (mp:ℝ)-(m:ℝ)=(e:ℝ)*(k:ℝ) := by
    exact_mod_cast hShift
  have hKReal : |(k:ℝ)|=(k.natAbs:ℝ) := by
    simp only [Nat.cast_natAbs,Int.cast_abs]
  have hProduct : (e:ℝ)*(k.natAbs:ℝ)<U := by
    calc
      _ = |(e:ℝ)*(k:ℝ)| := by rw [abs_mul,abs_of_pos hePos,hKReal]
      _ = |(mp:ℝ)-(m:ℝ)| := by rw [hShiftR]
      _ < U := hDiff
  by_contra hkNeg
  have hkLarge : 2*L^(K0+88)≤(k.natAbs:ℝ) := le_of_not_gt hkNeg
  have hProdPos : 0<2*L^(K0+88) := by positivity
  have hLt : ((U*L^(-(K0+88)))/2)*(2*L^(K0+88))<
      (e:ℝ)*(2*L^(K0+88)) :=
    mul_lt_mul_of_pos_right hLower hProdPos
  have hLe : (e:ℝ)*(2*L^(K0+88))≤(e:ℝ)*(k.natAbs:ℝ) :=
    mul_le_mul_of_nonneg_left hkLarge hePos.le
  have hEq : ((U*L^(-(K0+88)))/2)*(2*L^(K0+88))=U := by
    calc
      _ = U*(L^(-(K0+88))*L^(K0+88)) := by ring
      _ = U := by rw [hInverse]; ring
  linarith [hLt,hLe,hProduct]

/-- On L≥8, all nonzero moving η_e-supported historical k satisfy
|k|<L^(K0+89); the factor two of the smooth buffer has been
absorbed by ONE additional explicit logarithmic power. This is
the exact arithmetic input to the original source-independent
Parity (2.6) character mask and 4.17 q=2|k| legality. -/
theorem parity_original_historical_full_odd_k_bound_polylog434
    (L U E K0 : ℝ) (e m mp : ℕ) (k : ℤ)
    (hL : 8≤L) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hw : parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hShift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k) :
    (k.natAbs:ℝ)<L^(K0+89) := by
  have hK := parity_original_historical_full_odd_eta_e_physical_k_bound434
    L U E K0 e m mp k hL hU hScale hw hmLo hmHi hmpLo hmpHi hShift
  have hLp : 0<L := by linarith
  have hBase : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
  have hP : L^(K0+89)=L^(K0+88)*L := by
    have hh : K0+89=(K0+88)+1 := by ring
    rw [hh,Real.rpow_add hLp,Real.rpow_one]
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : (2:ℝ)≤L) hBase.le]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddPhysicalPFree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- In the newly ENLARGED positive-original-Parity square the
selected e need no longer be a native Q-selected product.
Nevertheless, ANY genuinely populated original physical
Q/P gate e*vStar=ordinary_P(u) with u>0 forces e to be
P-prime-free, because ordinary_P(u) has no group-prime factors.
This follows from the real source gate, NOT the former sparse
selected-Q support or a hidden prime-free assumption. -/
theorem parity_original_historical_physical_gate_e_P_free434
    (P : Finset ℕ) (u e vs : ℕ) (hu : 0 < u)
    (hP : ∀p∈P,p.Prime)
    (hGate : e*vs=sourceOriginalOrdinaryPart P u) :
    ∀p∈P, ¬p∣e := by
  intro p hp hdiv
  have hOrdFree := parity_original_ordinary_part_avoids_P_prime434
    P u p hu.ne' hp (hP p hp)
  apply hOrdFree
  rw [←hGate]
  exact dvd_mul_of_dvd_left hdiv vs

/-- The complete original h=-2 two-ended SOURCE physical carrier
on the FULL odd-e×all-n envelope automatically forces its e
P-free at every actually nonzero Q/B509 endpoint, without using
the old selected-Q e support. Applies uniformly to both original
sign branches and every e within the full domain. -/
theorem parity_original_historical_full_odd_physical_valid_e_P_free434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    ∀p∈Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L),
      ¬p∣e := by
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hValid
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  have hU : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hGate : e*vs=sourceOriginalOrdinaryPart Pall u :=
    (Finset.mem_filter.mp hvs).2
  have hP : ∀p∈Pall,p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact (parity_original_actual_full_P_prime_rough_cap434 L hL g p hpg).1
  exact parity_original_historical_physical_gate_e_P_free434 Pall u e vs
    hU hP hGate

/-- SOURCE zero of the actual signed physical offdiagonal for
an e WITH ANY original P-group prime factor, even when e is an
arbitrary odd number in the ENLARGED pre-Gram interval.
This permits exact removal of P-bad e *after* the full square
has been expanded, without selecting only the old sparse-Q e
and without illegal complex monotonicity. -/
theorem parity_original_historical_full_odd_P_bad_e_physical_zero434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ)
    (p : ℕ) (hp : p∈Finset.univ.biUnion
      (sourceOriginalPAllActualBands 20 L))
    (hDiv : p∣e) :
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp=0 := by
  apply parity_original_historical_offdiag_zero_without_physical_N434
    d L band slot δ ξ rho α signed Y e m mp n
  intro hValid
  exact (parity_original_historical_full_odd_physical_valid_e_P_free434
    d L hL band slot δ Y e m mp n hValid p hp) hDiv
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEq417PFreeObstruction -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- An original positive integer free of ALL primes in P has
ordinary_P(u)=u exactly, including any unrelated prime powers.
This follows from literal true factorization, not a heuristic
statement about the prime-part. -/
theorem parity_original_historical_ordinary_eq_self_of_P_free434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0)
    (hFree : ∀p∈P,¬p∣u) :
    sourceOriginalOrdinaryPart P u=u := by
  have hEmpty : u.primeFactors∩P=∅ := by
    ext p
    constructor
    · intro hmem
      have hm := Finset.mem_inter.mp hmem
      exact False.elim (hFree p hm.2 (Nat.mem_primeFactors.mp hm.1).2.1)
    · intro hh
      simpa using hh
  have hPone : sourceOriginalPPrimePart P u=1 := by
    unfold sourceOriginalPPrimePart
    rw [hEmpty]
    simp
  have hSplit := source_original_ordinary_times_P_part P u hu
  rw [hPone,mul_one] at hSplit
  exact hSplit

/-- CONCRETE TRUE NUMBER-THEORETIC OBSTRUCTION to simply replacing
original physically P-gated Parity (4.16) two-prime-slot terms with
the FULL unrestricted Parity (4.17) correlation.

With P={3}, rough m=7,m'=13 (P-free, all prime factors >5),
k=2, e=(m'-m)/k=3 ODD POSITIVE, p=151,p'=281 BOTH PRIME,

    z=m'p=13*151=1963, z+2k=m p'=7*281=1967,
    mn=e p+2=455, m'n=e p'+2=845, n=65.

Both original z ordinary(P) divisor-pair and genuine common-shared
n arithmetic support conditions hold. Nevertheless e=3 has the
forbidden P factor 3 and the original Q/P physical gate
 e*vStar=ordinary_P(mn-2) is IMPOSSIBLE for every vStar. Thus a
pure unmasked two-prime-slot support inclusion is STRICT in general.

This is a small concrete ARITHMETIC test case, not a claim that
these numbers satisfy Parity's asymptotic original L-dependent Q_j
prime intervals, full large-L b629 fine rough support or cutoffs.
A correct source-sensitive masked (4.17) saving or precise
analysis of extra terms is still needed before full TypeII. -/
theorem parity_original_historical_unrestricted_pair_can_fail_physical_P_gate434 :
    let P : Finset ℕ := {3}
    let m : ℕ := 7
    let mp : ℕ := 13
    let k : ℤ := 2
    let e : ℕ := 3
    let z : ℕ := 1963
    let zp : ℕ := 1967
    let n : ℕ := 65
    let p : ℕ := 151
    let pp : ℕ := 281
    p.Prime ∧ pp.Prime ∧
    sourceD20Rough 5 m ∧ sourceD20Rough 5 mp ∧
    Odd e ∧
    (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧
    (z:ℤ)+2*k=(zp:ℤ) ∧
    z=mp*p ∧ zp=m*pp ∧
    mp ∣ sourceOriginalOrdinaryPart P z ∧
    m ∣ sourceOriginalOrdinaryPart P zp ∧
    m*n=e*p+2 ∧ mp*n=e*pp+2 ∧
    (∀vs : ℕ, e*vs≠sourceOriginalOrdinaryPart P (m*n-2)) := by
  dsimp only
  have hz : sourceOriginalOrdinaryPart ({3} : Finset ℕ) 1963 = 1963 := by
    apply parity_original_historical_ordinary_eq_self_of_P_free434
    · norm_num
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      norm_num
  have hzp : sourceOriginalOrdinaryPart ({3} : Finset ℕ) 1967 = 1967 := by
    apply parity_original_historical_ordinary_eq_self_of_P_free434
    · norm_num
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      norm_num
  have hImpossible : ∀vs : ℕ,
      3*vs≠sourceOriginalOrdinaryPart ({3} : Finset ℕ) (7*65-2) := by
    intro vs hGate
    have hu : 0 < (7*65-2:ℕ) := by norm_num
    have hPrime : ∀r∈({3}:Finset ℕ),r.Prime := by
      intro r hr
      simp only [Finset.mem_singleton] at hr
      subst r
      norm_num
    have hBad := parity_original_historical_physical_gate_e_P_free434
      ({3}:Finset ℕ) (7*65-2) 3 vs hu hPrime hGate
    exact (hBad 3 (by simp) (by norm_num))
  refine ⟨by norm_num,by norm_num,?_,?_,by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [sourceD20Rough]
  · norm_num [sourceD20Rough]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hz]
    norm_num
  · rw [hzp]
    norm_num
  · norm_num
  · norm_num
  · exact hImpossible
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEq417GateCriterion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- EXACT ORIGINAL Parity h=-2 physical Q/P source endpoint condition
for a prescribed pair (e,v) with 0<e and 0<v:

  ∃vStar>0, e*vStar=ordinary_P(e*v) AND
  v=vStar*Ppart_P(e*v)
    ↔ (no prime from ORIGINAL group P divides e).

This is a NECESSARY AND SUFFICIENT condition, not a heuristic
one-directional gate, and ALL repeated P-prime valuations of v
are kept. It follows from the literal original P split and
multiplicativity under P-prime-free multiplication. The missing
source support mask at Parity(4.17) therefore includes the
coupled e=(m'-m)/k P-free condition; it cannot be silently dropped
from the unrestricted signed two-prime-slot correlation. -/
theorem parity_original_historical_endpoint_QP_gate_iff_e_P_free434
    (P : Finset ℕ) (e v : ℕ) (he : 0<e) (hv : 0<v)
    (hP : ∀p∈P,p.Prime) :
    (∃vs : ℕ,
        0<vs ∧ e*vs=sourceOriginalOrdinaryPart P (e*v) ∧
        v=vs*sourceOriginalPPrimePart P (e*v)) ↔
      (∀p∈P,¬p∣e) := by
  constructor
  · rintro ⟨vs,hvs,hGate,hFactor⟩
    exact parity_original_historical_physical_gate_e_P_free434
      P (e*v) e vs (Nat.mul_pos he hv) hP hGate
  · intro hEFree
    let vs := sourceOriginalOrdinaryPart P v
    have hVS : 0<vs := Nat.pos_of_ne_zero
      (parity_original_ordinary_part_nonzero434 P v hv.ne')
    have hGate : e*vs=sourceOriginalOrdinaryPart P (e*v) := by
      exact (parity_original_ordinary_part_mul_prime_free434
        P e v he.ne' hv.ne' hEFree).symm
    have hPpart : sourceOriginalPPrimePart P (e*v)=
        sourceOriginalPPrimePart P v :=
      parity_original_P_prime_part_mul_prime_free434
        P e v he.ne' hv.ne' hEFree
    have hSplit := source_original_ordinary_times_P_part P v hv.ne'
    have hFactor : v=vs*sourceOriginalPPrimePart P (e*v) := by
      rw [hPpart]
      exact hSplit.symm
    exact ⟨vs,hVS,hGate,hFactor⟩

/-- EXACT BOTH-ENDPOINT original Parity(4.13) physical source Q/P
conditions for positive e,v,v': if u=e*v and u'=e*v', then
genuine original positive vStar and vStar' witnesses with the
full Ppart decompositions exist SIMULTANEOUSLY if and only if
this one common e has NO ORIGINAL P-group prime divisor.

This strengthens the reverse divisor-pair arithmetic result:
for any unrestricted (4.17) pair with integer shared n, the
outstanding Q/P gate is literally a nonseparable condition on
e=(m'-m)/k, rather than an unspecified flaw in an endpoint.
No assumption about the source e window, fine α, or dyadic n is
introduced by this criterion. -/
theorem parity_original_historical_two_endpoint_QP_gate_iff_e_P_free434
    (P : Finset ℕ) (e v vp : ℕ)
    (he : 0<e) (hv : 0<v) (hvp : 0<vp)
    (hP : ∀p∈P,p.Prime) :
    (∃vs vps : ℕ,
      0<vs ∧ 0<vps ∧
      e*vs=sourceOriginalOrdinaryPart P (e*v) ∧
      e*vps=sourceOriginalOrdinaryPart P (e*vp) ∧
      v=vs*sourceOriginalPPrimePart P (e*v) ∧
      vp=vps*sourceOriginalPPrimePart P (e*vp)) ↔
    (∀p∈P,¬p∣e) := by
  have hFirst := parity_original_historical_endpoint_QP_gate_iff_e_P_free434
    P e v he hv hP
  have hSecond := parity_original_historical_endpoint_QP_gate_iff_e_P_free434
    P e vp he hvp hP
  constructor
  · rintro ⟨vs,vps,hvs,hvps,hg,hgp,hf,hfp⟩
    exact hFirst.mp ⟨vs,hvs,hg,hf⟩
  · intro hFree
    obtain ⟨vs,hvs,hg,hf⟩ := hFirst.mpr hFree
    obtain ⟨vps,hvps,hgp,hfp⟩ := hSecond.mpr hFree
    exact ⟨vs,vps,hvs,hvps,hg,hgp,hf,hfp⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEq417UngatedEndpoint -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Critical corrected Parity original (4.10) Cauchy-domain identity:
for source e>0 with NO P-group prime divisors and positive u,

   e*vStar = ordinary_P(u)
       ↔ e|u AND vStar = ordinary_P(u/e).

This proves that the PRE-CAUCHY original allocated e/vStar gate
agrees with the natural UNGATED physical a_v(v) coefficient
at v=u/e. For general full odd e the RIGHT condition can hold
even if P|e, whereas the original allocated e/vStar gate cannot.
Thus the replacement can be used to enlarge the NONNEGATIVE
Cauchy square to the paper's actual full (4.10) physical domain,
while keeping EXACT source values on selected-Q e. -/
theorem parity_original_historical_Pfree_e_gate_iff_ungated_divisor434
    (P : Finset ℕ) (u e vs : ℕ)
    (hu : 0<u) (he : 0<e)
    (hFree : ∀p∈P,¬p∣e) :
    (e*vs=sourceOriginalOrdinaryPart P u) ↔
    (e∣u ∧ vs=sourceOriginalOrdinaryPart P (u/e)) := by
  constructor
  · intro hGate
    have hU : u≠0 := hu.ne'
    have hPpart : sourceOriginalPPrimePart P u≠0 :=
      parity_original_P_prime_part_nonzero434 P u hU
    let v := vs*sourceOriginalPPrimePart P u
    have hUEq : u=e*v := by
      have hSplit := source_original_ordinary_times_P_part P u hU
      rw [←hGate] at hSplit
      calc
        _ = (e*vs)*sourceOriginalPPrimePart P u := hSplit.symm
        _ = e*v := by dsimp [v]; ring
    have hDiv : e∣u := by
      rw [hUEq]
      exact dvd_mul_right e v
    have hvPos : 0<v := by
      have hReal := hu
      rw [hUEq] at hReal
      exact Nat.pos_of_mul_pos_left hReal
    have hEq : vs=sourceOriginalOrdinaryPart P v := by
      have hVOrd := parity_original_ordinary_part_mul_prime_free434
        P e v he.ne' hvPos.ne' hFree
      rw [←hUEq, ←hGate] at hVOrd
      exact Nat.eq_of_mul_eq_mul_left he hVOrd
    have hDivEq : u/e=v := by
      rw [hUEq]
      exact Nat.mul_div_cancel_left v he
    refine ⟨hDiv,?_⟩
    rw [hDivEq]
    exact hEq
  · rintro ⟨hDiv,hVS⟩
    have hNZ : e≠0 := he.ne'
    have hUeq : u=e*(u/e) := by
      exact (Nat.mul_div_cancel_left' hDiv).symm
    have hvPos : 0<u/e := by
      have hu' := hu
      rw [hUeq] at hu'
      exact Nat.pos_of_mul_pos_left hu'
    have hOrd := parity_original_ordinary_part_mul_prime_free434
      P e (u/e) he.ne' hvPos.ne' hFree
    rw [←hUeq] at hOrd
    rw [hVS]
    exact hOrd.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddCharacterMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- **FULL odd-e original Parity (2.6) character mask** after
legitimate original (4.10) positive-Cauchy expansion to ALL odd e.

For every nonzero actual constructed smooth η_e,L at the physical
e, ANY odd e (not necessarily selected Q) with BOTH genuine Q/P
h=-2 endpoints, fine b629 alpha_m,alpha_mp ≠0 and original
m,m' dyad admits a nonzero signed canonical k with
|k|<L^(K0+89), k EVEN, and EXACT original (2.6) character
projector value 1:
  Σχ cχ χ(m') conjχ(m)=1.

The new K0+89 (rather than source sparse K0+88) precisely pays the
factor 2 width of the moving η_e positive-buffer support.
Rough cofactor m,m' makes χ units mod 2|k|; no assumption about
a sparse selected e, a made-up character modulus or spectral 4.17
saving. Full original physical Q/P gates and signed negative k
are preserved. -/
theorem parity_eventually_original_full_odd_smooth_fine_mask434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hL : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U E : ℝ) (K : Finset ℕ)
        (prime : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (e m mp n : ℕ),
      Odd e → m≠mp →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0 →
      parityOriginalHistoricalPhysicalValidN434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp n →
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m≠0 →
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp≠0 →
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      k≠0 ∧ (k.natAbs:ℝ)<L^(K0+89) ∧ Even k ∧
        (∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          χ (mp : ZMod (2*k.natAbs)) *
          star (χ (m : ZMod (2*k.natAbs))))=1 := by
  filter_upwards [parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma,
    b638_eventually_poly_exp434 2 (K0+89) (1/2) (by norm_num) (by norm_num),
    eventually_ge_atTop (8:ℝ)] with L hRough hPoly hL8
  refine ⟨hL8,?_⟩
  intro hL band slot δ U E K prime lFine uFine hU hScale hl hFineLow
    e m mp n he hNe hmLo hmHi hmpLo hmpHi hEta hValid hAm hAmp
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  have hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m :=
    hRough prime lFine uFine hl hFineLow K m hAm
  have hRoughMp : sourceD20Rough (Real.exp (Real.sqrt L)) mp :=
    hRough prime lFine uFine hl hFineLow K mp hAmp
  have hBound : (k.natAbs:ℝ)<L^(K0+89) :=
    parity_original_historical_full_odd_k_bound_polylog434
      L U E K0 e m mp k hL hU hScale hEta
      hmLo hmHi hmpLo hmpHi
      (parity_original_historical_physical_k_exact_cofactor_shift434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp n he hNe hValid)
  have hNonzero : k≠0 :=
    (parity_original_historical_supported_canonical_z_positive_shift434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp n he hNe hValid).1
  have hW : (2:ℝ)≤Real.exp (Real.sqrt L) :=
    parity_rough_cutoff_at_least_two434 L (by linarith)
  have hmOdd : Odd m := parity_original_rough_cofactor_odd434
    (Real.exp (Real.sqrt L)) m hW hRoughM
  have hmpOdd : Odd mp := parity_original_rough_cofactor_odd434
    (Real.exp (Real.sqrt L)) mp hW hRoughMp
  have hPoly' : 2*L^(K0+89)≤Real.exp (Real.sqrt L) := by
    simpa only [Real.sqrt_eq_rpow] using hPoly
  have hq : ((2*k.natAbs : ℕ):ℝ)≤Real.exp (Real.sqrt L) := by
    calc
      _ = 2*(k.natAbs:ℝ) := by push_cast; ring
      _ ≤ 2*L^(K0+89) := mul_le_mul_of_nonneg_left hBound.le (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := hPoly'
  have hDet := parity_original_historical_physical_k_exact_cofactor_shift434
    (sourceOriginalLiteralDepth 20 L) L band slot δ
    ⌊2*Real.exp L⌋₊ e m mp n he hNe hValid
  have hMask := parity_original_bilinear_shift_mask_fourier_one434
    e m mp he hmOdd hmpOdd k hNonzero hDet
    (Real.exp (Real.sqrt L)) hRoughM hq
  exact ⟨hNonzero,hBound,hMask.1,hMask.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddMaskInsert -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- EXACT original Parity(2.6) character mask inserted into the
**NEW FULL-ODD-E enlarged original physical signed offdiagonal**
at a fixed original positive canonical z. The selected e is from
ALL odd e≤2E, NOT sparse original selected-Q labels, and n is
from ALL n≤3V. Each n-dependent true moving eta_e and fixed eta_n
weight remains INSIDE its original physical supported n-fibre.

If the complex signed source sum W vanishes then the identity is
trivial. If not, a genuinely physically gated n with nonzero
source smoothing and both actual fine alpha coefficients exists;
this proves the native exact Parity(2.6) character identity on the
needed m,mp,k with |k|<L^(K0+89) from actual eta support.
There is NO assumed cancellation, no independent character count,
no illegitimate complex superset inequality, and no unsupported
physical n or z term. -/
theorem parity_eventually_original_full_odd_supported_z_fine_mask_insert434
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
      z∈parityOriginalHistoricalPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp Nenv →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      let W := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434
        e m mp Nenv z).filter
          (parityOriginalHistoricalPhysicalValidN434
            (sourceOriginalLiteralDepth 20 L) L band slot δ
            ⌊2*Real.exp L⌋₊ e m mp),
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
            ⌊2*Real.exp L⌋₊ e n m mp
      W = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        (parityShiftTwoMaskCoefficient434 k.natAbs χ *
          χ (mp : ZMod (2*k.natAbs)) *
          star (χ (m : ZMod (2*k.natAbs)))) * W := by
  filter_upwards [parity_eventually_original_full_odd_smooth_fine_mask434
    S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv signed prime lFine uFine
    e m mp z hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    hl hFineLow
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let N := (parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
    (parityOriginalHistoricalPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp)
  let W : ℂ := ∑n∈N,
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
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
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp [ham]
    exact hW hZero
  have hAmp : alpha mp ≠ 0 := by
    intro hamp
    have hZero : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp [hamp]
    exact hW hZero
  obtain ⟨n,hn,hTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  have hValid : parityOriginalHistoricalPhysicalValidN434
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

/-! ## OriginalHistoricalFullOddWeightedMaskedKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Literal full-odd-e post-GRAM original signed Parity(4.13) physical
k/z weighted SOURCE after Parity(2.6) character insertion; actual
eta_e,L*eta_n smooth weight remains in true n-fibre. The external
selected Q-e support was legally enlarged only before Cauchy. -/
def parityOriginalHistoricalFullOddWeightedMaskedKZ434
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
          ∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp Nenv,
            ∑chi : DirichletCharacter ℂ (2*k.natAbs),
              (parityShiftTwoMaskCoefficient434 k.natAbs chi *
                chi (mp : ZMod (2*k.natAbs)) *
                star (chi (m : ZMod (2*k.natAbs)))) *
              (∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
                (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
                ((w e n:ℝ):ℂ)*
                parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp)

end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddWeightedMaskJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact character-orthogonality (Parity 2.6) for the COMPLETE
post-positive-Cauchy FULL-ODD-E and full n carrier signed offdiagonal.
Its smooth weight is the ACTUAL constructed eta_e,L(e/E) eta_n(n/V),
and remains inside the real B509/Q/P physical n-fibre. The source
alpha is the original b629 fine-cofactor, both signs 1/E retained.

The proof is not an arbitrary extension of the OLD sparse signed
sum: the positive Cauchy rectangle was enlarged BEFORE Gram; the
entire new signed offdiagonal is reindexed to exact k/z physical
carriers, and the mask is now independently derived from the actual
nonzero eta_e support, |k|<L^(K0+89), original W-roughness and the
true physical determinant. No #characters loss and no hypothetical
Parity4.17 spectral saving. -/
theorem parity_eventually_original_full_odd_fine_offdiag_masked434
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
      parityOriginalHistoricalWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalFullOddWeightedMaskedKZ434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_full_odd_supported_z_fine_mask_insert434
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
  rw [parity_original_historical_weighted_full_odd_offdiag_k_z_exact434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    alpha signed ⌊2*Real.exp L⌋₊ w hOdd]
  unfold parityOriginalHistoricalWeightedExtendedPhysicalKZ434
    parityOriginalHistoricalFullOddWeightedMaskedKZ434
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
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddCharacterOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Genuine real signed full-odd e × all n Parity(4.13) character
OUTER, χ coefficient cχ conjχ(m) exterior to m',z,n and χ(m')
interior to the true B509/Q/P physical arithmetic fibre. Character
orthogonality was already inserted exactly; this is FINITE Fubini,
not a norm bound on the signed source nor a guessed TypeII saving. -/
def parityOriginalHistoricalFullOddCharacterOuter434
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
              (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
                d L band slot δ Y e m mp Nenv,
                ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
                  (parityOriginalHistoricalPhysicalValidN434
                    d L band slot δ Y e m mp),
                  ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                    d L band slot δ ξ rho α signed Y e n m mp))

/-- Source-faithful original signed after-mask finite Fubini. In
particular the Dirichlet character is NOT applied to the unsigned
odd-parity projector and no character count is paid before using the
source-proven (2.6) ℓ1 mask bound. -/
theorem parity_original_historical_full_odd_masked_k_z_eq_character_outer434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    parityOriginalHistoricalFullOddWeightedMaskedKZ434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w =
    parityOriginalHistoricalFullOddCharacterOuter434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  unfold parityOriginalHistoricalFullOddWeightedMaskedKZ434
    parityOriginalHistoricalFullOddCharacterOuter434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let Q : Finset (DirichletCharacter ℂ (2*k.natAbs)) := Finset.univ
  let Z : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ Y e m mp Nenv
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      star (chi (m : ZMod (2*k.natAbs)))
  let f : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
    fun chi mp => chi (mp : ZMod (2*k.natAbs))
  let Wfz : ℕ → ℕ → ℂ := fun mp z =>
    ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
      ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
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

/-! ## OriginalHistoricalFullOddCharacterJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- Original Parity (4.10) positive-Cauchy enlarged to FULL odd e≤2E
and ALL n≤3V: its COMPLETE new signed offdiagonal with actual
moving-source eta_e,L*eta_n, fine b629 alpha, physical Q/P/B509
H0, original epsilon=1 or E, is EXACTLY the character-outer
Parity(2.6) physical k/z expression. Every χ coefficient cχ conjχ(m)
is outside m',z,n (and χ(m') is inside), at zero ℓ1-cost.

This was proved by source-independent full-odd-e mask, NOT by
illegitimately replacing a sparse SOURCE complex sum with the
full signed correlation. Its canonical nonzero k obeys the new
L^(K0+89) bound only when the smooth source e weight is nonzero.
No 4.17 cancellation or Type II is claimed. -/
theorem parity_eventually_original_full_odd_fine_offdiag_eq_character_outer434
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
      parityOriginalHistoricalWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalFullOddCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_full_odd_fine_offdiag_masked434
      S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [hMask.2 hLw band slot δ ξ U E V rho K Nenv prime signed
    lFine uFine hU hScale hDyad hl hFineLow]
  exact parity_original_historical_full_odd_masked_k_z_eq_character_outer434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed ⌊2*Real.exp L⌋₊
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddTypeIIPrecursor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Real positive Cauchy combined with genuine complex signed Gram:
if the diagonal is bounded, the ONLY missing quantitative component
is the norm of its complex signed offdiagonal. In particular no
signed complex subset inclusion is used. -/
theorem parity_original_physical_cauchy_gram_diagonal_and_offdiag_le434
    (cauchy mass square diagonal B : ℝ) (OD : ℂ)
    (hmass : 0 ≤ mass) (hcauchy : cauchy ≤ mass * square)
    (hgram : ((square:ℝ):ℂ)=((diagonal:ℝ):ℂ)+OD)
    (hdiag : diagonal≤B) :
    cauchy ≤ mass * (B+‖OD‖) := by
  have hRe : square=diagonal+OD.re := by
    have hh := congrArg Complex.re hgram
    simpa only [Complex.ofReal_re,Complex.add_re] using hh
  have hSquare : square≤B+‖OD‖ := by
    rw [hRe]
    exact add_le_add hdiag (Complex.re_le_norm OD)
  exact hcauchy.trans (mul_le_mul_of_nonneg_left hSquare hmass)

/-- SOURCE-TRUE Parity §4.10--§4.16 quantitative TypeII precursor:

 |A_source|² ≤ (Σoriginal selected-e,n |a_e β_n|²) *
  (2 Acoef² exp(L) L^(2*C_W1+344) + ||OD_full_odd_character_outer||).

This is a theorem about the ACTUAL selected-Q h=-2 r20 Cauchy input,
not an assumed bilinear estimate. The second Cauchy factor was
legitimately enlarged to ALL odd e≤2E and n≤3V BEFORE the Gram,
with actual nonnegative constructed η_e,L η_n. The full original
positive diagonal was bounded by shifted τ(u)^3 τ(u+2) moment, and
full-odd signed character mask and χ-outer equality were independently
proved from physical eta support and true b629 W-rough cofactor.
No spectral (4.17) saving, TypeII (4.2) or final theorem is assumed. -/
theorem parity_eventually_original_full_odd_Cauchy_diag_character_outer_bound434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
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
      let EFull := parityOriginalHistoricalFullOddEEnvelope434 E
      let NFull := parityOriginalHistoricalFullNEnvelope434 V
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      let OD := parityOriginalHistoricalFullOddCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K EFull NFull alpha signed ⌊2*Real.exp L⌋₊ w
      let Amass := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
      Amass *
        (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
          ‖OD‖) := by
  filter_upwards [parity_eventually_original_actual_full_odd_Cauchy_Gram434,
    parity_eventually_original_historical_full_odd_diagonal_polylog434,
    parity_eventually_original_full_odd_fine_offdiag_eq_character_outer434
      S beta gamma K0 hS hbeta hgamma] with L hSquare hDiag hChar
  refine ⟨hDiag.1,hSquare.1,?_⟩
  intro hLw band slot δ ξ U E V rho K J betaSeq prime signed
    lFine uFine Acoef hU hV hScale hDyad hNRange hl hFineLow
  dsimp only
  intro hAcoef hAlpha
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let EFull := parityOriginalHistoricalFullOddEEnvelope434 E
  let NFull := parityOriginalHistoricalFullNEnvelope434 V
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  let Square := parityOriginalHistoricalWeightedExtendedCauchySquare434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K EFull NFull
    alpha signed ⌊2*Real.exp L⌋₊ w
  let Diag := parityOriginalHistoricalWeightedExtendedDiagonal434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K EFull NFull
    alpha signed ⌊2*Real.exp L⌋₊ w
  let OD := parityOriginalHistoricalFullOddCharacterOuter434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K EFull NFull
    alpha signed ⌊2*Real.exp L⌋₊ w
  let Mass : ℝ := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
      (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*betaSeq n‖^2
  let Bdiag : ℝ := 2*Acoef^2*Real.exp L*
    L^(2*parityOriginalW1PolylogExponent434+344)
  have hLp : 0<L := by linarith [hSquare.1]
  have hE : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hOld := hSquare.2 hLw band slot δ ξ E V rho K J alpha betaSeq
    signed ⌊2*Real.exp L⌋₊ hE hV hNRange
  have hOld' :
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha betaSeq signed ⌊2*Real.exp L⌋₊‖^2 ≤ Mass*Square :=
    hOld.1
  have hChar' := hChar.2 hLw band slot δ ξ U E V rho K NFull
    prime signed lFine uFine hU hScale hDyad hl hFineLow
  have hEqChar : parityOriginalHistoricalWeightedExtendedOffdiag434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K EFull NFull
    alpha signed ⌊2*Real.exp L⌋₊ w = OD := hChar'
  have hEqGram : ((Square:ℝ):ℂ) = ((Diag:ℝ):ℂ)+OD := by
    have hh : ((Square:ℝ):ℂ)=((Diag:ℝ):ℂ)+
        parityOriginalHistoricalWeightedExtendedOffdiag434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
          EFull NFull alpha signed ⌊2*Real.exp L⌋₊ w := hOld.2
    rw [hEqChar] at hh
    exact hh
  have hD := hDiag.2.2 hLw band slot δ ξ E V rho K alpha signed Acoef
    hAcoef hAlpha
  have hD' : Diag≤Bdiag := hD
  have hMass : 0≤Mass := by
    dsimp [Mass]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact parity_original_physical_cauchy_gram_diagonal_and_offdiag_le434
    _ Mass Square Diag Bdiag OD hMass hOld' hEqGram hD'
end Green64Analytic.Parity

end

end

