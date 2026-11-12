module

public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part007
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# Sieve / Foundations / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalPhysicalNFilter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- This is the ACTUAL two-endpoint physical source condition on one
original n, not an a priori test on its canonical z. Both original
positive integer u/u' sources and both genuine Q/B509 vStar support
fibres must be populated for the complex offdiagonal term to survive. -/
def parityOriginalHistoricalPhysicalValidN434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) : Prop :=
  ∃ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
    ∃ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
      (parityOriginalHistoricalOffdiagPhysicalVStarGate434
        d L band slot δ e u).Nonempty ∧
      (parityOriginalHistoricalOffdiagPhysicalVStarGate434
        d L band slot δ e up).Nonempty

/-- The original true n support at a fixed e,m,m' and original
physical h=-2 B509/Q product carriers. This is a subset of J, not
an independently manufactured ``v'' support or a target Z dyad. -/
def parityOriginalHistoricalPhysicalValidNFibre434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) : Finset ℕ :=
  J.filter (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp)

/-- The COMPLEX original two-ended signed physical source is zero
unless the actual h=-2 u and u' fibres AND both P/Q gated vStar
supports are simultaneously inhabited. This does not use Cauchy,
mask-orthogonality or a hypothesized pointwise coefficient bound. -/
theorem parity_original_historical_offdiag_zero_without_physical_N434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp n : ℕ)
    (hBad : ¬parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp = 0 := by
  unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro up hup
  let V := parityOriginalHistoricalOffdiagPhysicalVStarGate434
    d L band slot δ e u
  let Vp := parityOriginalHistoricalOffdiagPhysicalVStarGate434
    d L band slot δ e up
  by_cases hV : V.Nonempty
  · have hVp : ¬Vp.Nonempty := by
      intro hVp
      exact hBad ⟨u,hu,up,hup,hV,hVp⟩
    have hEmpty : Vp = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVp
    change ∑ vStar∈V,∑vpStar∈Vp,_ = 0
    rw [hEmpty]
    simp
  · have hEmpty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
    change ∑ vStar∈V,∑vpStar∈Vp,_ = 0
    rw [hEmpty]
    simp

/-- The ENTIRE original signed physical offdiagonal n sum can be
restricted exactly to supported source n. Unsupported canonical k,z
image elements have zero physical coefficient; no absolute value,
no Fourier tail and no source term are dropped. -/
theorem parity_original_historical_offdiag_N_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) :
    (∑ n∈J,parityOriginalHistoricalOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp) =
    ∑ n∈parityOriginalHistoricalPhysicalValidNFibre434
       d L band slot δ Y e m mp J,
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  unfold parityOriginalHistoricalPhysicalValidNFibre434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n
  · simp [h]
  · simp [h,parity_original_historical_offdiag_zero_without_physical_N434
      d L band slot δ ξ rho α signed Y e m mp n h]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- On the ACTUAL two-sided signed physical source support (rather than
the oversized canonical n->z image), the original map
`n ↦ z=m'*(m*n-2)/e` is INJECTIVE. This remains true even if a floor
quotient collides on nonsupported n. Crucially, both original h=-2
Q/P product constraints are kept, and no factor `#n` is lost. -/
theorem parity_original_historical_supported_canonical_z_injective434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n n' : ℕ) (he : 0<e) (hmp : 0 < mp)
    (hn : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hn' : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n')
    (hz : parityOriginalHistoricalCanonicalZ434 e m mp n =
      parityOriginalHistoricalCanonicalZ434 e m mp n') : n=n' := by
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hn
  obtain ⟨u',hu',up',hup',⟨vs',hvs'⟩,⟨vps',hvps'⟩⟩ := hn'
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hu').2
  have huPos : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have huPos' : 0 < u' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu').1).1
  have hgate := (Finset.mem_filter.mp hvs).2
  have hgate' := (Finset.mem_filter.mp hvs').2
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hZ1 := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n u vs he huPos h1.2.2 hgate
  have hZ2 := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n' u' vs' he huPos' h2.2.2 hgate'
  have hvEq : vs*sourceOriginalPPrimePart P u =
      vs'*sourceOriginalPPrimePart P u' := by
    apply Nat.mul_left_cancel hmp
    calc
      mp*(vs*sourceOriginalPPrimePart P u) =
        parityOriginalHistoricalCanonicalZ434 e m mp n := hZ1.symm
      _ = parityOriginalHistoricalCanonicalZ434 e m mp n' := hz
      _ = mp*(vs'*sourceOriginalPPrimePart P u') := hZ2
  have hU : e*(vs*sourceOriginalPPrimePart P u)=u := by
    calc
      _ = (e*vs)*sourceOriginalPPrimePart P u := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u*sourceOriginalPPrimePart P u := by rw [hgate]
      _ = u := source_original_ordinary_times_P_part P u huPos.ne'
  have hU' : e*(vs'*sourceOriginalPPrimePart P u')=u' := by
    calc
      _ = (e*vs')*sourceOriginalPPrimePart P u' := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u'*sourceOriginalPPrimePart P u' := by rw [hgate']
      _ = u' := source_original_ordinary_times_P_part P u' huPos'.ne'
  have huEq : u=u' := by
    calc
      u = e*(vs*sourceOriginalPPrimePart P u) := hU.symm
      _ = e*(vs'*sourceOriginalPPrimePart P u') := by rw [hvEq]
      _ = u' := hU'
  have hmPos : 0 < m := h1.1
  have hmn : m*n=m*n' := by
    omega
  exact Nat.mul_left_cancel hmPos hmn

/-- On ACTUAL supported data, canonical z and its shifted companion
z+2k are strictly positive, and k is the NONZERO physical Parity(4.13)
quotient. The positivity is not extended to the unfiltered image. -/
theorem parity_original_historical_supported_canonical_z_positive_shift434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hn : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    k≠0 ∧ 0 < z ∧ 0 < (z:ℤ)+2*k := by
  dsimp only
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hn
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hup).2
  have huPos : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0 < up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hgate := (Finset.mem_filter.mp hvs).2
  have hgatep := (Finset.mem_filter.mp hvps).2
  have hPhys := parity_original_historical_actual_k_quotient_source434
    L e m mp n u up vs vps he huPos hupPos hgate hgatep
    h1.2.2 h2.2.2 hneq
  have hZ := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n u vs he.pos huPos h1.2.2 hgate
  have hShift := parity_original_historical_canonical_z_plus_two_k_source434
    L e m mp n u up vs vps he huPos hupPos hgate hgatep
    h1.2.2 h2.2.2 hneq
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hEv : e*(vs*sourceOriginalPPrimePart P u)=u := by
    calc
      _ = (e*vs)*sourceOriginalPPrimePart P u := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u*sourceOriginalPPrimePart P u := by rw [hgate]
      _ = u := source_original_ordinary_times_P_part P u huPos.ne'
  have hEvp : e*(vps*sourceOriginalPPrimePart P up)=up := by
    calc
      _ = (e*vps)*sourceOriginalPPrimePart P up := by ac_rfl
      _ = sourceOriginalOrdinaryPart P up*sourceOriginalPPrimePart P up := by rw [hgatep]
      _ = up := source_original_ordinary_times_P_part P up hupPos.ne'
  have hvPos : 0 < vs*sourceOriginalPPrimePart P u :=
    Nat.pos_of_mul_pos_left (hEv.symm ▸ huPos)
  have hvpPos : 0 < vps*sourceOriginalPPrimePart P up :=
    Nat.pos_of_mul_pos_left (hEvp.symm ▸ hupPos)
  have hmPos : 0 < m := h1.1
  have hmpPos : 0 < mp := h2.1
  refine ⟨hPhys.1,?_,?_⟩
  · rw [hZ]
    exact Nat.mul_pos hmpPos hvPos
  · rw [hShift]
    exact_mod_cast Nat.mul_pos hmPos hvpPos

/-- Original physical supported canonical z-FIBRE is a singleton at
most. Hence after genuine physical source restriction there is NO
factor of `#J` from n->z collisions when invoking character masks. -/
theorem parity_original_historical_supported_canonical_z_fibre_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (he : 0<e) (hmp : 0 < mp)
    (J : Finset ℕ) (z : ℕ) :
    ((parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn n' hn'
  have hnV := (Finset.mem_filter.mp hn).2
  have hnV' := (Finset.mem_filter.mp hn').2
  have hnZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hnZ' := (Finset.mem_filter.mp (Finset.mem_filter.mp hn').1).2
  exact parity_original_historical_supported_canonical_z_injective434
    d L band slot δ Y e m mp n n' he hmp hnV hnV'
    (hnZ.trans hnZ'.symm)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalShiftTwoFactors -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- The true original Parity (4.13) physical h=-2 signed pair has
BOTH *natural* endpoint identities on its populated Q/P source:
  z=m'*v,  (z+2k).toNat=m*v',
with v=(mn-2)/e and v'=(m'n-2)/e both STRICTLY POSITIVE.
No guessed support beyond original physical two-ended gates and
no nonzero k surrogate is inserted. This is the exact domain
needed for transferring original W1, epsilon and P-part to the
two prime-slot cores of §4.6. -/
theorem parity_original_historical_true_two_endpoint_z_v_factors434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let v := parityOriginalHistoricalCanonicalV434 e m n
    let vp := parityOriginalHistoricalCanonicalV434 e mp n
    0<v ∧ 0<vp ∧ 0<z ∧ 0<(z:ℤ)+2*k ∧
      z=mp*v ∧ ((z:ℤ)+2*k).toNat=m*vp := by
  dsimp only
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hValid
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hmn := (Finset.mem_filter.mp hu).2.2.2
  have hmpn := (Finset.mem_filter.mp hup).2.2.2
  have hg := (Finset.mem_filter.mp hvs).2
  have hgp := (Finset.mem_filter.mp hvps).2
  have hvEq := parity_original_historical_canonical_v_eq_source_physical434
    L e m n u vs he.pos huPos hmn hg
  have hvpEq := parity_original_historical_canonical_v_eq_source_physical434
    L e mp n up vps he.pos hupPos hmpn hgp
  have hShift := parity_original_historical_canonical_z_plus_two_k_source434
    L e m mp n u up vs vps he huPos hupPos hg hgp hmn hmpn hneq
  dsimp only at hShift
  have hShiftEq :
      (parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
        2*parityOriginalHistoricalOffdiagK434 e m mp =
      (m:ℤ)*(parityOriginalHistoricalCanonicalV434 e mp n:ℤ) := by
    rw [hShift]
    rw [hvpEq]
    simp only [Nat.cast_mul]
  have hPositive := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m mp n he hneq
    ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩
  dsimp only at hPositive
  have hVpos : 0<parityOriginalHistoricalCanonicalV434 e m n := by
    have hz : 0 < mp * parityOriginalHistoricalCanonicalV434 e m n := hPositive.2.1
    exact Nat.pos_of_mul_pos_left hz
  have hVpPos : 0<parityOriginalHistoricalCanonicalV434 e mp n := by
    have hz : (0:ℤ)<(m:ℤ)*(parityOriginalHistoricalCanonicalV434 e mp n:ℤ) := by
      rw [←hShiftEq]
      exact hPositive.2.2
    have hZnat : 0 < m * parityOriginalHistoricalCanonicalV434 e mp n := by
      exact_mod_cast hz
    exact Nat.pos_of_mul_pos_left hZnat
  have hNat :
      ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
        2*parityOriginalHistoricalOffdiagK434 e m mp).toNat =
      m*parityOriginalHistoricalCanonicalV434 e mp n := by
    rw [hShiftEq]
    rfl
  exact ⟨hVpos,hVpPos,hPositive.2.1,hPositive.2.2,rfl,hNat⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalTwoEndpointInvariants -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- EXACT SOURCE Parity §4.6 BOTH-ENDPOINT invariance on REAL
h=-2/Q/P populated physical data, for both original signed signs.
Set v=(mn-2)/e, v'=(m'n-2)/e, z=m'v and z'=z+2k=m v'.
If original fine alpha endpoints are W-rough, no group prime can
divide m or m'. Consequently, at BOTH actual endpoints:

 W1(z)=W1(v), W1(z')=W1(v');
 eps(z)=eps(v), eps(z')=eps(v');
 groupSign(z)=groupSign(v), groupSign(z')=groupSign(v');
 Ppart(z)=Ppart(v), Ppart(z')=Ppart(v');
 zStar=m'*vStar, z'Star=m*v'Star  (ordinary parts).

The last identities are for ORDINARY_P(v), not yet the original
reserved vStar: proving vStar=ordinary_P(v) requires exact Q/P
source e-divisibility. No term is extended outside true populated
physical supports and all P valuations retain multiplicities. -/
theorem parity_original_historical_physical_two_endpoint_P_invariance434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hm : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hmp : sourceD20Rough (Real.exp (Real.sqrt L)) mp)
    (signed : Bool) :
    let P := sourceOriginalPAllActualBands 20 L
    let Pall := Finset.univ.biUnion P
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    let v := parityOriginalHistoricalCanonicalV434 e m n
    let vp := parityOriginalHistoricalCanonicalV434 e mp n
    sourceOriginalW1 P z=sourceOriginalW1 P v ∧
    sourceOriginalW1 P zp=sourceOriginalW1 P vp ∧
    parityOriginalPSignedEpsilon434 Pall signed z=
      parityOriginalPSignedEpsilon434 Pall signed v ∧
    parityOriginalPSignedEpsilon434 Pall signed zp=
      parityOriginalPSignedEpsilon434 Pall signed vp ∧
    groupSign P signed z=groupSign P signed v ∧
    groupSign P signed zp=groupSign P signed vp ∧
    sourceOriginalPPrimePart Pall z=sourceOriginalPPrimePart Pall v ∧
    sourceOriginalPPrimePart Pall zp=sourceOriginalPPrimePart Pall vp ∧
    sourceOriginalOrdinaryPart Pall z=mp*sourceOriginalOrdinaryPart Pall v ∧
    sourceOriginalOrdinaryPart Pall zp=m*sourceOriginalOrdinaryPart Pall vp := by
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*k).toNat
  let v := parityOriginalHistoricalCanonicalV434 e m n
  let vp := parityOriginalHistoricalCanonicalV434 e mp n
  have hActual := parity_original_actual_full_P_prime_rough_cap434 L hL
  have hPprime : ∀g p,p∈P g → p.Prime :=
    fun g p hp => (hActual g p hp).1
  have hPbound : ∀g p,p∈P g → (p:ℝ)≤Real.exp (Real.sqrt L) :=
    fun g p hp => (hActual g p hp).2
  have hFmp : ∀g p,p∈P g → ¬p∣mp := by
    intro g p hp
    exact parity_original_actual_rough_avoids_group_prime434 _ mp p hmp
      (hPprime g p hp) (hPbound g p hp)
  have hFm : ∀g p,p∈P g → ¬p∣m := by
    intro g p hp
    exact parity_original_actual_rough_avoids_group_prime434 _ m p hm
      (hPprime g p hp) (hPbound g p hp)
  have hFmpAll : ∀p∈Pall,¬p∣mp := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hFmp g p hpg
  have hFmAll : ∀p∈Pall,¬p∣m := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hFm g p hpg
  have hmpNe : mp≠0 := by have h := hmp.1; omega
  have hmNe : m≠0 := by have h := hm.1; omega
  have hFactor := parity_original_historical_true_two_endpoint_z_v_factors434
    d L band slot δ Y e m mp n he hneq hValid
  dsimp only at hFactor
  obtain ⟨hv,hvp,hz,ht,hZ,hZp⟩ := hFactor
  change z = mp*v at hZ
  change zp = m*vp at hZp
  have hvNe : v≠0 := by exact hv.ne'
  have hvpNe : vp≠0 := by exact hvp.ne'
  have hWz : sourceOriginalW1 P z=sourceOriginalW1 P v := by
    rw [hZ]
    exact parity_original_W1_mul_rough_cofactor434 P mp v hPprime hFmp
  have hWzp : sourceOriginalW1 P zp=sourceOriginalW1 P vp := by
    rw [hZp]
    exact parity_original_W1_mul_rough_cofactor434 P m vp hPprime hFm
  have hEz : parityOriginalPSignedEpsilon434 Pall signed z=
      parityOriginalPSignedEpsilon434 Pall signed v := by
    rw [hZ]
    exact parity_original_signed_epsilon_mul_prime_free434 Pall mp v hmpNe hvNe hFmpAll signed
  have hEzp : parityOriginalPSignedEpsilon434 Pall signed zp=
      parityOriginalPSignedEpsilon434 Pall signed vp := by
    rw [hZp]
    exact parity_original_signed_epsilon_mul_prime_free434 Pall m vp hmNe hvpNe hFmAll signed
  have hGz : groupSign P signed z=groupSign P signed v := by
    rw [hZ]
    exact parity_original_group_sign_mul_prime_free434 P mp v hmpNe hvNe hFmp signed
  have hGzp : groupSign P signed zp=groupSign P signed vp := by
    rw [hZp]
    exact parity_original_group_sign_mul_prime_free434 P m vp hmNe hvpNe hFm signed
  have hPz : sourceOriginalPPrimePart Pall z=sourceOriginalPPrimePart Pall v := by
    rw [hZ]
    exact parity_original_P_prime_part_mul_prime_free434 Pall mp v hmpNe hvNe hFmpAll
  have hPzp : sourceOriginalPPrimePart Pall zp=sourceOriginalPPrimePart Pall vp := by
    rw [hZp]
    exact parity_original_P_prime_part_mul_prime_free434 Pall m vp hmNe hvpNe hFmAll
  have hOz : sourceOriginalOrdinaryPart Pall z=mp*sourceOriginalOrdinaryPart Pall v := by
    rw [hZ]
    exact parity_original_ordinary_part_mul_prime_free434 Pall mp v hmpNe hvNe hFmpAll
  have hOzp : sourceOriginalOrdinaryPart Pall zp=m*sourceOriginalOrdinaryPart Pall vp := by
    rw [hZp]
    exact parity_original_ordinary_part_mul_prime_free434 Pall m vp hmNe hvpNe hFmAll
  exact ⟨hWz,hWzp,hEz,hEzp,hGz,hGzp,hPz,hPzp,hOz,hOzp⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalStarCores -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- ORIGINAL Parity §4.6 real PRIME-SLOT endpoint identification on
actual two-ended h=-2 Q/P/B509 source, with BOTH original fine
alpha cofactor endpoints W-rough. At z=m'v, z'=z+2k=m v', the
ordinary parts are LITERALLY

  zStar = m'*vStar,  z'Star = m*v'Star,

where vStar and v'Star are the SAME original reserved-Q/skipped-Q
physical integer witnesses from e*vStar=ord_P(mn-2) and its other
endpoint, NOT arbitrary P-free cofactor replacements.

Hence the b633PrimeRest/prime-slot core target arguments are EXACT:
  zStar/m' = original vStar, z'Star/m = original v'Star.

All source signed ε/W1 invariances were separately proved; no
hypothetical (4.17) core saving or enlarged support is assumed. -/
theorem parity_original_historical_physical_source_star_two_cores434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hm : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hmp : sourceD20Rough (Real.exp (Real.sqrt L)) mp) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    ∃ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      ∃ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
        ∃ vs ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
          d L band slot δ e u,
          ∃ vps ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
            d L band slot δ e up,
          sourceOriginalOrdinaryPart P z = mp*vs ∧
          sourceOriginalOrdinaryPart P zp = m*vps ∧
          sourceOriginalOrdinaryPart P z/mp = vs ∧
          sourceOriginalOrdinaryPart P zp/m = vps := by
  dsimp only
  let G := sourceOriginalPAllActualBands 20 L
  let P := Finset.univ.biUnion G
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*k).toNat
  let v := parityOriginalHistoricalCanonicalV434 e m n
  let vp := parityOriginalHistoricalCanonicalV434 e mp n
  have hSource := hValid
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hValid
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hmn := (Finset.mem_filter.mp hu).2.2.2
  have hmpn := (Finset.mem_filter.mp hup).2.2.2
  have hg := (Finset.mem_filter.mp hvs).2
  have hgp := (Finset.mem_filter.mp hvps).2
  have hPrimeP : ∀p∈P,p.Prime := by
    intro p hp
    obtain ⟨g,hg0,hpg⟩ := Finset.mem_biUnion.mp hp
    exact (parity_original_actual_full_P_prime_rough_cap434 L hL g p hpg).1
  have hV := parity_original_historical_canonical_v_eq_source_physical434
    L e m n u vs he.pos huPos hmn hg
  have hVp := parity_original_historical_canonical_v_eq_source_physical434
    L e mp n up vps he.pos hupPos hmpn hgp
  have hVstar : sourceOriginalOrdinaryPart P v=vs := by
    change sourceOriginalOrdinaryPart P (parityOriginalHistoricalCanonicalV434 e m n) = vs
    rw [hV]
    exact parity_original_source_vStar_eq_ordinary_physical_v434
      P u e vs huPos.ne' hPrimeP hg
  have hVpstar : sourceOriginalOrdinaryPart P vp=vps := by
    change sourceOriginalOrdinaryPart P (parityOriginalHistoricalCanonicalV434 e mp n) = vps
    rw [hVp]
    exact parity_original_source_vStar_eq_ordinary_physical_v434
      P up e vps hupPos.ne' hPrimeP hgp
  have hInv := parity_original_historical_physical_two_endpoint_P_invariance434
    d L hL band slot δ Y e m mp n he hneq hSource hm hmp false
  dsimp only at hInv
  obtain ⟨hW1,hW2,hE1,hE2,hG1,hG2,hP1,hP2,hO1,hO2⟩ := hInv
  have hStarZ : sourceOriginalOrdinaryPart P z=mp*vs := by
    calc
      _ = mp*sourceOriginalOrdinaryPart P v := hO1
      _ = mp*vs := by rw [hVstar]
  have hStarZp : sourceOriginalOrdinaryPart P zp=m*vps := by
    calc
      _ = m*sourceOriginalOrdinaryPart P vp := hO2
      _ = m*vps := by rw [hVpstar]
  have hmPos : 0 < m := by have hh := hm.1; omega
  have hmpPos : 0 < mp := by have hh := hmp.1; omega
  have hQuotZ : sourceOriginalOrdinaryPart P z/mp=vs := by
    rw [hStarZ]
    exact Nat.mul_div_cancel_left vs hmpPos
  have hQuotZp : sourceOriginalOrdinaryPart P zp/m=vps := by
    rw [hStarZp]
    exact Nat.mul_div_cancel_left vps hmPos
  exact ⟨u,hu,up,hup,vs,hvs,vps,hvps,hStarZ,hStarZp,hQuotZ,hQuotZp⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Original physical z-image restricted to ACTUAL nonzero two-gated
source n fibres, not the oversized image of all formal J elements.
It retains the exact canonical z=m'*(m*n-2)/e and the original
m,m',e and full Q/P source data on both endpoints. -/
def parityOriginalHistoricalPhysicalValidZSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (parityOriginalHistoricalCanonicalZSupport434 e m mp J).filter
    (fun z => ((parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp)).Nonempty)

/-- The full signed original k,z source sum can be restricted to its
ACTUAL physical n and z carriers without altering complex coefficients.
There is no hidden multiplicity, loss of a Fourier phase or use of
signed cancellation to justify throwing away unsupported z. -/
theorem parity_original_historical_k_z_sum_physical_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) :
    (∑ z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
       ∑ n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp) =
    ∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
      ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  let V : ℕ → Prop :=
    parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp
  let Jz : ℕ → Finset ℕ :=
    parityOriginalHistoricalCanonicalZNFibre434 e m mp J
  have hOne (z : ℕ) :
      (∑n∈Jz z,parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp) =
      ∑n∈(Jz z).filter V,
        parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp :=
    parity_original_historical_offdiag_N_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp (Jz z)
  calc
    _ = ∑ z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        ∑n∈(Jz z).filter V,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hOne z
    _ = ∑ z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        if ((Jz z).filter V).Nonempty then
          (∑n∈(Jz z).filter V,
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hv : ((Jz z).filter V).Nonempty
      · simp only [if_pos hv]
      · have hempty : ((Jz z).filter V) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hv
        simp [hv,hempty]
    _ = _ := by
      unfold parityOriginalHistoricalPhysicalValidZSupport434
      rw [Finset.sum_filter]

/-- Every z on the TRUE physical offdiagonal source support is
strictly positive, as is z+2k, and the original canonical k is
nonzero, provided original e is odd and the offdiagonal m≠m'.
This is a SOURCE statement on full selected Q/P endpoints and not
an unsupported extension to the pre-filtered image. -/
theorem parity_original_historical_physical_supported_z_and_shift_pos434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) (z : ℕ)
    (he : Odd e) (hneq : m≠mp)
    (hz : z∈parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ Y e m mp J) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    k≠0 ∧ 0<z ∧ 0<(z:ℤ)+2*k := by
  dsimp only
  have hzHas := (Finset.mem_filter.mp hz).2
  obtain ⟨n,hn⟩ := hzHas
  have hnZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hnV := (Finset.mem_filter.mp hn).2
  have hPos := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m mp n he hneq hnV
  rw [hnZ] at hPos
  exact hPos

/-- Every actual physical z in the true source carrier has a UNIQUE
possible original n. Thus the original final Parity (4.17) z sum never
pays an arbitrary #J multiplicity at fixed e,m,m' after source filters. -/
theorem parity_original_historical_physical_supported_z_fibre_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) (z : ℕ)
    (he : 0 < e) (hmp : 0 < mp) :
    ((parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp)).card ≤ 1 :=
  parity_original_historical_supported_canonical_z_fibre_card_le_one434
    d L band slot δ Y e m mp he hmp J z

/-- Exact original full historical active e-window k,z offdiagonal
with ALL unsupported u,u',Q/B509,z/n entries eliminated at zero
complex cost. No character mask has yet been inserted and no TypeII
saving is inferred from this equality alone. -/
def parityOriginalHistoricalActiveCauchyOffdiagPhysicalKZ434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ m∈K,
      ∑ k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
              (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

/-- Actual signed original Cauchy offdiagonal equals TRUE physical
k,z support, not the formal image containing spurious zero amplitudes.
This proof joins the verified full active k,z reindex with the exact
zero-amplitude physical filter before mask orthogonality. -/
theorem parity_eventually_original_historical_active_offdiag_eq_physical_k_z434 :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      parityOriginalHistoricalActiveCauchyOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y =
      parityOriginalHistoricalActiveCauchyOffdiagPhysicalKZ434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y := by
  filter_upwards [parity_eventually_original_historical_active_offdiag_eq_k_z434]
    with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ E rho K J α signed Y
  rw [h.2 band slot δ ξ E rho K J α signed Y]
  unfold parityOriginalHistoricalActiveCauchyOffdiagKZ434
    parityOriginalHistoricalActiveCauchyOffdiagPhysicalKZ434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro mp hmp
  exact parity_original_historical_k_z_sum_physical_filter_exact434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
    Y e m mp J
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedFineMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Source-backed historical Parity (4.13) k / (2.6) character mask
on every PHYSICALLY NONZERO canonical z fibre, for the real original
b629 fine alpha coefficients at BOTH rough cofactors m,m'.
The original m*n=u+2, m'*n=u'+2, e*vStar and e*vStar' gates are
extracted from the physically restricted z carrier, not assumed.
The canonical k is the UNIQUE quotient (m'-m)/e. -/
theorem parity_eventually_original_historical_supported_fine_mask_at_z434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U E : ℝ) (K J : Finset ℕ)
        (e m mp z : ℕ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp J →
      ∀ (prime : Bool) (lFine uFine : ℕ), 2≤lFine →
        Real.exp (beta*L)≤(lFine:ℝ) →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp ≠ 0 →
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      k≠0 ∧ (k.natAbs:ℝ)<L^(K0+88) ∧ Even k ∧
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))))=1 ∧
        0<z ∧ 0<(z:ℤ)+2*k := by
  filter_upwards [parity_eventually_original_historical_gated_fine_offdiag_k_source434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ U E K J e m mp z hU hScale hmLo hmHi
    hmpLo hmpHi he hm hmp hz prime lFine uFine hl hFineLow hα hαp
  have hHas := (Finset.mem_filter.mp hz).2
  obtain ⟨n,hn⟩ := hHas
  have hnZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hnJ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := (Finset.mem_filter.mp hn).2
  have hFine := h.2 band slot δ U E K J e n m mp u up vs vps
    hU hScale hmLo hmHi hmpLo hmpHi he hnJ hm hmp hu hup hvs hvps
    prime lFine uFine hl hFineLow hα hαp
  dsimp only at hFine ⊢
  obtain ⟨k,hk,hmpm,hvpv,hdet,hzpEq,hRank,hEven,hMask,hZpos,hZpPos⟩ := hFine
  have hneq : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have hepos : 0<e := by
    by_contra hnon
    have he0 : e=0 := Nat.eq_zero_of_not_pos hnon
    rw [he0] at hmpm
    have hEq : m=mp := by omega
    exact hneq hEq
  have hkCanon := parity_original_historical_physical_k_eq_quotient434
    e m mp hepos k hmpm
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hgate := (Finset.mem_filter.mp hvs).2
  have hZEq := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n u vs hepos huPos (Finset.mem_filter.mp hu).2.2.2 hgate
  have hzEq : z=mp*(vs*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := by
    rw [←hnZ]
    exact hZEq
  have hzInt : (z:ℤ)=(mp:ℤ)*
      ((vs*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u):ℤ) := by
    exact_mod_cast hzEq
  have hZpos' : 0<z := by
    rw [hzEq]
    exact_mod_cast hZpos
  have hZpPos' : 0<(z:ℤ)+2*k := by
    rw [hzInt]
    exact hZpPos
  rw [hkCanon]
  exact ⟨hk,hRank,hEven,hMask,hZpos',hZpPos'⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedMaskInsert -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The EXACT original Parity (2.6) character-mask identity is inserted
into an arbitrary genuine complex source coefficient, WITHOUT first
bounding the ℓ1 mass. The hypothesis must be independently proved
from the real source unit/rough arithmetic; this theorem assumes no
identity on unsupported integer pairs. -/
theorem parity_original_exact_mask_insert_complex434
    (k : ℤ) (m mp : ℕ) (w : ℂ)
    (hMask : (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) = 1) :
    w = ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      (parityShiftTwoMaskCoefficient434 k.natAbs chi *
        chi (mp : ZMod (2*k.natAbs)) *
        star (chi (m : ZMod (2*k.natAbs)))) * w := by
  rw [←Finset.sum_mul,hMask]
  simp

/-- EXACT character orthogonality inserted into one complete original
physical z fibre with the actual b629 fine-cell α_m,α_m'. On the
unrestricted original formal k,z image the mask need not hold. Here
e,m,m',z and canonical k are source-filtered and the two endpoint
physical Q/P carriers are really inhabited. If either fine alpha is
zero, the entire SOURCE fibre is identically zero and stays zero.
No ℓ1 bound is applied until AFTER this identity. -/
theorem parity_eventually_original_supported_z_fine_character_mask_insert434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ) (signed prime : Bool)
        (lFine uFine e m mp z : ℕ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp J →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      let W := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m mp),
        parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
          ⌊2*Real.exp L⌋₊ e n m mp
      W = ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        (parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs)))) * W := by
  filter_upwards [parity_eventually_original_historical_supported_fine_mask_at_z434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ U E rho K J signed prime lFine uFine
    e m mp z hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let W : ℂ := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
    (parityOriginalHistoricalPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp),
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
      ⌊2*Real.exp L⌋₊ e n m mp
  change W = ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
    (parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) * W
  by_cases ham : alpha m=0
  · have hW : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp only [ham,zero_mul,mul_zero,Finset.sum_const_zero]
    rw [hW]
    simp
  by_cases hamp : alpha mp=0
  · have hW : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp only [hamp,zero_mul,mul_zero,star_zero,Finset.sum_const_zero]
    rw [hW]
    simp
  have hActual := h.2 band slot δ U E K J e m mp z
    hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    prime lFine uFine hl hFineLow ham hamp
  dsimp only at hActual
  have hMask := hActual.2.2.2.1
  exact parity_original_exact_mask_insert_complex434 k m mp W hMask
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- True ORIGINAL signed historical Cauchy offdiagonal after exact
Parity (2.6) character orthogonality, with the actual selected e-window,
nonzero source k, true canonical z, both Q/P physical gates and
fine-cell α. The character sum is OUTSIDE z,n but NOT yet outside
m,m' and k; no source equality or cancellation is assumed on formal
unsupported z. This is precisely the prerequisite for (4.16). -/
def parityOriginalHistoricalActiveCauchyOffdiagMaskedKZ434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ m∈K,
      ∑ k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
              (parityShiftTwoMaskCoefficient434 k.natAbs chi *
                chi (mp : ZMod (2*k.natAbs)) *
                star (chi (m : ZMod (2*k.natAbs)))) *
              (∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
                (parityOriginalHistoricalPhysicalValidN434
                  d L band slot δ Y e m mp),
                parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp)

/-- The FULL actual original h=-2 Cauchy offdiagonal from signed
sourceOriginalA equals the full CHARACTER-resolved physical k,z
correlation sum for original canonical b629 fine alpha and the true
historical e-window. The proof inserts orthogonality only after
source-proved unit/roughness and both original physical Q/P gates.
NO ℓ1 bound has yet been used, so no factor #characters appears. -/
theorem parity_eventually_original_historical_active_fine_offdiag_eq_masked_k_z434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      (∀ m∈K, U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      parityOriginalHistoricalActiveCauchyOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ =
      parityOriginalHistoricalActiveCauchyOffdiagMaskedKZ434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ := by
  filter_upwards [parity_eventually_original_historical_active_offdiag_eq_physical_k_z434,
    parity_eventually_original_supported_z_fine_character_mask_insert434
      S beta gamma K0 hS hbeta hgamma] with L hPhys hMask
  refine ⟨hPhys.1,?_⟩
  intro band slot δ ξ U E rho K J prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  rw [hPhys.2 band slot δ ξ E rho K J alpha signed ⌊2*Real.exp L⌋₊]
  unfold parityOriginalHistoricalActiveCauchyOffdiagPhysicalKZ434
    parityOriginalHistoricalActiveCauchyOffdiagMaskedKZ434
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
  have hPoint := hMask.2 band slot δ ξ U E rho K J signed prime
    lFine uFine e m mp z hU hScale hmD.1 hmD.2 hmpD.1 hmpD.2
    he hm hmpMem hz hl hFineLow
  dsimp only at hPoint
  rw [hkCanon] at hPoint
  exact hPoint
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCharacterOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact finite Parity (2.6) CHARACTER-OUTER reindex with true
m'->z-dependent physical support. This is no independent Cartesian
z support and introduces no #characters. Mask coefficients are
moved to the outside by finite distributivity only, not by a norm. -/
theorem parity_original_character_outer_finite_fubini434
    {ι : Type} [DecidableEq ι] (M : Finset ℕ) (Q : Finset ι)
    (Z : ℕ → Finset ℕ) (c : ι → ℂ) (f : ι → ℕ → ℂ)
    (w : ℕ → ℕ → ℂ) :
    (∑ mp∈M,∑ z∈Z mp,∑ chi∈Q,
      (c chi*f chi mp)*w mp z) =
      ∑ chi∈Q,c chi*(∑ mp∈M,f chi mp*(∑ z∈Z mp,w mp z)) := by
  classical
  calc
    _ = ∑mp∈M,∑chi∈Q,∑z∈Z mp,
          (c chi*f chi mp)*w mp z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact Finset.sum_comm
    _ = ∑chi∈Q,∑mp∈M,∑z∈Z mp,
          (c chi*f chi mp)*w mp z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mp hmp
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring

/-- True source Parity (4.13)--(4.16) with each ORIGINAL CHARACTER
OUTSIDE m', z and n for the full active e-window and canonical k.
The coefficient `c_chi*conj(chi(m))` remains separate from m' and
original b629 fine alpha; chi(m') remains inside the true cofactor
sum. This is the required position before original (4.17).
No Fourier ℓ1 bound or analytic cancellation is smuggled in. -/
def parityOriginalHistoricalActiveCauchyOffdiagCharacterOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ m∈K,
      ∑ k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          (parityShiftTwoMaskCoefficient434 k.natAbs chi *
            star (chi (m : ZMod (2*k.natAbs)))) *
          (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
            chi (mp : ZMod (2*k.natAbs)) *
              (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
                d L band slot δ Y e m mp J,
                ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
                  (parityOriginalHistoricalPhysicalValidN434
                    d L band slot δ Y e m mp),
                  parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                    d L band slot δ ξ rho α signed Y e n m mp))

/-- Source-faithful original signed after-mask finite Fubini. In
particular the Dirichlet character is NOT applied to the unsigned
odd-parity projector and no character count is paid before using the
source-proven (2.6) ℓ1 mask bound. -/
theorem parity_original_historical_masked_k_z_eq_character_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalActiveCauchyOffdiagMaskedKZ434
      d L E band slot δ ξ rho K J α signed Y =
    parityOriginalHistoricalActiveCauchyOffdiagCharacterOuter434
      d L E band slot δ ξ rho K J α signed Y := by
  unfold parityOriginalHistoricalActiveCauchyOffdiagMaskedKZ434
    parityOriginalHistoricalActiveCauchyOffdiagCharacterOuter434
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
      d L band slot δ Y e m mp J
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      star (chi (m : ZMod (2*k.natAbs)))
  let f : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
    fun chi mp => chi (mp : ZMod (2*k.natAbs))
  let w : ℕ → ℕ → ℂ := fun mp z =>
    ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  change (∑mp∈M,∑z∈Z mp,∑chi∈Q,
    (parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) * w mp z) =
    ∑chi∈Q,c chi*(∑mp∈M,f chi mp*(∑z∈Z mp,w mp z))
  calc
    _ = ∑mp∈M,∑z∈Z mp,∑chi∈Q,(c chi*f chi mp)*w mp z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro chi hchi
      dsimp [c,f]
      ring
    _ = _ := parity_original_character_outer_finite_fubini434 M Q Z c f w

/-- Actual original r20 signed fine-cell Cauchy offdiagonal is
exactly its historical k,z character-outer expression, retaining
original m' and physical u/u', e*vStar Q/P supports and chi modulus
2|k|. Orthogonality has been used BEFORE any ℓ1 estimate. -/
theorem parity_eventually_original_historical_active_fine_offdiag_eq_character_outer434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      (∀ m∈K, U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      parityOriginalHistoricalActiveCauchyOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ =
      parityOriginalHistoricalActiveCauchyOffdiagCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ := by
  filter_upwards [parity_eventually_original_historical_active_fine_offdiag_eq_masked_k_z434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ U E rho K J prime signed lFine uFine
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [h.2 band slot δ ξ U E rho K J prime signed lFine uFine
    hU hScale hDyad hl hFineLow]
  exact parity_original_historical_masked_k_z_eq_character_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed ⌊2*Real.exp L⌋₊
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCharacterBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Sharp h=-2 ORIGINAL character loss bound AFTER the source-true
orthogonality (2.6) and after the original conjugate chi(m) has been
kept at its proper cofactor. The full character mask costs ≤1,
uniformly in the physical signed modulus 2|k|. No φ(Q) loss and no
assumption of chi(m) being a unit on an unsupported m. -/
theorem parity_original_character_outer_mask_no_count_loss434
    (k : ℤ) (hk : k≠0) (m : ℕ)
    (F : DirichletCharacter ℂ (2*k.natAbs) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hF : ∀ chi : DirichletCharacter ℂ (2*k.natAbs),‖F chi‖≤M) :
    ‖∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      (parityShiftTwoMaskCoefficient434 k.natAbs chi *
        star (chi (m : ZMod (2*k.natAbs)))) * F chi‖ ≤ M := by
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityShiftTwoMaskCoefficient434 k.natAbs chi
  have hunit (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      ‖star (chi (m : ZMod (2*k.natAbs)))‖ ≤ 1 := by
    simpa only [norm_star] using
      (DirichletCharacter.norm_le_one chi (m : ZMod (2*k.natAbs)))
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖(c chi*star (chi (m : ZMod (2*k.natAbs))))*F chi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖c chi‖*M := by
      apply Finset.sum_le_sum
      intro chi hchi
      rw [norm_mul,norm_mul]
      calc
        ‖c chi‖*‖star (chi (m : ZMod (2*k.natAbs)))‖*‖F chi‖ ≤
          (‖c chi‖*1)*‖F chi‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hunit chi) (norm_nonneg _))
              (norm_nonneg _)
        _ ≤ (‖c chi‖*1)*M :=
            mul_le_mul_of_nonneg_left (hF chi)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ = ‖c chi‖*M := by ring
    _ = M*(∑ chi : DirichletCharacter ℂ (2*k.natAbs),‖c chi‖) := by
      rw [←Finset.sum_mul]
      ring
    _ ≤ M*1 := mul_le_mul_of_nonneg_left
      (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = M := mul_one M

/-- The norm of the original full physical character-outer term for
ONE actual canonical nonzero k and original e,m is bounded by a
uniform bound for the GENUINE m',z,n twisted source sum, with zero
additional character-count loss. This is the exact needed point in
the Parity TypeII proof AFTER the character identity is inserted. -/
theorem parity_original_historical_physical_k_character_budget434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e m : ℕ) (k : ℤ) (hk : k≠0)
    (M : ℝ) (hM : 0≤M)
    (hEach : ∀ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        chi (mp : ZMod (2*k.natAbs)) *
          (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
              (parityOriginalHistoricalPhysicalValidN434
                d L band slot δ Y e m mp),
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)‖≤M) :
    ‖∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      (parityShiftTwoMaskCoefficient434 k.natAbs chi *
        star (chi (m : ZMod (2*k.natAbs)))) *
      (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        chi (mp : ZMod (2*k.natAbs)) *
          (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
              (parityOriginalHistoricalPhysicalValidN434
                d L band slot δ Y e m mp),
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp))‖ ≤ M :=
  parity_original_character_outer_mask_no_count_loss434 k hk m _ M hM hEach
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedZProducts -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- TWO exact historical Parity(4.13) z-product equalities directly from
the ORIGINAL selected Q e and physical Ppart gates, with every prime
power retained:
  e*z=m'*u,  e*(z+2k)=m*u',
where u=m*n-2, u'=m'*n-2, z=m'v and k=(m'-m)/e.
The source proof does not introduce any new v or assume a product
factorization outside the true inhabited Q/B509 physical fibres. -/
theorem parity_original_historical_supported_z_exact_two_products434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hn : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    ∃ u up : ℕ,
      u∈parityOriginalHistoricalFixedMNUSupport434 Y m n ∧
      up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n ∧
      e*z=mp*u ∧
      (e:ℤ)*((z:ℤ)+2*k)=(m:ℤ)*(up:ℤ) := by
  dsimp only
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hn
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have h1 := (Finset.mem_filter.mp hu).2.2.2
  have h2 := (Finset.mem_filter.mp hup).2.2.2
  have hgate := (Finset.mem_filter.mp hvs).2
  have hgatep := (Finset.mem_filter.mp hvps).2
  have hZ := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n u vs he.pos huPos h1 hgate
  have hShift := parity_original_historical_canonical_z_plus_two_k_source434
    L e m mp n u up vs vps he huPos hupPos hgate hgatep h1 h2 hneq
  have hEU : e*(vs*sourceOriginalPPrimePart P u)=u := by
    calc
      _ = (e*vs)*sourceOriginalPPrimePart P u := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u*sourceOriginalPPrimePart P u := by rw [hgate]
      _ = u := source_original_ordinary_times_P_part P u huPos.ne'
  have hEUP : e*(vps*sourceOriginalPPrimePart P up)=up := by
    calc
      _ = (e*vps)*sourceOriginalPPrimePart P up := by ac_rfl
      _ = sourceOriginalOrdinaryPart P up*sourceOriginalPPrimePart P up := by rw [hgatep]
      _ = up := source_original_ordinary_times_P_part P up hupPos.ne'
  have hFirst : e*parityOriginalHistoricalCanonicalZ434 e m mp n=mp*u := by
    rw [hZ]
    calc
      e*(mp*(vs*sourceOriginalPPrimePart P u)) =
        mp*(e*(vs*sourceOriginalPPrimePart P u)) := by ac_rfl
      _ = mp*u := by rw [hEU]
  have hEUPcast : (e:ℤ)*
      ((vps:ℤ)*(sourceOriginalPPrimePart P up:ℤ))=(up:ℤ) := by
    simpa only [Nat.cast_mul] using (congrArg (fun t : ℕ => (t:ℤ)) hEUP)
  have hSecond : (e:ℤ)*
      ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
        2*parityOriginalHistoricalOffdiagK434 e m mp)=(m:ℤ)*(up:ℤ) := by
    dsimp only at hShift
    rw [hShift]
    calc
      _ = (m:ℤ)*((e:ℤ)*((vps:ℤ)*(sourceOriginalPPrimePart P up:ℤ))) := by ring
      _ = (m:ℤ)*(up:ℤ) := by rw [hEUPcast]
  exact ⟨u,up,hu,hup,hFirst,hSecond⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedZDyadic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ACTUAL original Parity (4.13)-(4.15) physical source z-scale from
true historical E=U L^-K0 and E L^-88<=e<=E, TWO real m' dyadic
bounds, positive physical u~exp L, and the exact source e*z=m'*u.
No guessed z~xL^K0 or independent Z cutoff is inserted: both
inequalities are literal algebraic consequences of source data. -/
theorem parity_original_historical_physical_z_real_scale434
    (L U E K0 : ℝ) (e mp u z : ℕ)
    (hL : 0<L) (hU : 0<U) (hE : E=U*L^(-K0))
    (hwin : parityOriginalHistoricalEWindow434 L E e)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (huLo : Real.exp L/2≤(u:ℝ)) (huHi : (u:ℝ)≤2*Real.exp L)
    (hEz : e*z=mp*u) :
    (Real.exp L/2)*L^K0 ≤ (z:ℝ) ∧
    (z:ℝ) ≤ 4*Real.exp L*L^(K0+88) := by
  have hX : 0<Real.exp L := Real.exp_pos L
  have hKpos : 0<L^K0 := Real.rpow_pos_of_pos hL _
  have hInvpos : 0<L^(-K0) := Real.rpow_pos_of_pos hL _
  have h88pos : 0<L^(-88:ℝ) := Real.rpow_pos_of_pos hL _
  have hEpos : 0<E := by rw [hE];exact mul_pos hU hInvpos
  have hepos : 0<(e:ℝ) :=
    (mul_pos hEpos h88pos).trans_le hwin.1
  have hEzR : (e:ℝ)*(z:ℝ)=(mp:ℝ)*(u:ℝ) := by exact_mod_cast hEz
  have hPair : L^(-K0)*L^K0=1 := by
    rw [←Real.rpow_add hL]
    simp
  have hTriple : L^(-K0)*L^(-88:ℝ)*L^(K0+88)=1 := by
    calc
      _ = (L^(-K0)*L^(-88:ℝ))*L^(K0+88) := by ring
      _ = L^(-K0+(-88:ℝ))*L^(K0+88) := by rw [←Real.rpow_add hL]
      _ = L^((-K0+(-88:ℝ))+(K0+88)) := by rw [←Real.rpow_add hL]
      _ = 1 := by
        have hx : -K0+(-88:ℝ)+(K0+88)=0 := by ring
        rw [hx,Real.rpow_zero]
  have hED : E*L^K0=U := by
    calc
      _ = U*(L^(-K0)*L^K0) := by rw [hE];ring
      _ = U := by rw [hPair];ring
  have hC : (E*L^(-88:ℝ))*L^(K0+88)=U := by
    calc
      _ = U*(L^(-K0)*L^(-88:ℝ)*L^(K0+88)) := by rw [hE];ring
      _ = U := by rw [hTriple];ring
  have hLoProd : U*(Real.exp L/2)≤(mp:ℝ)*(u:ℝ) := by
    exact mul_le_mul hmpLo huLo (by positivity) (by positivity)
  have hLoMult : ((Real.exp L/2)*L^K0)*(e:ℝ)≤(e:ℝ)*(z:ℝ) := by
    calc
      _ ≤ ((Real.exp L/2)*L^K0)*E :=
        mul_le_mul_of_nonneg_left hwin.2 (by positivity)
      _ = U*(Real.exp L/2) := by rw [show ((Real.exp L/2)*L^K0)*E =
          (Real.exp L/2)*(E*L^K0) by ring,hED];ring
      _ ≤ (mp:ℝ)*(u:ℝ) := hLoProd
      _ = (e:ℝ)*(z:ℝ) := hEzR.symm
  have hLow : (Real.exp L/2)*L^K0 ≤ (z:ℝ) :=
    le_of_mul_le_mul_right (by simpa only [mul_comm] using hLoMult) hepos
  have hHiProd : (mp:ℝ)*(u:ℝ) ≤ (2*U)*(2*Real.exp L) := by
    exact mul_le_mul hmpHi huHi (by positivity) (by positivity)
  have hHiMult : (E*L^(-88:ℝ))*(z:ℝ) ≤ 4*U*Real.exp L := by
    calc
      _ ≤ (e:ℝ)*(z:ℝ) :=
        mul_le_mul_of_nonneg_right hwin.1 (Nat.cast_nonneg _)
      _ = (mp:ℝ)*(u:ℝ) := hEzR
      _ ≤ (2*U)*(2*Real.exp L) := hHiProd
      _ = 4*U*Real.exp L := by ring
  have hCoeffPos : 0<E*L^(-88:ℝ) := mul_pos hEpos h88pos
  have hCoeffUpper :
      (E*L^(-88:ℝ))*(4*Real.exp L*L^(K0+88))=4*U*Real.exp L := by
    calc
      _ = 4*Real.exp L*((E*L^(-88:ℝ))*L^(K0+88)) := by ring
      _ = 4*Real.exp L*U := by rw [hC]
      _ = 4*U*Real.exp L := by ring
  have hUpper : (z:ℝ) ≤4*Real.exp L*L^(K0+88) := by
    apply le_of_mul_le_mul_left (a := E*L^(-88:ℝ)) (a0 := hCoeffPos)
    calc
      _ ≤ 4*U*Real.exp L := hHiMult
      _ = (E*L^(-88:ℝ))*(4*Real.exp L*L^(K0+88)) := hCoeffUpper.symm
  exact ⟨hLow,hUpper⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedZSourceDyadic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Historical Parity(4.13) real z dyadic growth, from the ACTUAL SOURCE
positive m*n=u+2 fibre and true m∈[U,2U), n∈[V,2V), U*V>=exp L.
The source upper restriction u<=floor(2exp L) and E-window are
retained. No smooth Z cutoff, Fourier factor, or unproved norm estimate
is introduced in this quantitative source geometry. -/
theorem parity_original_historical_actual_u_source_z_dyadic434
    (L U V E K0 : ℝ) (e m mp n u z : ℕ)
    (hL : 4≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (hmLo : U≤(m:ℝ)) (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hnLo : V≤(n:ℝ))
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434
      ⌊2*Real.exp L⌋₊ m n)
    (hEz : e*z=mp*u) :
    (Real.exp L/2)*L^K0 ≤ (z:ℝ) ∧
    (z:ℝ) ≤ 4*Real.exp L*L^(K0+88) := by
  have hLp : 0<L := by linarith
  have hmn := (Finset.mem_filter.mp hu).2.2.2
  have hmnR : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast hmn
  have hProdLo : Real.exp L ≤ (m:ℝ)*(n:ℝ) := by
    calc
      _ ≤ U*V := hUV
      _ ≤ (m:ℝ)*(n:ℝ) :=
        mul_le_mul hmLo hnLo (by positivity) (by positivity)
  have hX4 : (4:ℝ) ≤ Real.exp L := by
    have hexp := Real.add_one_le_exp L
    linarith
  have huLo : Real.exp L/2 ≤ (u:ℝ) := by
    linarith [hProdLo,hmnR,hX4]
  have huHi : (u:ℝ) ≤ 2*Real.exp L := by
    calc
      _ ≤ (⌊2*Real.exp L⌋₊:ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).2
      _ ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  exact parity_original_historical_physical_z_real_scale434
    L U E K0 e mp u z hLp hU hE hWin hmpLo hmpHi.le huLo huHi hEz

/-- The SAME quantitative Parity z range for the true FULL original
physically SUPPORTED canonical z image. This takes the actual source
u,u',vStar,vStar' witnesses from the filtered complex Cauchy carrier,
then uses e*z=m'*u and the real original m/n dyadic hypotheses.
No erroneous estimate for unsupported floor quotients is claimed. -/
theorem parity_original_historical_physical_supported_z_source_dyadic434
    (d : ℕ) (L U V E K0 : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (J : Finset ℕ) (e m mp z : ℕ)
    (hL : 4≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (he : Odd e) (hneq : m≠mp)
    (hmLo : U≤(m:ℝ)) (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hnLo : ∀ n∈J,V≤(n:ℝ))
    (hz : z∈parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m mp J) :
    (Real.exp L/2)*L^K0 ≤ (z:ℝ) ∧
    (z:ℝ) ≤ 4*Real.exp L*L^(K0+88) := by
  obtain ⟨n,hn⟩ := (Finset.mem_filter.mp hz).2
  have hnJ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hnValid := (Finset.mem_filter.mp hn).2
  obtain ⟨u,up,hu,hup,hEz,hEzp⟩ :=
    parity_original_historical_supported_z_exact_two_products434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m mp n he hneq hnValid
  have hCanonicalZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hProd : e*z=mp*u := by
    rw [←hCanonicalZ]
    exact hEz
  exact parity_original_historical_actual_u_source_z_dyadic434
    L U V E K0 e m mp n u z hL hU hV hUV hE hWin
    hmLo hmpLo hmpHi (hnLo n hnJ) hu hProd
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSupportedSourceEnvelope -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Complete ORIGINAL source-supported Parity (4.13)--(4.17)
arithmetic/dyadic pre-character envelope at the fine-cell b629 data:
  * source canonical nonzero EVEN k, |k|<L^(K0+88),
  * exact Dirichlet character mask identity modulo 2|k|,
  * original physical 0<z and 0<z+2k,
  * true historical Z polynomial window
      exp(L)*L^K0/2 <= z <= 4*exp(L)*L^(K0+88).
The input is the ACTUAL b629 fine α, true r20 Q/P physical source,
E=U L^-K0, selected e-window E L^-88<=e<=E, real m,n dyads,
U*V>=exp(L), and positive u≤floor(2exp(L)).
No extra source σ, smooth dyadic partition or analytic bound is used. -/
theorem parity_eventually_original_historical_supported_fine_k_z_envelope434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U V E : ℝ) (K J : Finset ℕ)
        (e m mp z : ℕ),
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      (∀ n∈J,V≤(n:ℝ)) →
      e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp J →
      ∀ (prime : Bool) (lFine uFine : ℕ), 2≤lFine →
        Real.exp (beta*L)≤(lFine:ℝ) →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp ≠ 0 →
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      k≠0 ∧ Even k ∧ (k.natAbs:ℝ)<L^(K0+88) ∧
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))))=1 ∧
        0<z ∧ 0<(z:ℤ)+2*k ∧
        (Real.exp L/2)*L^K0≤(z:ℝ) ∧
        (z:ℝ)≤4*Real.exp L*L^(K0+88) := by
  filter_upwards [parity_eventually_original_historical_supported_fine_mask_at_z434
      S beta gamma K0 hS hbeta hgamma,
    parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hMask hOdd
  refine ⟨hMask.1,?_⟩
  intro band slot δ U V E K J e m mp z
    hU hV hUV hScale hmLo hmHi hmpLo hmpHi hnLo
    he hm hmp hz prime lFine uFine hl hFineLow hα hαp
  have heSource := (Finset.mem_filter.mp he).1
  have heWin := (Finset.mem_filter.mp he).2
  have heOdd : Odd e := (hOdd.2 band slot δ e heSource).1
  have hneq : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have hOriginal := hMask.2 band slot δ U E K J e m mp z
    hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    prime lFine uFine hl hFineLow hα hαp
  have hZrange := parity_original_historical_physical_supported_z_source_dyadic434
    (sourceOriginalLiteralDepth 20 L) L U V E K0 band slot δ
    J e m mp z hMask.1 hU hV hUV hScale heWin heOdd hneq
    hmLo hmpLo hmpHi hnLo hz
  dsimp only at hOriginal ⊢
  exact ⟨hOriginal.1,hOriginal.2.2.1,hOriginal.2.1,
    hOriginal.2.2.2.1,hOriginal.2.2.2.2.1,
    hOriginal.2.2.2.2.2,hZrange.1,hZrange.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPulledBack -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- First EXACT original Parity (4.14) e/U pullback, with the true
historical h=-2 source cofactor relation m'-m=e*k and actual
positive U,E. No smoothing or unproved Fourier lemma is needed. -/
theorem parity_original_historical_pullback_e_ratio434
    (U E : ℝ) (e m mp : ℕ) (k : ℤ)
    (hU : 0 < U) (hE : 0 < E) (hk : k≠0)
    (hshift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k) :
    (e:ℝ)/E = (U/((k:ℝ)*E))*
      (((mp:ℝ)/U)-((m:ℝ)/U)) := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  have hshiftR : (mp:ℝ)-(m:ℝ)=(e:ℝ)*(k:ℝ) := by exact_mod_cast hshift
  field_simp
  nlinarith [hshiftR]

/-- Second EXACT original Parity (4.14) n/V pullback in literal
rational cofactor variables. Both h=-2 SOURCE relations are retained:
  m*n=u+2, m'-m=e*k, e*z=m'*u.
The original 2/m source correction is essential and NOT discarded. -/
theorem parity_original_historical_pullback_n_ratio434
    (V : ℝ) (e m mp n u z : ℕ) (k : ℤ)
    (hV : 0 < V) (hm : 0 < m) (hmp : 0 < mp) (hk : k≠0)
    (hmn : m*n=u+2)
    (hshift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hEz : e*z=mp*u) :
    (n:ℝ)/V =
      ((z:ℝ)/((k:ℝ)*V))*
        ((1/(m:ℝ))-(1/(mp:ℝ)))+
      2/((m:ℝ)*V) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hmpR : (mp:ℝ)≠0 := by exact_mod_cast hmp.ne'
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  have hmnR : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast hmn
  have hshiftR : (mp:ℝ)-(m:ℝ)=(e:ℝ)*(k:ℝ) := by exact_mod_cast hshift
  have hEzR : (e:ℝ)*(z:ℝ)=(mp:ℝ)*(u:ℝ) := by exact_mod_cast hEz
  have hKey : (n:ℝ)*((m:ℝ)*(mp:ℝ)*(k:ℝ)) =
      (z:ℝ)*((mp:ℝ)-(m:ℝ))+2*(mp:ℝ)*(k:ℝ) := by
    calc
      _ = ((m:ℝ)*(n:ℝ))*((mp:ℝ)*(k:ℝ)) := by ring
      _ = ((u:ℝ)+2)*((mp:ℝ)*(k:ℝ)) := by rw [hmnR]
      _ = ((e:ℝ)*(z:ℝ))*(k:ℝ)+2*(mp:ℝ)*(k:ℝ) := by rw [hEzR];ring
      _ = (z:ℝ)*((mp:ℝ)-(m:ℝ))+2*(mp:ℝ)*(k:ℝ) := by rw [hshiftR];ring
  field_simp [hmR,hmpR,hkR,hV.ne']
  nlinarith [hKey]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLogPullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ACTUAL original Parity (4.14) first pulled-back smooth cutoff
in its literal log dyadic coordinates t1=log(m/U), t2=log(m'/U).
No fictitious Fourier character is introduced: the equality follows
from the source integer m'-m=e*k and e>0 only where supported. -/
theorem parity_original_historical_log_dyadic_e_pullback434
    (U E : ℝ) (e m mp : ℕ) (k : ℤ)
    (hU : 0 < U) (hE : 0 < E) (hm : 0 < m) (hmp : 0 < mp)
    (hk : k≠0) (hshift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k) :
    let t1 := Real.log ((m:ℝ)/U)
    let t2 := Real.log ((mp:ℝ)/U)
    (e:ℝ)/E = (U/((k:ℝ)*E))*(Real.exp t2-Real.exp t1) := by
  dsimp only
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hmpR : 0 < (mp:ℝ) := Nat.cast_pos.mpr hmp
  rw [Real.exp_log (div_pos hmpR hU),Real.exp_log (div_pos hmR hU)]
  exact parity_original_historical_pullback_e_ratio434 U E e m mp k hU hE hk hshift

/-- The true Parity (4.14) SECOND cutoff pullback, including the
necessary original h=-2 correction 2/(UV)*exp(-t1) and signed k.
The exponentials are *exactly* the source positive real log ratios
(m/U),(m'/U),(z/Z). No approximation, derivative estimate, Fourier
inversion or manufactured independent n is used here. -/
theorem parity_original_historical_log_dyadic_n_pullback434
    (U V Z : ℝ) (e m mp n u z : ℕ) (k : ℤ)
    (hU : 0 < U) (hV : 0 < V) (hZ : 0 < Z)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z)
    (hk : k≠0) (hmn : m*n=u+2)
    (hshift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hEz : e*z=mp*u) :
    let t1 := Real.log ((m:ℝ)/U)
    let t2 := Real.log ((mp:ℝ)/U)
    let t3 := Real.log ((z:ℝ)/Z)
    (n:ℝ)/V = (Z/((k:ℝ)*U*V))*Real.exp t3 *
      (Real.exp (-t1)-Real.exp (-t2))+
      (2/(U*V))*Real.exp (-t1) := by
  dsimp only
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hmpR : 0 < (mp:ℝ) := Nat.cast_pos.mpr hmp
  have hzR : 0 < (z:ℝ) := Nat.cast_pos.mpr hz
  have hM : Real.exp (-Real.log ((m:ℝ)/U)) = U/(m:ℝ) := by
    rw [Real.exp_neg,Real.exp_log (div_pos hmR hU)]
    field_simp
  have hMP : Real.exp (-Real.log ((mp:ℝ)/U)) = U/(mp:ℝ) := by
    rw [Real.exp_neg,Real.exp_log (div_pos hmpR hU)]
    field_simp
  rw [Real.exp_log (div_pos hzR hZ),hM,hMP]
  rw [parity_original_historical_pullback_n_ratio434 V e m mp n u z k hV hm hmp hk hmn hshift hEz]
  have hm0 : (m:ℝ)≠0 := ne_of_gt hmR
  have hmp0 : (mp:ℝ)≠0 := ne_of_gt hmpR
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk
  field_simp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSourceLogPullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- BOTH true historical Parity (4.14) log-coordinate pullbacks at an
ACTUAL supported original h=-2 Q/P physical Cauchy endpoint pair.
This establishes all arithmetic/positivity inputs from SOURCE:
`m*n=u+2`, `m'*n=u'+2`, exact e*vStar Q product gates,
unique nonzero k=(m'-m)/e, canonical positive z=m'v, and true
`e*z=m'*u`. No arbitrary e,n or z coefficients are postulated.
The original smooth-cutoff Fourier approximation is separate. -/
theorem parity_original_historical_supported_source_log_cutoff_pullbacks434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let t1 := Real.log ((m:ℝ)/U)
    let t2 := Real.log ((mp:ℝ)/U)
    let t3 := Real.log ((z:ℝ)/Z)
    (e:ℝ)/E = (U/((k:ℝ)*E))*(Real.exp t2-Real.exp t1) ∧
    (n:ℝ)/V = (Z/((k:ℝ)*U*V))*Real.exp t3 *
        (Real.exp (-t1)-Real.exp (-t2))+
        (2/(U*V))*Real.exp (-t1) := by
  dsimp only
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hValid
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hup).2
  have huPos : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0 < up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hg := (Finset.mem_filter.mp hvs).2
  have hgp := (Finset.mem_filter.mp hvps).2
  have hPhysical := parity_original_historical_actual_k_quotient_source434
    L e m mp n u up vs vps he huPos hupPos hg hgp
    h1.2.2 h2.2.2 hneq
  dsimp only at hPhysical
  have hk : parityOriginalHistoricalOffdiagK434 e m mp≠0 := hPhysical.1
  have hShift : (mp:ℤ)-(m:ℤ)=(e:ℤ)*parityOriginalHistoricalOffdiagK434 e m mp :=
    hPhysical.2.1
  have hZProd := parity_original_historical_supported_z_exact_two_products434
    d L band slot δ Y e m mp n he hneq
    ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩
  dsimp only at hZProd
  obtain ⟨u0,up0,hu0,hup0,hEz,hEzp⟩ := hZProd
  have hZActual : e*parityOriginalHistoricalCanonicalZ434 e m mp n=mp*u := by
    have huEq : u0=u := by
      have ha := (Finset.mem_filter.mp hu0).2.2.2
      omega
    rwa [huEq] at hEz
  have hZpos := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m mp n he hneq
    ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩
  dsimp only at hZpos
  refine ⟨?_,?_⟩
  · exact parity_original_historical_log_dyadic_e_pullback434
      U E e m mp (parityOriginalHistoricalOffdiagK434 e m mp)
      hU hE h1.1 h2.1 hk hShift
  · exact parity_original_historical_log_dyadic_n_pullback434
      U V Z e m mp n u (parityOriginalHistoricalCanonicalZ434 e m mp n)
      (parityOriginalHistoricalOffdiagK434 e m mp)
      hU hV hZ h1.1 h2.1 hZpos.2.1 hk h1.2.2 hShift hZActual
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLogDyadicBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- A REAL physical Parity dyadic [A,2A] localizes its logarithmic
Fourier coordinate to the fixed interval [0,log 2]. This is valid
at arbitrary positive scale A, with no synthetic Fourier multiplier.
It supplies the exact compact box needed by Parity (4.14)-(4.15). -/
theorem parity_original_historical_log_dyadic_coordinate_Icc434
    (A x : ℝ) (hA : 0 < A) (hLo : A≤x) (hHi : x≤2*A) :
    0≤Real.log (x/A) ∧ Real.log (x/A)≤Real.log 2 := by
  have hx : 0 < x := hA.trans_le hLo
  have hDiv : 1≤x/A := (le_div_iff₀ hA).mpr (by simpa using hLo)
  have hUpper : x/A≤2 := (div_le_iff₀ hA).mpr (by nlinarith [hHi])
  exact ⟨Real.log_nonneg hDiv,
    Real.log_le_log (div_pos hx hA) hUpper⟩

/-- All three original Parity logarithmic Fourier coordinates lie in
the same FIXED compact box when m,m' and physical source z each lie
in their genuine positive dyadic windows. The source z range itself
is now derived separately, before partition into Z pieces. -/
theorem parity_original_historical_log_three_coordinate_box434
    (U Z : ℝ) (m mp z : ℕ) (hU : 0 < U) (hZ : 0 < Z)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(z:ℝ)) (hzHi : (z:ℝ)≤2*Z) :
    0≤Real.log ((m:ℝ)/U) ∧ Real.log ((m:ℝ)/U)≤Real.log 2 ∧
    0≤Real.log ((mp:ℝ)/U) ∧ Real.log ((mp:ℝ)/U)≤Real.log 2 ∧
    0≤Real.log ((z:ℝ)/Z) ∧ Real.log ((z:ℝ)/Z)≤Real.log 2 := by
  have hm := parity_original_historical_log_dyadic_coordinate_Icc434 U (m:ℝ)
    hU hmLo hmHi
  have hmp := parity_original_historical_log_dyadic_coordinate_Icc434 U (mp:ℝ)
    hU hmpLo hmpHi
  have hz := parity_original_historical_log_dyadic_coordinate_Icc434 Z (z:ℝ)
    hZ hzLo hzHi
  exact ⟨hm.1,hm.2,hmp.1,hmp.2,hz.1,hz.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSourceEtaPullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT original Parity §4.5 pulled-back eta_e(e/E)*eta_n(n/V)
weight on a GENUINE supported original physical source term.
The result applies to the real eta_e, eta_n smooth majorants, but
requires no synthetic analytic assumptions about their derivatives:
those are separate hypotheses for the 3-dimensional Fourier lemma.
The original h=-2 correction 2/(UV) is retained exactly. -/
theorem parity_original_historical_supported_eta_e_eta_n_pullback434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
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
  have hOriginal := parity_original_historical_supported_source_log_cutoff_pullbacks434
    d L band slot δ Y e m mp n he hneq hValid U E V Z hU hE hV hZ
  dsimp only at hOriginal
  rw [hOriginal.1,hOriginal.2]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSmooth3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exactly the FIRST source-derived original Parity (4.14) pulled-back
argument of eta_e, in the genuine three logarithmic variables
(t1,t2,t3) = (log(m/U), log(m'/U), log(z/Z)). -/
def parityOriginalHistoricalEtaELogArg434
    (U E : ℝ) (k : ℤ) (t : Fin 3 → ℝ) : ℝ :=
  (U/((k:ℝ)*E)) * (Real.exp (t 1) - Real.exp (t 0))

/-- Exactly the SECOND source-derived original Parity (4.14)
pulled-back argument of eta_n, with full h=-2 correction. -/
def parityOriginalHistoricalEtaNLogArg434
    (U V Z : ℝ) (k : ℤ) (t : Fin 3 → ℝ) : ℝ :=
  (Z/((k:ℝ)*U*V)) * Real.exp (t 2) *
    (Real.exp (-(t 0)) - Real.exp (-(t 1))) +
  (2/(U*V)) * Real.exp (-(t 0))

/-- The ACTUAL original Parity (4.14) eta_e argument is C∞ in ALL THREE
logarithmic variables. This is not a blanket hypothesis about a
Fourier-separation coefficient: the non-linear exponential map is
explicit and the proof is ordinary real differential calculus. -/
theorem parity_original_historical_eta_e_log_arg_smooth434
    (U E : ℝ) (k : ℤ) :
    ContDiff ℝ ∞ (parityOriginalHistoricalEtaELogArg434 U E k) := by
  unfold parityOriginalHistoricalEtaELogArg434
  fun_prop

/-- The full h=-2 original Parity eta_n log pullback is C∞, including
the exact source correction and all inverse parameters. -/
theorem parity_original_historical_eta_n_log_arg_smooth434
    (U V Z : ℝ) (k : ℤ) :
    ContDiff ℝ ∞ (parityOriginalHistoricalEtaNLogArg434 U V Z k) := by
  unfold parityOriginalHistoricalEtaNLogArg434
  fun_prop

/-- Original Parity (4.14) combined pulled-back eta_e*eta_n in
Fin3 variables. These are the physical arguments from the native
source, not surrogate independent smooth test functions. -/
def parityOriginalHistoricalPulledCutoff3D434
    (U E V Z : ℝ) (k : ℤ) (etaE etaN : ℝ → ℂ)
    (t : Fin 3 → ℝ) : ℂ :=
  etaE (parityOriginalHistoricalEtaELogArg434 U E k t) *
  etaN (parityOriginalHistoricalEtaNLogArg434 U V Z k t)

/-- Genuine entire pulled back 3-dimensional original Parity(4.14)
eta-product is C∞ when the two manuscript cutoff functions are C∞.
No assumption on differentiation of its composite 3D kernel. -/
theorem parity_original_historical_pulled_cutoff_3d_smooth434
    (U E V Z : ℝ) (k : ℤ) (etaE etaN : ℝ → ℂ)
    (hEtaE : ContDiff ℝ ∞ etaE) (hEtaN : ContDiff ℝ ∞ etaN) :
    ContDiff ℝ ∞
      (parityOriginalHistoricalPulledCutoff3D434 U E V Z k etaE etaN) := by
  unfold parityOriginalHistoricalPulledCutoff3D434
  exact (hEtaE.comp (parity_original_historical_eta_e_log_arg_smooth434 U E k)).mul
    (hEtaN.comp (parity_original_historical_eta_n_log_arg_smooth434 U V Z k))

/-- Original fixed-compact logarithmic cube cutoff multiplied by
genuine full eta_e*eta_n source pullback. The buffer functions are
ordinary independent, fixed smooth one-dimensional dyadic buffers;
no Fourier integral is asserted by this DEFINITION. -/
def parityOriginalHistoricalPulledBuffered3D434
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (etaE etaN : ℝ → ℂ)
    (t : Fin 3 → ℝ) : ℂ :=
  buf (t 0) * buf (t 1) * buf (t 2) *
  parityOriginalHistoricalPulledCutoff3D434 U E V Z k etaE etaN t

/-- The TRUE original Parity (4.14) 3D pullback, WITH its fixed compact
auxiliary dyadic buffers, is C∞, not merely pointwise continuous. -/
theorem parity_original_historical_pulled_buffered_3d_smooth434
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (etaE etaN : ℝ → ℂ)
    (hBuf : ContDiff ℝ ∞ buf)
    (hEtaE : ContDiff ℝ ∞ etaE) (hEtaN : ContDiff ℝ ∞ etaN) :
    ContDiff ℝ ∞
      (parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf etaE etaN) := by
  unfold parityOriginalHistoricalPulledBuffered3D434
  have hb0 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => buf (t 0)) :=
    hBuf.comp (contDiff_apply ℝ ℝ (0 : Fin 3))
  have hb1 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => buf (t 1)) :=
    hBuf.comp (contDiff_apply ℝ ℝ (1 : Fin 3))
  have hb2 : ContDiff ℝ ∞ (fun t : Fin 3 → ℝ => buf (t 2)) :=
    hBuf.comp (contDiff_apply ℝ ℝ (2 : Fin 3))
  exact ((hb0.mul hb1).mul hb2).mul
    (parity_original_historical_pulled_cutoff_3d_smooth434
      U E V Z k etaE etaN hEtaE hEtaN)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSmooth3DSchwartz -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The true full eta_e*eta_n Parity(4.14) 3D logarithmic kernel,
with a fixed original dyadic buffer in EACH coordinate, has
compact support in the exact closed real cube [a,b]^3 whenever
the supplied fixed buffer has support in [a,b].
This is an actual source-defined nonlinear kernel, not an assumed
Fourier-cutoff remainder bound or invented Schwartz function. -/
theorem parity_original_historical_pulled_buffered_3d_support434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBuf : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    Function.support
      (parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf etaE etaN) ⊆
      Set.Icc (fun _ : Fin 3 => a) (fun _ : Fin 3 => b) := by
  intro t ht
  change parityOriginalHistoricalPulledBuffered3D434
    U E V Z k buf etaE etaN t ≠ 0 at ht
  have h0 : buf (t 0) ≠ 0 := by
    intro hz
    exact ht (by simp [parityOriginalHistoricalPulledBuffered3D434,hz])
  have h1 : buf (t 1) ≠ 0 := by
    intro hz
    exact ht (by simp [parityOriginalHistoricalPulledBuffered3D434,hz])
  have h2 : buf (t 2) ≠ 0 := by
    intro hz
    exact ht (by simp [parityOriginalHistoricalPulledBuffered3D434,hz])
  have hb0 := hBuf (t 0) h0
  have hb1 := hBuf (t 1) h1
  have hb2 := hBuf (t 2) h2
  change (fun _ : Fin 3 => a) ≤ t ∧ t ≤ (fun _ : Fin 3 => b)
  constructor
  · intro i
    fin_cases i
    · exact hb0.1
    · exact hb1.1
    · exact hb2.1
  · intro i
    fin_cases i
    · exact hb0.2
    · exact hb1.2
    · exact hb2.2

/-- This REAL 3D source smooth pulledback cutoff has actual compact
support in the original fixed logarithmic dyadic box. -/
theorem parity_original_historical_pulled_buffered_3d_compact434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBuf : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    HasCompactSupport
      (parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf etaE etaN) := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · exact parity_original_historical_pulled_buffered_3d_support434
      U E V Z k buf etaE etaN a b hBuf
  · exact isClosed_Icc

/-- Genuine ORIGINAL Parity (4.14) 3-dimensional Schwartz function
for actual source eta_e,eta_n and a fixed dyadic buffer. This is
constructed by proving BOTH C-infinity and compact support, not
asserting a new synthetic Fourier bound. -/
def parityOriginalHistoricalPulledSchwartz3D434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    𝓢(Fin 3 → ℝ, ℂ) :=
  (parity_original_historical_pulled_buffered_3d_compact434
    U E V Z k buf etaE etaN a b hBufSupport).toSchwartzMap
      (parity_original_historical_pulled_buffered_3d_smooth434
        U E V Z k buf etaE etaN hBufSmooth hEtaESmooth hEtaNSmooth)

/-- Exact evaluation of the 3D Schwartz function: it is still the
ACTUAL eta_e*eta_n cutoff times three fixed original logarithmic
buffers, with no pointwise Fourier-tail or parity replacement. -/
theorem parity_original_historical_pulled_schwartz_3d_apply434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (t : Fin 3 → ℝ) :
    parityOriginalHistoricalPulledSchwartz3D434 U E V Z k buf etaE etaN
      a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport t =
    parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf etaE etaN t := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform RealInnerProductSpace
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The true Parity (4.14) pulledback 3D eta_e*eta_n cutoff as a
SCHWARTZ function on the actual Euclidean real inner product space,
not the product-sup normed space. A continuous-linear equivalence
transports the genuine C-infinity compact support already PROVED on
the original three source coordinates. This supplies the precise
inner-product Fourier-transform structure used in Parity §4.5. -/
def parityOriginalHistoricalPulledEuclidean3D434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := by
  let f : (Fin 3 → ℝ) → ℂ :=
    parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf etaE etaN
  let hLE := EuclideanSpace.equiv (Fin 3) ℝ
  let hC : HasCompactSupport (f ∘ hLE) :=
    (parity_original_historical_pulled_buffered_3d_compact434
      U E V Z k buf etaE etaN a b hBufSupport).comp_homeomorph
      hLE.toHomeomorph
  let hS : ContDiff ℝ ∞ (f ∘ hLE) :=
    (parity_original_historical_pulled_buffered_3d_smooth434
      U E V Z k buf etaE etaN hBufSmooth hEtaESmooth hEtaNSmooth).comp
      hLE.contDiff
  exact hC.toSchwartzMap hS

/-- Exact evaluation on original source logarithmic coordinates;
the Euclidean model is NOT a different smooth cutoff. -/
theorem parity_original_historical_pulled_euclidean_3d_apply434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (t : EuclideanSpace ℝ (Fin 3)) :
    parityOriginalHistoricalPulledEuclidean3D434 U E V Z k buf etaE etaN
      a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport t =
    parityOriginalHistoricalPulledBuffered3D434
      U E V Z k buf etaE etaN (EuclideanSpace.equiv (Fin 3) ℝ t) := rfl

/-- ORIGINAL Parity §4.5 exact 3-D REAL Fourier inversion of the TRUE
h=-2 eta_e/eta_n pulledback cutoff with the original fixed dyadic
buffers. Uses genuine Euclidean Lebesgue measure, mathematical
Fourier inverse exp(+2πi ⟪ξ,t⟫), Schwartz transform and NO assumed
decay/tail, inserted σ or missing 2π factor. -/
theorem parity_original_historical_pulled_3d_fourier_inversion434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (t : EuclideanSpace ℝ (Fin 3)) :
    parityOriginalHistoricalPulledEuclidean3D434 U E V Z k buf etaE etaN
      a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport t =
    ∫ ξ : EuclideanSpace ℝ (Fin 3),
      Complex.exp (((2*Real.pi*⟪ξ,t⟫ : ℝ):ℂ)*Complex.I) *
      (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
        U E V Z k buf etaE etaN a b
        hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  let f := parityOriginalHistoricalPulledEuclidean3D434 U E V Z k buf etaE etaN
    a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  have hInv : (𝓕⁻ (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))) t = f t := by
    rw [FourierTransform.fourierInv_fourier_eq]
  calc
    _ = f t := rfl
    _ = (𝓕⁻ (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))) t := hInv.symm
    _ = _ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [smul_eq_mul]
      rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3DPhase -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- GENUINE dimension-3 Fourier phase from the Schwartz inversion of
Parity's pulled-back eta_e,eta_n cutoff. In the TRUE Euclidean physical
inner product it is precisely the product of THREE signed 2π complex
exponentials, not a formal placeholder for a desired (4.17) phase. -/
theorem parity_original_historical_fourier_3d_inner_phase_split434
    (ξ t : EuclideanSpace ℝ (Fin 3)) :
    Complex.exp (((2*Real.pi*⟪ξ,t⟫ : ℝ):ℂ)*Complex.I) =
      ∏ i : Fin 3,
        Complex.exp (((2*Real.pi*(ξ i)*(t i):ℝ):ℂ)*Complex.I) := by
  have hInner : ⟪ξ,t⟫ = ∑ i : Fin 3, (ξ i)*(t i) := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  rw [hInner]
  have hC : (((2*Real.pi*(∑ i : Fin 3, (ξ i)*(t i)) : ℝ):ℂ)*Complex.I) =
      ∑ i : Fin 3, (((2*Real.pi*(ξ i)*(t i) : ℝ):ℂ)*Complex.I) := by
    simp only [Fin.sum_univ_three]
    push_cast
    ring
  rw [hC,Complex.exp_sum]

/-- Source-matched physical log coordinates for the REAL original
Parity (4.14): t1=log(m/U),t2=log(m'/U),t3=log(z/Z), embedded in
Euclidean R^3 with its standard inner product. -/
def parityOriginalHistoricalRealLogTriple434
    (U Z : ℝ) (m mp z : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![Real.log ((m:ℝ)/U),Real.log ((mp:ℝ)/U),Real.log ((z:ℝ)/Z)]

/-- The exact actual 3D Fourier product at SOURCE coordinates is
three logarithmic characters; the source normalizations U,U,Z are
still visible, and the mathematical Fourier frequency is 2πξ. -/
theorem parity_original_historical_log_triple_fourier_phase434
    (U Z : ℝ) (m mp z : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    Complex.exp (((2*Real.pi*⟪ξ,parityOriginalHistoricalRealLogTriple434 U Z m mp z⟫ : ℝ):ℂ)*Complex.I) =
      Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) *
      Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
      Complex.exp (((2*Real.pi*(ξ 2)*Real.log ((z:ℝ)/Z):ℝ):ℂ)*Complex.I) := by
  rw [parity_original_historical_fourier_3d_inner_phase_split434]
  simp only [Fin.prod_univ_three,parityOriginalHistoricalRealLogTriple434]
  simp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3DSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- Original source at a true h=-2 two-ended Q/P/B509 physical
cofactor pair: the ORIGINAL smoothed eta_e(e/E)*eta_n(n/V)
with exactly three dyadic log buffers is equal to the ACTUAL
3D Euclidean Schwartz pulledback eta kernel at t=(log(m/U),
log(m'/U),log(z/Z)), not merely a definition of abstract eta. -/
theorem parity_original_historical_source_eta_equals_euclidean_3d434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
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
  have hEta := parity_original_historical_supported_eta_e_eta_n_pullback434
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

/-! ## OriginalHistoricalFourier3DSourceIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- EXACT Parity (4.14)--(4.16) 3D Fourier separation for ORIGINAL
SOURCE h=-2 eta_e(e/E)*eta_n(n/V) at actual two-ended Q/P physical
cofactor data. It carries three real logarithmic Fourier coordinates
m,m',z, the ORIGINAL 2π normalization, all true primes/rough gates,
and the entire complex Schwartz multiplier of the actual pulled-back
cutoff. No frequency truncation, polynomial total-variation, 4.17
correlation or subsequent TypeII is claimed by this equality. -/
theorem parity_original_historical_source_eta_real_3d_fourier_integral434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z)
    (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    buf (Real.log ((m:ℝ)/U)) * buf (Real.log ((mp:ℝ)/U)) *
    buf (Real.log ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z)) *
    (etaE ((e:ℝ)/E)*etaN ((n:ℝ)/V)) =
      ∫ ξ : EuclideanSpace ℝ (Fin 3),
        (Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) *
         Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
         Complex.exp (((2*Real.pi*(ξ 2)*Real.log
           ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z):ℝ):ℂ)*Complex.I)) *
        (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
          U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
          buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  let t := parityOriginalHistoricalRealLogTriple434 U Z m mp
    (parityOriginalHistoricalCanonicalZ434 e m mp n)
  let f := parityOriginalHistoricalPulledEuclidean3D434
    U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
    buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  have hSource := parity_original_historical_source_eta_equals_euclidean_3d434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ buf etaE etaN a b
    hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  have hFourier := parity_original_historical_pulled_3d_fourier_inversion434
    U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
    buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport t
  have hPhase (ξ : EuclideanSpace ℝ (Fin 3)) :=
    parity_original_historical_log_triple_fourier_phase434
      U Z m mp (parityOriginalHistoricalCanonicalZ434 e m mp n) ξ
  rw [←hSource,hFourier]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [hPhase ξ]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3DIntegrable -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact original 3D log cutoff Schwartz-Fourier transform is
absolutely integrable over REAL Euclidean Lebesgue 3-space. This is
proved from its genuine source C-infinity compact-support Schwartz
construction and the native Fourier transform on EuclideanSpace;
no analytic Fourier tail precision or presumed L1-bound is inserted. -/
theorem parity_original_historical_true_3d_fourier_L1_integrable434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      ‖(𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) := by
  let f := parityOriginalHistoricalPulledEuclidean3D434 U E V Z k buf etaE etaN
      a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  exact (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)).integrable.norm

/-- Original EXACT Fourier inversion integrand is integrable for
ANY source physical logarithmic triple t, uniformly as a statement
(not yet uniformly with polynomial L constants). The phase carries
the unmodified Mathlib/Parity 2π normalization. -/
theorem parity_original_historical_true_3d_fourier_phase_integrable434
    (U E V Z : ℝ) (k : ℤ) (buf etaE etaN : ℝ → ℂ)
    (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (t : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (((2*Real.pi*⟪ξ,t⟫:ℝ):ℂ)*Complex.I) *
      (𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
  let f := parityOriginalHistoricalPulledEuclidean3D434 U E V Z k buf etaE etaN
    a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  have hI : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) :=
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)).integrable
  have hcont : Continuous (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (((2*Real.pi*⟪ξ,t⟫:ℝ):ℂ)*Complex.I) *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
    fun_prop
  apply hI.mono hcont.aestronglyMeasurable
  filter_upwards [] with ξ
  simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,le_refl]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3DTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ACTUAL original smooth Parity (4.14) pulledback 3D Fourier H-th
frequency moment, on Euclidean R^3 with Fourier convention 2π.
Unlike a placeholder, the moment integrates the GENUINE physical
source Schwartz transform of eta_e*eta_n and fixed dyadic buffers. -/
def parityOriginalHistorical3DFourierMoment434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) : ℝ :=
  ∫ ξ : EuclideanSpace ℝ (Fin 3),
    ‖ξ‖^H *
      ‖(𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖

/-- Every actual source 3D pulledback Fourier moment of arbitrary
fixed integer order H is finite, since the original kernel was
proved C∞ compactly supported rather than assumed Fourier-regular. -/
theorem parity_original_historical_3d_fourier_moment_integrable434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      ‖ξ‖^H *
      ‖(𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) := by
  let f := parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
    buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  exact (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)).integrable_pow_mul volume H

/-- Genuine 3D original SOURCE Fourier moment is nonnegative. -/
theorem parity_original_historical_3d_fourier_moment_nonneg434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    0≤parityOriginalHistorical3DFourierMoment434 H U E V Z k
       buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport := by
  unfold parityOriginalHistorical3DFourierMoment434
  exact integral_nonneg (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg _) H) (norm_nonneg _))

/-- EXACT original Parity §4.5 frequency truncation inequality in
three real Euclidean Fourier variables. The outside-norm tail has
factor T^-H with H-th ACTUAL Schwartz Fourier moment; every Fourier
phase has modulus 1. This is a quantitative source theorem, but
proving the moment uniformly polynomial in L,k,Z remains a separate
analytic requirement before full Parity TypeII (4.2). -/
theorem parity_original_historical_3d_fourier_tail_le_moment434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (T : ℝ) (hT : 0 < T) :
    (∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T} : Set _)ᶜ,
      ‖(𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) ≤
    parityOriginalHistorical3DFourierMoment434 H U E V Z k
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport / T^H := by
  let f := (𝓕 (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {ξ | ‖ξ‖ ≤ T}
  have hS : MeasurableSet S :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hw : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖f ξ‖) := f.integrable.norm
  have hx : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖ξ‖^H*‖f ξ‖) :=
    parity_original_historical_3d_fourier_moment_integrable434 H U E V Z k
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  have hOutside : ∀ᵐ ξ ∂volume.restrict Sᶜ,
      T^H*‖f ξ‖ ≤ ‖ξ‖^H*‖f ξ‖ := by
    filter_upwards [ae_restrict_mem hS.compl] with ξ hξ
    have hξT : T ≤ ‖ξ‖ := by
      have hh : ¬‖ξ‖≤T := hξ
      exact le_of_lt (lt_of_not_ge hh)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.le hξT H) (norm_nonneg _)
  have hint := integral_mono_ae (hw.integrableOn.const_mul (T^H))
    hx.integrableOn hOutside
  rw [integral_const_mul] at hint
  have htotal :
      (∫ ξ in Sᶜ, ‖ξ‖^H*‖f ξ‖) ≤
      parityOriginalHistorical3DFourierMoment434 H U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport :=
    setIntegral_le_integral hx (Filter.Eventually.of_forall
      (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg _) H) (norm_nonneg _)))
  have hp : 0 < T^H := pow_pos hT _
  exact (le_div_iff₀ hp).mpr (by
    simpa only [mul_comm] using hint.trans htotal)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistorical3DFourierSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- A genuine ORIGINAL 3D Schwartz Fourier moment upper bound by
TWO EXPLICIT native Schwartz seminorms of the TRUE source η_eη_n
Fourier transform. The prefactor is fixed by 3-dimensional Lebesgue
measure and independent of all actual source L,k,Z and both cutoffs.
This is not yet a polynomial-in-L bound: that requires a SOURCE
seminorm estimate as the moving η_e lower window shrinks. -/
theorem parity_original_historical_3d_moment_le_two_source_seminorms434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    parityOriginalHistorical3DFourierMoment434 H U E V Z k
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport ≤
    ((2:ℝ)^(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower *
      (∫ x : EuclideanSpace ℝ (Fin 3),
        (1+‖x‖)^(-((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℝ)))) *
      ((SchwartzMap.seminorm ℂ 0 0)
        (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
          U E V Z k buf etaE etaN a b
          hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) +
       (SchwartzMap.seminorm ℂ (H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower) 0)
        (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
          U E V Z k buf etaE etaN a b
          hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3), ℂ))) := by
  let F : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ) :=
    𝓕 (parityOriginalHistoricalPulledEuclidean3D434
      U E V Z k buf etaE etaN a b
      hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport)
  have h := SchwartzMap.integral_pow_mul_iteratedFDeriv_le
    ℂ volume F H 0
  simpa only [parityOriginalHistorical3DFourierMoment434,
    norm_iteratedFDeriv_zero] using h
end Green64Analytic.Parity

end

end

