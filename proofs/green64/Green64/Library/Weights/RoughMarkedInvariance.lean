module

public import Green64.Library.Weights.UnbannedMarkedPairCap
public import Green64.Library.Weights.Part101
public import Green64.Library.Weights.Part097
public import Green64.Library.Weights.AuxiliarySize

@[expose] public section

/-!
# Weights / RoughMarkedInvariance

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalRoughMarkedInvariance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationD
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Multiplication by a positive cofactor avoiding every original P prime
preserves the entire P valuation vector, not merely its parity. -/
theorem b618_original_P_valuations_mul434
    (P : Finset ℕ) (n H : ℕ) (hn : 0<n) (hH : 0<H)
    (havoid : ∀ p∈P, ¬p∣n) :
    ∀ p∈P, (n*H).factorization p=H.factorization p := by
  intro p hp
  simp only [Nat.factorization_mul hn.ne' hH.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (havoid p hp), zero_add]

/-- Exact original P part, ordinary part, and parity exponent along a
P-free cofactor progression. All prime powers are retained. -/
theorem b618_original_P_ordinary_mul434
    (P : Finset ℕ) (n H : ℕ) (hn : 0<n) (hH : 0<H)
    (havoid : ∀ p∈P, ¬p∣n) :
    sourceOriginalPPrimePart P (n*H)=sourceOriginalPPrimePart P H ∧
    sourceOriginalOrdinaryPart P (n*H)=n*sourceOriginalOrdinaryPart P H ∧
    sourceOriginalPParityExponent P (n*H)=sourceOriginalPParityExponent P H := by
  have hf := b618_original_P_valuations_mul434 P n H hn hH havoid
  have hset : (n*H).primeFactors ∩ P=H.primeFactors ∩ P := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hp, hP⟩
      have hd := Nat.mem_primeFactors.mp hp
      have hdiv : p∣H := (hd.1.dvd_mul.mp hd.2.1).resolve_left (havoid p hP)
      exact ⟨Nat.mem_primeFactors.mpr ⟨hd.1,hdiv,hH.ne'⟩,hP⟩
    · rintro ⟨hp,hP⟩
      have hd := Nat.mem_primeFactors.mp hp
      exact ⟨Nat.mem_primeFactors.mpr
        ⟨hd.1,dvd_mul_of_dvd_right hd.2.1 n,(Nat.mul_pos hn hH).ne'⟩,hP⟩
  have hpart : sourceOriginalPPrimePart P (n*H)=sourceOriginalPPrimePart P H := by
    unfold sourceOriginalPPrimePart
    rw [hset]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hf p (Finset.mem_inter.mp hp).2]
  refine ⟨hpart,?_,?_⟩
  · have hpos := (b613_original_P_part_prime_support434 P H).1
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc
      sourceOriginalPPrimePart P H*sourceOriginalOrdinaryPart P (n*H)
          =n*H := by
        rw [←hpart]
        exact b613_original_P_ordinary_recombine434 P (n*H) (Nat.mul_pos hn hH).ne'
      _=n*(sourceOriginalPPrimePart P H*sourceOriginalOrdinaryPart P H) := by
        rw [b613_original_P_ordinary_recombine434 P H hH.ne']
      _=sourceOriginalPPrimePart P H*(n*sourceOriginalOrdinaryPart P H) := by ring
  · unfold sourceOriginalPParityExponent
    exact Finset.sum_congr rfl hf

private theorem b618_prime_support_mul
    (P : Finset ℕ) (n H : ℕ)
    (hprime : ∀p∈P,p.Prime) (havoid : ∀p∈P,¬p∣n) :
    smallPrimeSupport P (n*H)=smallPrimeSupport P H := by
  ext p
  simp only [smallPrimeSupport, Finset.mem_filter]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,((hprime p hp).dvd_mul.mp hd).resolve_left (havoid p hp)⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,dvd_mul_of_dvd_right hd n⟩

private theorem b618_big_mark_lists_mul
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G→Finset ℕ) (t : G→ℕ) (n H : ℕ)
    (hprime : ∀g p,p∈P g→p.Prime) (havoid : ∀g p,p∈P g→¬p∣n) :
    bigMarkLists P t (n*H)=bigMarkLists P t H := by
  have hs : ∀g,smallPrimeSupport (P g) (n*H)=smallPrimeSupport (P g) H :=
    fun g=>b618_prime_support_mul (P g) n H (hprime g) (havoid g)
  simp only [bigMarkLists,orderedBigMarks,hs]

private theorem b618_big_mark_prefactor_mul
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G→Finset ℕ) (t : G→ℕ) (q : ℝ) (V : G→ℝ) (n H : ℕ)
    (hprime : ∀g p,p∈P g→p.Prime) (havoid : ∀g p,p∈P g→¬p∣n) :
    bigMarkPrefactor P t q V (n*H)=bigMarkPrefactor P t q V H := by
  have hs : ∀g,smallPrimeSupport (P g) (n*H)=smallPrimeSupport (P g) H :=
    fun g=>b618_prime_support_mul (P g) n H (hprime g) (havoid g)
  simp only [bigMarkPrefactor,smallPrimeCount,hs]

/-- The COMPLETE literal unbanned marked slice is progression-constant.
Both marked lists, all hidden marks, full canonical active cells and every
conductor term are kept. Only P-free endpoint cofactors are removed. -/
theorem b618_original_unbanned_marked_slice_mul434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ)
    (n t H Hp : ℕ)
    (hprime : ∀g p,p∈P g→p.Prime)
    (hn : ∀g p,p∈P g→¬p∣n) (ht : ∀g p,p∈P g→¬p∣t) :
    b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q
        (n*H) (t*Hp)=
      b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q H Hp := by
  unfold b615OriginalUnbannedMarkedSlice434
  dsimp only
  rw [b618_big_mark_prefactor_mul P _ q V n H hprime hn,
    b618_big_mark_prefactor_mul P _ q V t Hp hprime ht,
    b618_big_mark_lists_mul P _ n H hprime hn,
    b618_big_mark_lists_mul P _ t Hp hprime ht]

/-- Every genuine original P prime is below the original roughness
cutoff W=exp(sqrt L), already for L>=1. -/
theorem b618_actual_P_below_W434
    (r : ℕ) (L : ℝ) (hL : 1≤L)
    (g : sourceOriginalPAllGroupType r L) (p : ℕ)
    (hp : p∈sourceOriginalPAllActualBands r L g) :
    (p : ℝ)≤Real.exp (Real.sqrt L) := by
  have hpprime := source_original_P_all_actual_band_prime r L g p hp
  have hppos : 0<(p:ℝ) := by exact_mod_cast hpprime.pos
  have hlog := source_original_P_all_actual_band_log r L hL g p hp
  have hpow : L^(2/5 : ℝ)≤Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  calc
    (p:ℝ)=Real.exp (Real.log (p:ℝ)) := (Real.exp_log hppos).symm
    _≤Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr (hlog.trans hpow)

/-- Literal W-roughness makes the entire actual P union coprime to a
cofactor. This uses the genuine prime-band bound, not a supplied P cap. -/
theorem b618_actual_rough_avoids_P434
    (r : ℕ) (L : ℝ) (hL : 1≤L) (n : ℕ)
    (hn : sourceD20Rough (Real.exp (Real.sqrt L)) n) :
    ∀p∈sourceNativeOriginalG434 r L,¬p∣n := by
  intro p hp hpn
  obtain ⟨g,_,hgp⟩ := Finset.mem_biUnion.mp hp
  have hprime := source_original_P_all_actual_band_prime r L g p hgp
  have hbound := b618_actual_P_below_W434 r L hL g p hgp
  have hmin : (n.minFac:ℝ)≤(p:ℝ) := by
    exact_mod_cast Nat.minFac_le_of_dvd hprime.two_le hpn
  exact (not_lt_of_ge (hmin.trans hbound)) hn.2

/-- The literal actual static all-P coefficient after deleting ONLY the
auxiliary ban. The original L-only P-part carrier and both signed parity
projectors remain INSIDE this coefficient; the complete Knu is unchanged. -/
def b618ActualUnbannedStaticCoefficient434
    (L sigmaT : ℝ) (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (w wp : ℕ) : ℂ :=
  let Pall:=sourceNativeOriginalG434 6 L
  let R:=sourceActualSortedPPartSupport 6 L ⌊(Real.exp L)^sigmaT⌋₊
  let nuf:=b604ActualLiftedPattern434 6 L m nu
  if sourceOriginalPPrimePart Pall w∈R ∧ sourceOriginalPPrimePart Pall wp∈R then
    b598ActualAllPPatternProjector434 6 L m nuf w *
    b598ActualAllPPatternProjector434 6 L m nuf wp *
    b615OriginalUnbannedMarkedSlice434 J 1 m hmJ nuf Q hA hB xi
      (sourceOriginalPAllActualBands 6 L) (sourceNativeOriginalAllPMass434 6 L)
      (b604ActualLiftedAux434 6 L m nu aux) (1/2) w wp
  else 0

/-- Actual no-ban progression constancy, with the genuine original P
carrier, lifted signed projector, hidden SMALL factors, and all canonical
BIG active cells. No physical j occurs in this coefficient. -/
theorem b618_actual_unbanned_static_coefficient_constancy434
    (L sigmaT : ℝ) (hL : 1≤L) (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (n t H Hp : ℕ)
    (hn : sourceD20Rough (Real.exp (Real.sqrt L)) n)
    (ht : sourceD20Rough (Real.exp (Real.sqrt L)) t)
    (hH : 0<H) (hHp : 0<Hp) :
    b618ActualUnbannedStaticCoefficient434 L sigmaT J m hmJ nu Q hA hB xi aux
        (n*H) (t*Hp)=
      b618ActualUnbannedStaticCoefficient434 L sigmaT J m hmJ nu Q hA hB xi aux H Hp := by
  have hna:=b618_actual_rough_avoids_P434 6 L hL n hn
  have hta:=b618_actual_rough_avoids_P434 6 L hL t ht
  have hpn:=b618_original_P_ordinary_mul434
    (sourceNativeOriginalG434 6 L) n H (by have:=hn.1;omega) hH hna
  have hpt:=b618_original_P_ordinary_mul434
    (sourceNativeOriginalG434 6 L) t Hp (by have:=ht.1;omega) hHp hta
  have hnb : ∀g p,p∈sourceOriginalPAllActualBands 6 L g→¬p∣n := by
    intro g p hp
    exact hna p (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ g,hp⟩)
  have htb : ∀g p,p∈sourceOriginalPAllActualBands 6 L g→¬p∣t := by
    intro g p hp
    exact hta p (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ g,hp⟩)
  have hs:=b618_original_unbanned_marked_slice_mul434 J 1 m hmJ
    (b604ActualLiftedPattern434 6 L m nu) Q hA hB xi
    (sourceOriginalPAllActualBands 6 L) (sourceNativeOriginalAllPMass434 6 L)
    (b604ActualLiftedAux434 6 L m nu aux) (1/2) n t H Hp
    (source_original_P_all_actual_band_prime 6 L) hnb htb
  unfold b618ActualUnbannedStaticCoefficient434
  dsimp only
  rw [hpn.1,hpt.1]
  split_ifs
  · rw [hs]
    have hparn := hpn.2.2
    have hpart := hpt.2.2
    dsimp only [sourceNativeOriginalG434] at hparn hpart
    simp only [b598ActualAllPPatternProjector434,b598ActualAllPPatternPhase434,
      hparn,hpart]
  · rfl

end Green64Analytic.ShiftTwoTerminal

end

end

