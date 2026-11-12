module

public import Green64.Library.Weights.D61EmptyQSkipChartZero
public import Green64.Library.Correlation.CleanPhysicalRowEnergy

@[expose] public section

/-!
# Analysis / Estimates / ConditionalPrimeFibre

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualConditionalPrimeFibre -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64ComparisonPartial Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem B567_active_rough
    (a eta b0 L : ℝ) (j m : ℕ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j) :
    rough (Real.exp (Real.sqrt L)) m := by
  have hK := (Finset.mem_filter.mp hm).1
  have hAlpha := (Finset.mem_filter.mp hm).2
  have hmlo := (Finset.mem_Icc.mp hK).1
  have hmpos : 0 < m := (by positivity : 0 < (2:ℕ)^j).trans_le hmlo
  have hDelta : sourceD20FullDelta (L^(-(1:ℝ)))
      (Real.exp (Real.sqrt L)) ((Real.exp L)^a) m ≠ 0 := by
    intro hz
    apply hAlpha
    simp [sourceNativeB563OriginalD61Alpha434,sourceD36OriginalCofactorMask,hz]
  have hR := original_D20_full_delta_support_SourceRoughAbove434
    (L^(-(1:ℝ))) (Real.exp (Real.sqrt L)) ((Real.exp L)^a) m hWy hDelta
  exact ⟨hmpos,hR⟩

private theorem B567_same_dyad_prime_unique
    (j m A h p1 p2 t1 t2 : ℕ) (s : ℤ)
    (hm : m ∈ sourceD36DyadicInterval j)
    (ht1 : t1 ∈ sourceD36DyadicInterval j)
    (ht2 : t2 ∈ sourceD36DyadicInterval j)
    (hA : 0 < A) (hc : Nat.Coprime m h)
    (he1 : ((m*A*p1:ℕ):ℤ)+s=((h*t1:ℕ):ℤ))
    (he2 : ((m*A*p2:ℕ):ℤ)+s=((h*t2:ℕ):ℤ)) :
    t1=t2 ∧ p1=p2 := by
  have hmB := Finset.mem_Icc.mp hm
  have hpw : 2^(j+1)=2^j*2 := by rw [pow_succ]
  have hmpos : 0 < m := (by positivity : 0 < (2:ℕ)^j).trans_le hmB.1
  have hstep (u v p q : ℕ)
      (hu : u ∈ sourceD36DyadicInterval j)
      (hv : v ∈ sourceD36DyadicInterval j) (huv : u ≤ v)
      (hep : ((m*A*p:ℕ):ℤ)+s=((h*u:ℕ):ℤ))
      (heq : ((m*A*q:ℕ):ℤ)+s=((h*v:ℕ):ℤ)) : u=v := by
    have huB := Finset.mem_Icc.mp hu
    have hvB := Finset.mem_Icc.mp hv
    have hdiffI : (m:ℤ) ∣ (h:ℤ)*((v:ℤ)-(u:ℤ)) := by
      refine ⟨(A:ℤ)*((q:ℤ)-(p:ℤ)),?_⟩
      push_cast at hep heq
      nlinarith
    have hdiff : m ∣ h*(v-u) := Int.natCast_dvd_natCast.mp (by
      push_cast
      rw [Int.ofNat_sub huv]
      exact hdiffI)
    have hmdiff := hc.dvd_of_dvd_mul_left hdiff
    have hsmall : v-u < m := by omega
    by_contra hne
    have hpos : 0 < v-u := by omega
    have hle := Nat.le_of_dvd hpos hmdiff
    omega
  have ht : t1=t2 := by
    rcases le_total t1 t2 with hle | hle
    · exact hstep t1 t2 p1 p2 ht1 ht2 hle he1 he2
    · exact (hstep t2 t1 p2 p1 ht2 ht1 hle he2 he1).symm
  refine ⟨ht,?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hmpos hA)
  apply Int.natCast_inj.mp
  rw [ht] at he1
  linarith

/-- A prime selected from one genuine skipped-Q coordinate is NOT an
independent interval variable after fixing the left cofactor, all remaining
left factors A, and the complete right complementary product h. The
original active cofactor dyad is shorter than the congruence step m, so
both the other cofactor and the selected prime are unique. The true full
auxiliary product and signed 2kD shift remain. -/
theorem source_native_B567_actual_D61_prime_pair_unique434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (dsrc : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (nu : SourceOriginalProbePattern434 G m0)
    (aux : SourceOriginalProbeAuxIndex434 m0 nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 nu dsrc.Tb))
    (a eta b0 : ℝ) (j m A h p1 p2 t1 t2 : ℕ) (k : ℤ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j)
    (ht1 : t1 ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j)
    (ht2 : t2 ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j)
    (hA : 0 < A) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ Real.exp (Real.sqrt L))
    (he1 : ((m*A*p1:ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t1:ℕ):ℤ))
    (he2 : ((m*A*p2:ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t2:ℕ):ℤ)) :
    t1=t2 ∧ p1=p2 := by
  have hmR := B567_active_rough a eta b0 L j m hWy hm
  have hcop : Nat.Coprime m h :=
    source_native_B547_original_aux_comparison_coprime434 dsrc m0 nu aux haux
      m h (m*A*p1) k hmR hk hsmall
      ⟨A*p1,by ring⟩ (by rw [he1]; exact ⟨(t1:ℤ),by push_cast; rfl⟩)
  exact B567_same_dyad_prime_unique j m A h p1 p2 t1 t2
    (2*k*((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ))
    (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp ht1).1
    (Finset.mem_filter.mp ht2).1 hA hcop he1 he2

/-- Literal one-coordinate rigidity in the original labelled QSkip carrier.
Only the selected skipped coordinate varies on the left; the other labels,
the designated Q prime and the whole P-part are fixed. The entire right
complementary product is fixed, while its original active cofactor may vary.
This theorem does not identify or collapse a modular character-ratio fibre. -/
theorem source_native_B567_actual_QSkip_coordinate_unique434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (dsrc : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (nu : SourceOriginalProbePattern434 G m0)
    (aux : SourceOriginalProbeAuxIndex434 m0 nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 nu dsrc.Tb))
    (r d jK m p0 v h t1 t2 : ℕ) (a eta b0 sigmaT : ℝ) (k : ℤ)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (u1 u2 : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
      ¬ δ i = true})
    (hoff : ∀ z, z ≠ i → u1 z = u2 z)
    (hp0 : p0 ∈ sourceOriginalQActualBands r d L b)
    (hv : v ∈ sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
    (ht1 : t1 ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
    (ht2 : t2 ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
    (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ Real.exp (Real.sqrt L))
    (he1 : ((m*sourceQPTagH ((m,(p0,u1)),v):ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t1:ℕ):ℤ))
    (he2 : ((m*sourceQPTagH ((m,(p0,u2)),v):ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t2:ℕ):ℤ)) :
    t1=t2 ∧ u1=u2 := by
  classical
  let I := {z : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
    ¬ δ z = true}
  let P := ∏ z ∈ (Finset.univ : Finset I).erase i,(u1 z).val
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro z _
    exact (source_native_B537_actual_Q_band_prime434 r d L b slot z.val
      (u1 z).val (u1 z).property).pos
  have hp0pos : 0 < p0 := (sourceOriginalQActualBands_prime434 r d L b p0 hp0).pos
  have hvpos : 0 < v := by
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
    omega
  have hprod1 : orderedSkipProduct u1 = (u1 i).val*P := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset I)
      (fun z => (u1 z).val) (Finset.mem_univ i)).symm
  have hprod2 : orderedSkipProduct u2 = (u2 i).val*P := by
    have hrest : (∏ z ∈ (Finset.univ : Finset I).erase i,(u2 z).val) = P := by
      apply Finset.prod_congr rfl
      intro z hz
      rw [hoff z (Finset.mem_erase.mp hz).1]
    calc
      _ = (u2 i).val*(∏ z ∈ (Finset.univ : Finset I).erase i,(u2 z).val) :=
        (Finset.mul_prod_erase (Finset.univ : Finset I)
          (fun z => (u2 z).val) (Finset.mem_univ i)).symm
      _ = _ := by rw [hrest]
  have he1' : ((m*(p0*P*v)*(u1 i).val:ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t1:ℕ):ℤ) := by
    convert he1 using 1; simp only [sourceQPTagH,hprod1]; push_cast; ring
  have he2' : ((m*(p0*P*v)*(u2 i).val:ℕ):ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux:ℕ):ℤ)=
      ((h*t2:ℕ):ℤ) := by
    convert he2 using 1; simp only [sourceQPTagH,hprod2]; push_cast; ring
  obtain ⟨ht,hp⟩ := source_native_B567_actual_D61_prime_pair_unique434
    dsrc m0 nu aux haux a eta b0 jK m (p0*P*v) h (u1 i).val (u2 i).val t1 t2 k
    hWy hm ht1 ht2 (Nat.mul_pos (Nat.mul_pos hp0pos hP) hvpos) hk hsmall he1' he2'
  refine ⟨ht,funext (fun z => ?_)⟩
  by_cases hzi : z=i
  · subst z
    exact Subtype.ext hp
  · exact hoff z hzi

/-- The exact conditional prime/cofactor fibre. The original active D61
cofactor set is retained. Q may be the actual numerical band of a selected
skipped label. Every further physical, parity or marked gate only restricts
this set. The parameter D is instantiated with the full actual auxiliary
product in the theorems below. -/
def sourceNativeB567ActualPrimeFibre434
    (a eta b0 L : ℝ) (j m A h : ℕ) (Q : Finset ℕ) (k : ℤ) (D : ℕ) : Finset (ℕ×ℕ) :=
  ((sourceNativeB563OriginalD61ActiveK434 a eta b0 L j) ×ˢ Q).filter
    (fun z => ((m*A*z.2:ℕ):ℤ)+2*k*(D:ℤ)=((h*z.1:ℕ):ℤ))

/-- After the actual conditioning, at most one prime/cofactor term remains.
This is a conditional fibre statement, not a bound for the sum over all
left cofactors, opposite complements or modular character-ratio fibres. -/
theorem source_native_B567_actual_prime_fibre_card434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (dsrc : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (nu : SourceOriginalProbePattern434 G m0)
    (aux : SourceOriginalProbeAuxIndex434 m0 nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 nu dsrc.Tb))
    (a eta b0 : ℝ) (j m A h : ℕ) (Q : Finset ℕ) (k : ℤ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j)
    (hA : 0 < A) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ Real.exp (Real.sqrt L)) :
    (sourceNativeB567ActualPrimeFibre434 a eta b0 L j m A h Q k
      (sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨hzmem,hzeq⟩ := Finset.mem_filter.mp hz
  obtain ⟨hwmem,hweq⟩ := Finset.mem_filter.mp hw
  have ht := source_native_B567_actual_D61_prime_pair_unique434 dsrc m0 nu aux haux
    a eta b0 j m A h z.2 w.2 z.1 w.1 k hWy hm
    (Finset.mem_product.mp hzmem).1 (Finset.mem_product.mp hwmem).1 hA hk hsmall hzeq hweq
  exact Prod.ext ht.1 ht.2

/-- On an occupied actual conditional fibre, its coherent signed sum is one
literal full-Delta term. The arbitrary coefficient c can retain the complete
physical, QSkip, parity and marked factors; no positivity or nonvanishing of
that coefficient is assumed or concluded. In particular full-cell centering
cannot remove this fibre by averaging its selected prime coordinate. -/
theorem source_native_B567_actual_prime_fibre_sum434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (dsrc : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (nu : SourceOriginalProbePattern434 G m0)
    (aux : SourceOriginalProbeAuxIndex434 m0 nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 nu dsrc.Tb))
    (a eta b0 : ℝ) (j m A h : ℕ) (Q : Finset ℕ) (k : ℤ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b0 L j)
    (hA : 0 < A) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ Real.exp (Real.sqrt L))
    (z0 : ℕ×ℕ)
    (hz0 : z0 ∈ sourceNativeB567ActualPrimeFibre434 a eta b0 L j m A h Q k
      (sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux))
    (c : ℕ×ℕ → ℂ) :
    (∑ z ∈ sourceNativeB567ActualPrimeFibre434 a eta b0 L j m A h Q k
      (sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux),
      star (sourceNativeB563OriginalD61Alpha434 a eta b0 L m)*
        sourceNativeB563OriginalD61Alpha434 a eta b0 L z.1*c z) =
      star (sourceNativeB563OriginalD61Alpha434 a eta b0 L m)*
        sourceNativeB563OriginalD61Alpha434 a eta b0 L z0.1*c z0 := by
  have hcard := source_native_B567_actual_prime_fibre_card434 dsrc m0 nu aux haux
    a eta b0 j m A h Q k hWy hm hA hk hsmall
  have hset : sourceNativeB567ActualPrimeFibre434 a eta b0 L j m A h Q k
      (sourceOriginalProbeDA434 m0 nu aux * sourceOriginalProbeDB434 m0 nu aux) = {z0} := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard) z hz z0 hz0)
    · intro hz
      simpa only [Finset.mem_singleton.mp hz] using hz0
  rw [hset,Finset.sum_singleton]
end Green64Analytic.ShiftTwoTerminal

end

end

