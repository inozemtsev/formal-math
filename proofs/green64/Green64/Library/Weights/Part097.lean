module

public import Green64.Library.Weights.QBandCapacity
public import Green64.Library.Correlation.Part066
public import Green64.Library.Weights.SourceQSkipActualResidual
public import Mathlib.Data.Nat.Find

@[expose] public section

/-!
# Weights / Part097

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSaturatedQMultiplier -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000


/-- Exact partition of ALL original prime powers into the P part and
ordinary part. This is the literal physical decomposition used by the core. -/
theorem b613_original_P_ordinary_recombine434
    (P : Finset ℕ) (w : ℕ) (hw : w≠0) :
    sourceOriginalPPrimePart P w*sourceOriginalOrdinaryPart P w=w := by
  unfold sourceOriginalPPrimePart sourceOriginalOrdinaryPart
  rw [Finset.prod_inter_mul_prod_sdiff]
  exact (Nat.prod_primeFactors_pow_factorization hw).symm

/-- The ordinary-core factorization and the fixed physical cofactor
determine the actual complement as its ORIGINAL P part times Q product.
No Q/P support condition on an arbitrary h is introduced. -/
theorem b613_actual_complement_P_Q_split434
    (P : Finset ℕ) (w m h q : ℕ) (hw : w ≠ 0) (hm : 0 < m)
    (hphysical : w=m*h)
    (hordinary : sourceOriginalOrdinaryPart P w=m*q) :
    h=sourceOriginalPPrimePart P w*q := by
  apply Nat.eq_of_mul_eq_mul_left hm
  calc
    m*h=w := hphysical.symm
    _=sourceOriginalPPrimePart P w*sourceOriginalOrdinaryPart P w :=
      (b613_original_P_ordinary_recombine434 P w hw).symm
    _=sourceOriginalPPrimePart P w*(m*q) := by rw [hordinary]
    _=m*(sourceOriginalPPrimePart P w*q) := by ring

/-- The literal native P-prime part retains every prime power, is positive,
and has no prime factors outside its actual finite P set. -/
theorem b613_original_P_part_prime_support434
    (P : Finset ℕ) (w : ℕ) :
    0 < sourceOriginalPPrimePart P w ∧
      ∀ q : ℕ, q.Prime → q∣sourceOriginalPPrimePart P w → q∈P := by
  constructor
  · unfold sourceOriginalPPrimePart
    apply Finset.prod_pos
    intro p hp
    have hprime := (Nat.mem_primeFactors.mp (Finset.mem_inter.mp hp).1).1
    exact pow_pos hprime.pos _
  · intro q hq hqd
    unfold sourceOriginalPPrimePart at hqd
    obtain ⟨p,hp,hqp⟩ := (hq.prime.dvd_finsetProd_iff
      (fun p => p^w.factorization p)).mp hqd
    have hprime := (Nat.mem_primeFactors.mp (Finset.mem_inter.mp hp).1).1
    have he : q=p := (Nat.prime_dvd_prime_iff_eq hq hprime).mp
      (hq.dvd_of_dvd_pow hqp)
    exact he.symm ▸ (Finset.mem_inter.mp hp).2

/-- Appending the LITERAL P-prime part changes no Q-band multiplicity.
This supports the real ordinary/P split rather than a surrogate support law. -/
theorem b613_actual_P_Q_band_capacity434
    (r d : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (P : Finset ℕ)
    (hDisj : ∀ g : Fin (d+1), ∀ q, q∈sourceOriginalQActualBands r d L g → q∉P)
    (w : ℕ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (g : Fin (d+1)) :
    b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
      (sourceOriginalPPrimePart P w*(p*orderedSkipProduct a)) ≤ r := by
  have hP := b613_original_P_part_prime_support434 P w
  have hp0 := (sourceOriginalQActualBands_prime434 r d L b p hp).ne_zero
  have ha0 : orderedSkipProduct a≠0 := by
    unfold orderedSkipProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro z _
    exact (sourceOriginalQActualBands_prime434 r d L
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot z.val).val.1
      (a z).val (a z).property).ne_zero
  have hzero : b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
      (sourceOriginalPPrimePart P w)=0 := by
    apply Finset.sum_eq_zero
    intro q hq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hDisj g q hq (hP.2 q (sourceOriginalQActualBands_prime434 r d L g q hq) hd)
  have hm :
      b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
        (sourceOriginalPPrimePart P w*(p*orderedSkipProduct a)) =
      b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
        (sourceOriginalPPrimePart P w) +
      b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
        (p*orderedSkipProduct a) := by
    simp only [b613QBandMultiplicity434,
      Nat.factorization_mul hP.1.ne' (mul_ne_zero hp0 ha0),
      Finsupp.add_apply,Finset.sum_add_distrib]
  rw [hm,hzero,zero_add]
  exact b613_actual_QSlot_QSkip_band_capacity434 r d L hr hL b slot δ p hp a g

/-- An original complement already saturated in every fine Q band
cannot acquire any positive small multiplier and remain an actual
P-prime-part times designated-plus-QSkip product. Coarse Q and all P
primes are required only to exceed the displayed multiplier bound.
All allocations, repeated values and complete P valuations are retained. -/
theorem b613_actual_saturated_Q_small_multiplier_one434
    (r d : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (P : Finset ℕ)
    (hDisj : ∀ g : Fin (d+1), ∀ q, q∈sourceOriginalQActualBands r d L g → q∉P)
    (J B u h0 : ℕ) (hu : 0<u) (h0pos : 0<h0) (huB : u≤B)
    (hPbig : ∀ q∈P, B<q)
    (hCoarse : ∀ g : Fin (d+1), g.val<J →
      ∀ q∈sourceOriginalQActualBands r d L g, B<q)
    (hSat : ∀ g : Fin (d+1), J≤g.val →
      r≤b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) h0)
    (w : ℕ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (heq : h0*u=sourceOriginalPPrimePart P w*(p*orderedSkipProduct a)) :
    u=1 := by
  by_contra hne
  obtain ⟨q,hq,hqu⟩ := Nat.exists_prime_and_dvd hne
  have hqB : q≤B := (Nat.le_of_dvd hu hqu).trans huB
  have hdiv : q∣sourceOriginalPPrimePart P w*(p*orderedSkipProduct a) := by
    rw [←heq]
    exact dvd_mul_of_dvd_right hqu h0
  rcases hq.dvd_mul.mp hdiv with hqP | hqQ
  · have hpP := (b613_original_P_part_prime_support434 P w).2 q hq hqP
    exact (not_lt_of_ge hqB) (hPbig q hpP)
  · obtain ⟨g,hg⟩ := b613_actual_QSlot_QSkip_prime_support434
      r d L b slot δ p hp a q hq hqQ
    have hfine : J≤g.val := by
      by_contra hn
      have hc := hCoarse g (by omega) q hg
      omega
    have hcap := b613_actual_P_Q_band_capacity434
      r d L hr hL P hDisj w b slot δ p hp a g
    rw [←heq] at hcap
    have hmul :
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) (h0*u) =
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) h0 +
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) u := by
      simp only [b613QBandMultiplicity434,Nat.factorization_mul h0pos.ne' hu.ne',
        Finsupp.add_apply,Finset.sum_add_distrib]
    have hfac : 0<u.factorization q := hq.factorization_pos_of_dvd hu.ne' hqu
    have hsum : u.factorization q ≤
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) u :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg
    have hs := hSat g hfine
    rw [hmul] at hcap
    omega


/-- The small Q multiplier is excluded BEFORE any auxiliary ban is used.
An arbitrary positive further scale T cannot lower any fine-band prime
multiplicity. In particular this theorem also applies to the unrestricted
stripped kernel once its literal ordinary/P decomposition is retained. -/
theorem b613_actual_saturated_Q_small_multiplier_with_scale_one434
    (r d : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (P : Finset ℕ)
    (hDisj : ∀ g : Fin (d+1), ∀ q, q∈sourceOriginalQActualBands r d L g → q∉P)
    (J B u T h0 : ℕ) (hu : 0<u) (hT : 0<T) (h0pos : 0<h0) (huB : u≤B)
    (hPbig : ∀ q∈P, B<q)
    (hCoarse : ∀ g : Fin (d+1), g.val<J →
      ∀ q∈sourceOriginalQActualBands r d L g, B<q)
    (hSat : ∀ g : Fin (d+1), J≤g.val →
      r≤b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) h0)
    (w : ℕ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (heq : h0*u*T=sourceOriginalPPrimePart P w*(p*orderedSkipProduct a)) :
    u=1 := by
  have hSat' (g : Fin (d+1)) (hg : J≤g.val) :
      r≤b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) (h0*T) := by
    have hs := hSat g hg
    have hm :
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) (h0*T) =
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) h0 +
        b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g) T := by
      simp only [b613QBandMultiplicity434,Nat.factorization_mul h0pos.ne' hT.ne',
        Finsupp.add_apply,Finset.sum_add_distrib]
    rw [hm]
    omega
  apply b613_actual_saturated_Q_small_multiplier_one434
    r d L hr hL P hDisj J B u (h0*T) hu (Nat.mul_pos h0pos hT)
      huB hPbig hCoarse hSat' w b slot δ p hp a
  calc
    (h0*T)*u=h0*u*T := by ring
    _=sourceOriginalPPrimePart P w*(p*orderedSkipProduct a) := heq
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## SourceQSkipActualDepth -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false

/-- Literal SourceOriginalMovingDepthCore, numerical admissibility 20 log L. -/
noncomputable def sourceOriginalDepthAdmissible
    (r₀ j : ℕ) (L : ℝ) : Prop :=
  20*Real.log L ≤ (5/(11*(r₀:ℝ)))/(2:ℝ)^j * L

/-- Literal SourceOriginalLiteralDepth search cutoff. -/
noncomputable def sourceOriginalDepthSearchBound (r₀ : ℕ) (L : ℝ) : ℕ :=
  ⌊((5/(11*(r₀:ℝ)))*L)/(20*Real.log L)⌋₊

/-- Exact original largest admissible depth, no replacement by an arbitrary
large or fixed number; Nat.findGreatest has its original small-L default. -/
noncomputable def sourceOriginalLiteralDepth (r₀ : ℕ) (L : ℝ) : ℕ :=
  Nat.findGreatest (fun j => sourceOriginalDepthAdmissible r₀ j L)
    (sourceOriginalDepthSearchBound r₀ L)

end Green64Analytic.SourceBlockSieve
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false

/-- The **actual r=6 source-normalized residual c(v)** with exactly the
largest admissible moving depth, original sorted-Q labels, designated index,
full factorial, signed Fourier phases, allocation and all prime repeats. -/
theorem source_native_original_six_QSkip_residual_norm_le_one434
    (L : ℝ) (hL : 0 < L)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (i : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → ℝ)
    (v : ℕ) :
    let d := sourceOriginalLiteralDepth 6 L
    let n := (sourceOrderedLabels 6 (sourceActualSortedScales 6 d L) b i).length
    let Q := sourceActualSortedQ 6 d L b i
    let s := sourceActualSortedFrequencyScales 6 d L b i
    ‖sourceEndpointFibre (Finset.univ : Finset (OrderedQSkip n Q δ))
      orderedSkipProduct
      (fun a => sourceActualSortedFactorial 6 d *
        orderedSkipPhase s ξ a) v‖ ≤ 1 := by
  exact source_actual_sorted_QSkip_residual_norm_le_one434
    6 (sourceOriginalLiteralDepth 6 L) L (by norm_num) hL b i δ ξ v

/-- The exact sign in original comparison source Eq. (1.4):
    orderedSkipPhase s (-xi), not a retuned frequency convention. -/
theorem source_native_original_six_QSkip_negative_frequency_c434
    (L : ℝ) (hL : 0 < L)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (i : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → ℝ)
    (v : ℕ) :
    let d := sourceOriginalLiteralDepth 6 L
    let n := (sourceOrderedLabels 6 (sourceActualSortedScales 6 d L) b i).length
    let Q := sourceActualSortedQ 6 d L b i
    let s := sourceActualSortedFrequencyScales 6 d L b i
    ‖sourceEndpointFibre
      (Finset.univ : Finset (OrderedQSkip n Q δ)) orderedSkipProduct
      (fun a => sourceActualSortedFactorial 6 d *
        orderedSkipPhase s (-ξ) a) v‖ ≤ 1 := by
  exact source_native_original_six_QSkip_residual_norm_le_one434
    L hL b i δ (-ξ) v
end Green64Analytic.ShiftTwoTerminal

end

end

