module

public import Green64.Library.Correlation.Part066
public import Green64.Library.Correlation.Part065
public import Mathlib

@[expose] public section

/-!
# Weights / Part096

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSharedPPartCap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Reindex the literal full-valuation P part; absent prime factors
contribute one, so no prime multiplicity is discarded. -/
theorem b575_original_Ppart_eq_full_product (P : Finset ℕ) (n : ℕ) :
    sourceOriginalPPrimePart P n=∏ p ∈ P,p^n.factorization p := by
  unfold sourceOriginalPPrimePart
  apply Finset.prod_subset Finset.inter_subset_right
  intro p hp hnot
  have hnp : p ∉ n.primeFactors := by
    intro hn
    exact hnot (Finset.mem_inter.mpr ⟨hn,hp⟩)
  have hf : n.factorization p=0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa only [Nat.support_factorization] using hnp
  simp only [hf,pow_zero]

/-- Exact multiplicativity of the same P part used by the native gated
kernel, including repeated primes at both endpoints. -/
theorem b575_original_Ppart_mul (P : Finset ℕ) (a b : ℕ)
    (ha : 0<a) (hb : 0<b) :
    sourceOriginalPPrimePart P (a*b)=
      sourceOriginalPPrimePart P a*sourceOriginalPPrimePart P b := by
  simp only [b575_original_Ppart_eq_full_product]
  rw [Nat.factorization_mul (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)]
  simp only [Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]

/-- A genuine P-supported shared dilation is completely retained by
Ppart, rather than being erased as it is by ordinaryPart. -/
theorem b575_original_Ppart_of_supported (P : Finset ℕ) (D : ℕ)
    (hD : 0<D) (hSupport : D.primeFactors⊆P) :
    sourceOriginalPPrimePart P D=D := by
  unfold sourceOriginalPPrimePart
  rw [Finset.inter_eq_left.mpr hSupport]
  exact (Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hD)).symm

/-- Exact physical-to-stripped P-part identity for every supported shared
product; no injectivity hypothesis suppresses repeated labels. -/
theorem b575_shared_dilation_Ppart (P : Finset ℕ) (D w : ℕ)
    (hD : 0<D) (hw : 0<w) (hSupport : D.primeFactors⊆P) :
    sourceOriginalPPrimePart P (D*w)=D*sourceOriginalPPrimePart P w := by
  rw [b575_original_Ppart_mul P D w hD hw,
    b575_original_Ppart_of_supported P D hD hSupport]

/-- The ORIGINAL cap at the physical endpoint is implied by a half-exponent
cap at the stripped endpoint and the true subexponential shared-product bound.
Both floors and all P valuations are retained. -/
theorem b575_shared_dilation_half_cap
    (P : Finset ℕ) (D w : ℕ) (σ L : ℝ)
    (hD : 0<D) (hw : 0<w) (hSupport : D.primeFactors⊆P)
    (hSmall : (D:ℝ)≤Real.exp ((σ/2)*L))
    (hPart : sourceOriginalPPrimePart P w≤⌊Real.exp ((σ/2)*L)⌋₊) :
    sourceOriginalPPrimePart P (D*w)≤⌊Real.exp (σ*L)⌋₊ := by
  rw [b575_shared_dilation_Ppart P D w hD hw hSupport]
  apply Nat.le_floor
  push_cast
  have hc : (sourceOriginalPPrimePart P w:ℝ)≤Real.exp ((σ/2)*L) := by
    exact (Nat.cast_le.mpr hPart).trans (Nat.floor_le (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp ((σ/2)*L)*Real.exp ((σ/2)*L) :=
      mul_le_mul hSmall hc (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (σ*L) := by rw [←Real.exp_add]; congr 1; ring

/-- A failed actual physical P cap lies in the genuine original half-threshold
Ppart tail. This is the support statement consumed by weighted Rankin. -/
theorem b575_failed_physical_Pcap_has_stripped_tail
    (P : Finset ℕ) (D w : ℕ) (σ L : ℝ)
    (hD : 0<D) (hw : 0<w) (hSupport : D.primeFactors⊆P)
    (hSmall : (D:ℝ)≤Real.exp ((σ/2)*L))
    (hFail : ⌊Real.exp (σ*L)⌋₊<sourceOriginalPPrimePart P (D*w)) :
    ⌊Real.exp ((σ/2)*L)⌋₊<sourceOriginalPPrimePart P w := by
  by_contra h
  have hh := b575_shared_dilation_half_cap P D w σ L hD hw hSupport hSmall (by omega)
  omega
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceQSkipActualBands -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Original s_j identity; original sourceOriginalPGroupScale is imported,
not redefined. -/
theorem source_original_Q_actual_scale_eq_P_scale434
    (r j : ℕ) (L : ℝ) (hr : 1 ≤ r) :
    sourceOriginalQActualExponent r j * L =
      sourceOriginalPGroupScale r L j := by
  have hr0 : (r:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr)
  unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    sourceOriginalPGroupScale
  have hp : (2:ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Original exact inclusive Q_j endpoint range. -/
theorem source_original_Q_actual_prime_range434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r)
    (j : Fin (d+1)) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands r d L j) :
    Real.exp (sourceOriginalPGroupScale r L j.val) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp ((6/5:ℝ)*sourceOriginalPGroupScale r L j.val) := by
  have hRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hs := source_original_Q_actual_scale_eq_P_scale434 r j.val L hr
  constructor
  · have h := (Nat.ceil_le).1 hRange.1
    rw [← hs]
    exact h
  · have hFloor := (Nat.floor_le (Real.exp_nonneg
        (((6/5:ℝ)*sourceOriginalQActualExponent r j.val)*L)))
    have hCast : (p:ℝ) ≤
        (⌊Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r j.val)*L)⌋₊:ℝ) := by
      exact_mod_cast hRange.2
    have hComp := hCast.trans hFloor
    have hEq : ((6/5:ℝ)*sourceOriginalQActualExponent r j.val)*L =
        (6/5:ℝ)*sourceOriginalPGroupScale r L j.val := by
      rw [← hs]
      ring
    rw [hEq] at hComp
    exact hComp

/-- Genuine distinct original Q bands are disjoint with inclusive endpoints. -/
theorem source_original_Q_actual_all_disjoint434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L) :
    ∀ j k : Fin (d+1), ∀ p,
      p ∈ sourceOriginalQActualBands r d L j →
      p ∈ sourceOriginalQActualBands r d L k → j = k := by
  intro j k p hpj hpk
  by_contra hNe
  have hval : j.val ≠ k.val := by
    intro hh
    exact hNe (Fin.ext hh)
  obtain hjk | hkj := lt_or_gt_of_ne hval
  · have hSep := source_original_P_actual_scale_dyadic_separation
      r j.val k.val L hr hL hjk
    have hPos : 0 < sourceOriginalPGroupScale r L k.val := by
      unfold sourceOriginalPGroupScale
      positivity
    have hGap : (6/5:ℝ)*sourceOriginalPGroupScale r L k.val <
        sourceOriginalPGroupScale r L j.val := by
      nlinarith
    have hjRange := source_original_Q_actual_prime_range434 r d L hr j p hpj
    have hkRange := source_original_Q_actual_prime_range434 r d L hr k p hpk
    have he := Real.exp_strictMono hGap
    linarith
  · have hSep := source_original_P_actual_scale_dyadic_separation
      r k.val j.val L hr hL hkj
    have hPos : 0 < sourceOriginalPGroupScale r L j.val := by
      unfold sourceOriginalPGroupScale
      positivity
    have hGap : (6/5:ℝ)*sourceOriginalPGroupScale r L j.val <
        sourceOriginalPGroupScale r L k.val := by
      nlinarith
    have hjRange := source_original_Q_actual_prime_range434 r d L hr j p hpj
    have hkRange := source_original_Q_actual_prime_range434 r d L hr k p hpk
    have he := Real.exp_strictMono hGap
    linarith
end Green64Analytic.SourceBlockSieve

end

end

