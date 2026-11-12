module

public import Green64.Library.Weights.MarkedJointInterval
public import Green64.Library.Correlation.Part066
public import Mathlib

@[expose] public section

/-!
# Correlation / CleanPhysicalRowEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## CleanPhysicalRowEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- On the genuine +2D affine row, one clean BIG prime can mark at most
one index before a complete prime residue period. This uses the physical
row equation, not a prime-distribution or character-orthogonality model. -/
theorem source_original_B553_clean_row_prime_unique434
    (t0 h0 e n D r s p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hrow : t0*n=e*h0+2*D) (hclean : ¬p ∣ D)
    (hr : r < p) (hs : s < p)
    (hpr : p ∣ h0+2*n*r) (hps : p ∣ h0+2*n*s) : r=s := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬p ∣ 2 := by
    intro hh
    have hle := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) hh
    omega
  have htwo : (2:ZMod p) ≠ 0 := by
    intro hh
    exact hp2 ((ZMod.natCast_eq_zero_iff 2 p).mp hh)
  have hD : (D:ZMod p) ≠ 0 := by
    intro hh
    exact hclean ((ZMod.natCast_eq_zero_iff D p).mp hh)
  have hzr : (h0:ZMod p)+2*(n:ZMod p)*(r:ZMod p)=0 := by
    have hh := (ZMod.natCast_eq_zero_iff (h0+2*n*r) p).mpr hpr
    push_cast at hh
    exact hh
  have hzs : (h0:ZMod p)+2*(n:ZMod p)*(s:ZMod p)=0 := by
    have hh := (ZMod.natCast_eq_zero_iff (h0+2*n*s) p).mpr hps
    push_cast at hh
    exact hh
  have hrowZ : (t0:ZMod p)*(n:ZMod p)=(e:ZMod p)*(h0:ZMod p)+2*(D:ZMod p) := by
    have hh := congrArg (fun z : ℕ => (z : ZMod p)) hrow
    push_cast at hh
    exact hh
  have hn : (n:ZMod p) ≠ 0 := by
    intro hn0
    have hh0 : (h0:ZMod p)=0 := by simpa only [hn0,mul_zero,zero_mul,add_zero] using hzr
    have hh : (2:ZMod p)*(D:ZMod p)=0 := by
      simpa only [hn0,hh0,mul_zero,zero_add] using hrowZ.symm
    exact (mul_ne_zero htwo hD) hh
  have heq : ((2:ZMod p)*(n:ZMod p))*(r:ZMod p)=
      ((2:ZMod p)*(n:ZMod p))*(s:ZMod p) := by
    linear_combination hzr-hzs
  have hrs := mul_left_cancel₀ (mul_ne_zero htwo hn) heq
  exact ((ZMod.natCast_eq_natCast_iff r s p).mp hrs).eq_of_lt_of_lt hr hs

/-- The original W-rough cofactor cannot carry a BIG prime at most W.
Thus its exact physical mark at t*h is a mark at h, with no lost powers. -/
theorem source_original_B553_rough_mark_divisor_transfer434
    (t h p : ℕ) (W : ℝ) (ht : SourceRoughAbove t W)
    (hp : p.Prime) (hpW : (p:ℝ) ≤ W) : p ∣ t*h ↔ p ∣ h := by
  have hpt : ¬p ∣ t := by
    intro hh
    exact (not_le_of_gt (ht p hp hh)) hpW
  rw [hp.dvd_mul]
  exact or_iff_right hpt

private theorem B553_norm_sum_sq_of_pointwise_disjoint
    {X : Type} (R : Finset ℕ) (F : ℕ → X → ℂ)
    (hdisj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ∀ a, F r a=0 ∨ F s a=0)
    (a : X) : ‖∑ r ∈ R, F r a‖^2 = ∑ r ∈ R, ‖F r a‖^2 := by
  by_cases hn : ∃ r ∈ R, F r a ≠ 0
  · obtain ⟨r,hr,hnr⟩ := hn
    have hzero : ∀ s ∈ R, s ≠ r → F s a=0 := by
      intro s hs hsr
      exact (hdisj s hs r hr hsr a).resolve_right hnr
    have hsum : (∑ s ∈ R, F s a)=F r a :=
      Finset.sum_eq_single r hzero (fun hh => False.elim (hh hr))
    have hsq : (∑ s ∈ R, ‖F s a‖^2)=‖F r a‖^2 :=
      Finset.sum_eq_single r (fun s hs hsr => by rw [hzero s hs hsr]; simp)
        (fun hh => False.elim (hh hr))
    rw [hsum,hsq]
  · have hz : ∀ r ∈ R, F r a=0 := by
      intro r hr
      by_contra hh
      exact hn ⟨r,hr,hh⟩
    rw [Finset.sum_eq_zero (fun r hr => hz r hr)]
    simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact (Finset.sum_eq_zero (fun r hr => by rw [hz r hr]; simp)).symm

section Original
variable {ι G : Type} [Fintype ι] [DecidableEq ι]
  [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (d : SourceComparisonData434 ι G cfg x L Y Hprime)
  (J ell m : ℕ) (hmJ : m ≤ J)

/-- Literal original ordered BIG-mark mask at the self-product
(t0+2er)(h0+2nr). For rough cofactor multipliers its mask equals the
original crossed-position mask, as proved below. The inherited test F
retains any Q/Delta, phases, prefactors, parity and additional gates;
no equality of full endpoint coefficients at different products is asserted. -/
def sourceOriginalB553PhysicalRowTest434
    (t0 h0 e n : ℕ)
    (F : ℕ → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (r : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  if (fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
        ((t0+2*e*r)*(h0+2*n*r)) then F r ν a else 0

/-- The exact CLEAN part of that same physical mark test. Auxiliary D
may have repeated primes. Its complementary dirty part is retained below. -/
def sourceOriginalB553CleanPhysicalRowTest434
    (t0 h0 e n D : ℕ)
    (F : ℕ → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (r : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  if Nat.Coprime D (h0+2*n*r) then
    sourceOriginalB553PhysicalRowTest434 d J ell m hmJ t0 h0 e n F r ν a else 0

/-- Exact clean/dirty decomposition: no auxiliary-overlap term is erased
by the following energy identity for the clean subfamily. -/
theorem source_original_B553_physical_clean_dirty_exact434
    (t0 h0 e n D r : ℕ)
    (F : ℕ → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalB553PhysicalRowTest434 d J ell m hmJ t0 h0 e n F r ν a =
      sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r ν a +
      (if Nat.Coprime D (h0+2*n*r) then 0 else
        sourceOriginalB553PhysicalRowTest434 d J ell m hmJ t0 h0 e n F r ν a) := by
  unfold sourceOriginalB553CleanPhysicalRowTest434
  split_ifs <;> simp

/-- Exact transfer of the FULL original ordered/injective mark-list mask
from the physical product t*h to the complementary endpoint h. -/
theorem source_original_B553_original_mark_mask_rough_transfer434
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (t h : ℕ) (W : ℝ) (ht : SourceRoughAbove t W)
    (hBigUpper : ∀ g p, p ∈ d.Tb g → (p:ℝ) ≤ W) :
    ((fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) (t*h)) ↔
    ((fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) h) := by
  simp only [bigMarkLists,Fintype.mem_piFinset,orderedBigMarks,Finset.mem_filter]
  constructor
  · intro hh g
    refine ⟨fun i => ?_,(hh g).2⟩
    have hi := Finset.mem_filter.mp ((hh g).1 i)
    exact Finset.mem_filter.mpr ⟨hi.1,
      (source_original_B553_rough_mark_divisor_transfer434 t h (a g i).val W ht
        (d.hTbPrime g _ (a g i).property) (hBigUpper g _ (a g i).property)).mp hi.2⟩
  · intro hh g
    refine ⟨fun i => ?_,(hh g).2⟩
    have hi := Finset.mem_filter.mp ((hh g).1 i)
    exact Finset.mem_filter.mpr ⟨hi.1,
      (source_original_B553_rough_mark_divisor_transfer434 t h (a g i).val W ht
        (d.hTbPrime g _ (a g i).property) (hBigUpper g _ (a g i).property)).mpr hi.2⟩

/-- The original integrated pair uses crossed positions t_s*h_r and
 t_r*h_s. This is the exact MASK-ONLY adapter from any rough cross
 multiplier to the rough self multiplier. Full endpoint coefficients at
 these positions are not identified by this theorem. -/
theorem source_original_B553_original_cross_self_mask434
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (tCross tSelf h : ℕ) (W : ℝ)
    (hcross : SourceRoughAbove tCross W) (hself : SourceRoughAbove tSelf W)
    (hBigUpper : ∀ g p, p ∈ d.Tb g → (p:ℝ) ≤ W) :
    ((fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) (tCross*h)) ↔
    ((fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) (tSelf*h)) := by
  exact (source_original_B553_original_mark_mask_rough_transfer434
    d J ell m hmJ ν a tCross h W hcross hBigUpper).trans
    (source_original_B553_original_mark_mask_rough_transfer434
      d J ell m hmJ ν a tSelf h W hself hBigUpper).symm

/-- Actual clean physical marked tests on a short integrated row have
pointwise disjoint support on ONE COMMON original nu-dependent carrier.
An actually present BIG group with an actual free slot is explicit. -/
theorem source_original_B553_clean_actual_mark_support_disjoint434
    (ν : SourceOriginalProbePattern434 G m) (g0 : G)
    (i0 : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g0))
    (R : Finset ℕ) (N t0 h0 e n D : ℕ) (W : ℝ)
    (hrow : t0*n=e*h0+2*D) (hR : ∀ r ∈ R, r < N)
    (hBigLower : ∀ p ∈ d.Tb g0, N ≤ p ∧ 3 ≤ p)
    (hBigUpper : ∀ p ∈ d.Tb g0, (p:ℝ) ≤ W)
    (c : ℕ → ℂ) (hrough : ∀ r ∈ R, c r ≠ 0 → SourceRoughAbove (t0+2*e*r) W)
    (F : ℕ → (η : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ η) → ℂ) :
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
    ∀ a : SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν),
      c r * sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r ν a=0 ∨
      c s * sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F s ν a=0 := by
  intro r hr s hs hrs a
  by_contra hn
  have hnr : c r * sourceOriginalB553CleanPhysicalRowTest434
      d J ell m hmJ t0 h0 e n D F r ν a ≠ 0 := by tauto
  have hns : c s * sourceOriginalB553CleanPhysicalRowTest434
      d J ell m hmJ t0 h0 e n D F s ν a ≠ 0 := by tauto
  have hcr : c r ≠ 0 := (mul_ne_zero_iff.mp hnr).1
  have hcs : c s ≠ 0 := (mul_ne_zero_iff.mp hns).1
  have hFr := (mul_ne_zero_iff.mp hnr).2
  have hFs := (mul_ne_zero_iff.mp hns).2
  have hcleanR : Nat.Coprime D (h0+2*n*r) := by
    by_contra hh
    simp only [sourceOriginalB553CleanPhysicalRowTest434,ite_eq_right hh] at hFr
    exact hFr rfl
  have hcleanS : Nat.Coprime D (h0+2*n*s) := by
    by_contra hh
    simp only [sourceOriginalB553CleanPhysicalRowTest434,ite_eq_right hh] at hFs
    exact hFs rfl
  have hmarkR : (fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
        ((t0+2*e*r)*(h0+2*n*r)) := by
    by_contra hh
    simp only [sourceOriginalB553CleanPhysicalRowTest434,ite_eq_left hcleanR,
      sourceOriginalB553PhysicalRowTest434,ite_eq_right hh] at hFr
    exact hFr rfl
  have hmarkS : (fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
        ((t0+2*e*s)*(h0+2*n*s)) := by
    by_contra hh
    simp only [sourceOriginalB553CleanPhysicalRowTest434,ite_eq_left hcleanS,
      sourceOriginalB553PhysicalRowTest434,ite_eq_right hh] at hFs
    exact hFs rfl
  simp only [bigMarkLists,Fintype.mem_piFinset,orderedBigMarks,Finset.mem_filter] at hmarkR hmarkS
  let p : ℕ := (a g0 i0).val
  have hpMem : p ∈ d.Tb g0 := (a g0 i0).property
  have hp : p.Prime := d.hTbPrime g0 p hpMem
  have hpR : p ∣ h0+2*n*r :=
    (source_original_B553_rough_mark_divisor_transfer434 (t0+2*e*r) (h0+2*n*r)
      p W (hrough r hr hcr) hp (hBigUpper p hpMem)).mp
        (Finset.mem_filter.mp ((hmarkR g0).1 i0)).2
  have hpS : p ∣ h0+2*n*s :=
    (source_original_B553_rough_mark_divisor_transfer434 (t0+2*e*s) (h0+2*n*s)
      p W (hrough s hs hcs) hp (hBigUpper p hpMem)).mp
        (Finset.mem_filter.mp ((hmarkS g0).1 i0)).2
  have hpD : ¬p ∣ D := by
    intro hh
    have hpg : p ∣ Nat.gcd D (h0+2*n*r) := Nat.dvd_gcd hh hpR
    rw [hcleanR.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  exact hrs (source_original_B553_clean_row_prime_unique434 t0 h0 e n D r s p
    hp (hBigLower p hpMem).2 hrow hpD
    ((hR r hr).trans_le (hBigLower p hpMem).1)
    ((hR s hs).trans_le (hBigLower p hpMem).1) hpR hpS)

/-- Exact harmonic L2 diagonalization of the GENUINE clean signed row
pool with the FULL B542 prime-product lift. The original mu(a)P(a)^2
weight remains inside every diagonal term. There is no row-length loss.
This is an endpoint-energy theorem, not a varying-k kernel bound. -/
theorem source_original_B553_true_lifted_clean_row_energy_diagonal434
    (ν : SourceOriginalProbePattern434 G m) (g0 : G) (hell : 0 < ell)
    (R : Finset ℕ) (N t0 h0 e n D : ℕ) (W : ℝ)
    (hrow : t0*n=e*h0+2*D) (hR : ∀ r ∈ R, r < N)
    (hBigLower : ∀ p ∈ d.Tb g0, N ≤ p ∧ 3 ≤ p)
    (hBigUpper : ∀ p ∈ d.Tb g0, (p:ℝ) ≤ W)
    (c : ℕ → ℂ) (hrough : ∀ r ∈ R, c r ≠ 0 → SourceRoughAbove (t0+2*e*r) W)
    (F : ℕ → (η : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ η) → ℂ) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        ∑ r ∈ R, c r * sourceOriginalB553CleanPhysicalRowTest434
          d J ell m hmJ t0 h0 e n D F r η a) ν =
      ∑ r ∈ R, ‖c r‖^2 * sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
        (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
          sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r η a) ν := by
  let X := SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
  let μ : X → ℝ := sourceOriginalVariableBIGMass434
    (fun g : G => {p : ℕ // p ∈ d.Tb g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    (sourceOriginalJointHarmonicMu434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (fun _ p => p.val) d.Vbig)
  let P : X → ℂ := fun a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a:ℂ)
  let f : ℕ → X → ℂ := fun r a =>
    sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r ν a
  have hfree : 0 < sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g0 := by
    unfold sourceOriginalProbeFreeMarkCount434
    omega
  let i0 : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g0) := ⟨0,hfree⟩
  have hdisj := source_original_B553_clean_actual_mark_support_disjoint434
    d J ell m hmJ ν g0 i0 R N t0 h0 e n D W hrow hR hBigLower hBigUpper c hrough F
  have hpoint (a : X) : ‖P a * ∑ r ∈ R, c r*f r a‖^2 =
      ∑ r ∈ R, ‖c r‖^2*‖P a*f r a‖^2 := by
    have hh := B553_norm_sum_sq_of_pointwise_disjoint R (fun r a => c r*f r a) hdisj a
    rw [norm_mul,mul_pow,hh,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [norm_mul,mul_pow]
    ring
  change (∑ a : X, μ a * ‖P a * ∑ r ∈ R, c r*f r a‖^2) =
    ∑ r ∈ R, ‖c r‖^2 * (∑ a : X, μ a*‖P a*f r a‖^2)
  calc
    _ = ∑ a : X, ∑ r ∈ R, μ a*(‖c r‖^2*‖P a*f r a‖^2) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hpoint,Finset.mul_sum]
    _ = ∑ r ∈ R, ∑ a : X, μ a*(‖c r‖^2*‖P a*f r a‖^2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- Counting form of the SAME clean row identity. One full numeric prime
product survives in every diagonal summand. This is not an unweighted
counting-law energy or a probability-one normalization. -/
theorem source_original_B553_true_lifted_clean_row_counting434
    (ν : SourceOriginalProbePattern434 G m) (g0 : G) (hell : 0 < ell)
    (R : Finset ℕ) (N t0 h0 e n D : ℕ) (W : ℝ)
    (hrow : t0*n=e*h0+2*D) (hR : ∀ r ∈ R, r < N)
    (hBigLower : ∀ p ∈ d.Tb g0, N ≤ p ∧ 3 ≤ p)
    (hBigUpper : ∀ p ∈ d.Tb g0, (p:ℝ) ≤ W)
    (c : ℕ → ℂ) (hrough : ∀ r ∈ R, c r ≠ 0 → SourceRoughAbove (t0+2*e*r) W)
    (F : ℕ → (η : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ η) → ℂ) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        ∑ r ∈ R, c r * sourceOriginalB553CleanPhysicalRowTest434
          d J ell m hmJ t0 h0 e n D F r η a) ν =
    sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν *
      ∑ r ∈ R, ‖c r‖^2 * ∑ a,
        sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a *
        ‖sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r ν a‖^2 := by
  rw [source_original_B553_true_lifted_clean_row_energy_diagonal434
    d J ell m hmJ ν g0 hell R N t0 h0 e n D W hrow hR hBigLower hBigUpper c hrough F]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [source_original_B542_true_C191_counting_pullback_energy434]
  ring

/-- Literal original sigma=1 full-cell D20 coefficient. Its existing
support theorem supplies W-roughness, so there is no new rough-support
hypothesis and no replacement by a cell-recentered coefficient. The
remaining factors b and F, the clean gate, and all diagonal prime weights
are kept unchanged. -/
theorem source_original_B553_actual_sigma_one_D20_row_diagonal434
    (ν : SourceOriginalProbePattern434 G m) (g0 : G) (hell : 0 < ell)
    (R : Finset ℕ) (N t0 h0 e n D : ℕ) (aExp : ℝ)
    (hWy : Real.exp (Real.sqrt L) ≤ Real.exp (aExp*L))
    (hrow : t0*n=e*h0+2*D) (hR : ∀ r ∈ R, r < N)
    (hBigLower : ∀ p ∈ d.Tb g0, N ≤ p ∧ 3 ≤ p)
    (hBigUpper : ∀ p ∈ d.Tb g0, (p:ℝ) ≤ Real.exp (Real.sqrt L))
    (b : ℕ → ℂ)
    (F : ℕ → (η : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434 (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ η) → ℂ) :
    let c : ℕ → ℂ := fun r =>
      (sourceD20FullDelta (1/L) (Real.exp (Real.sqrt L)) (Real.exp (aExp*L))
        (t0+2*e*r):ℂ) * b r
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        ∑ r ∈ R, c r * sourceOriginalB553CleanPhysicalRowTest434
          d J ell m hmJ t0 h0 e n D F r η a) ν =
      ∑ r ∈ R, ‖c r‖^2 * sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
        (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
          sourceOriginalB553CleanPhysicalRowTest434 d J ell m hmJ t0 h0 e n D F r η a) ν := by
  dsimp only
  apply source_original_B553_true_lifted_clean_row_energy_diagonal434
    d J ell m hmJ ν g0 hell R N t0 h0 e n D (Real.exp (Real.sqrt L))
    hrow hR hBigLower hBigUpper
  intro r hr hc
  apply original_D20_full_delta_support_SourceRoughAbove434
    (1/L) (Real.exp (Real.sqrt L)) (Real.exp (aExp*L)) (t0+2*e*r) hWy
  intro hz
  apply hc
  simp only [hz,Complex.ofReal_zero,zero_mul]

end Original
end Green64Analytic.CorrelationSquare

end

end

