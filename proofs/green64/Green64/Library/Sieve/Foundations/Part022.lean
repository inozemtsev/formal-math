module

public import Green64.Library.Sieve.Foundations.Part021
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Green64.Library.Analysis.Estimates.Part007
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Green64.Library.Sieve.Foundations.Part019
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Green64.Library.Sieve.Foundations.Part020

@[expose] public section

/-!
# Sieve / Foundations / Part022

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalDyadicEta -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- True ordinary-e scale attached to source dyadic level j; the
smallest is a=L^-88 and each successive scale doubles, with all
prime multiplicities in the actual source untouched. -/
def parityOriginalHistoricalDyadicEScale434 (a : ℝ) (j : ℕ) : ℝ :=
  ((2:ℝ)^j)*a

theorem parity_original_historical_dyadic_e_scale_pos434
    (a : ℝ) (ha : 0<a) (j : ℕ) :
    0<parityOriginalHistoricalDyadicEScale434 a j := by
  unfold parityOriginalHistoricalDyadicEScale434
  positivity

/-- Original source dyadic η_e family with all positive centres
c_j=2^j a no larger than one. The raw Finset.range cutoff
ceil(1/a)+2 is deliberately polynomial in 1/a, not guessed
O(log L); only finitely many true j survive the centre filter. -/
def parityOriginalHistoricalDyadicECentres434 (a : ℝ) : Finset ℕ :=
  (Finset.range (⌈1/a⌉₊+2)).filter
    (fun j => parityOriginalHistoricalDyadicEScale434 a j≤1)

/-- The original source number of dyadic candidate scales has a
literal bound ceil(1/a)+2, hence polynomial in L for a=L^-88. -/
theorem parity_original_historical_dyadic_e_centres_card434
    (a : ℝ) :
    (parityOriginalHistoricalDyadicECentres434 a).card ≤ ⌈1/a⌉₊+2 := by
  unfold parityOriginalHistoricalDyadicECentres434
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Every retained source centre lies between a and one. -/
theorem parity_original_historical_dyadic_e_centre_range434
    (a : ℝ) (ha : 0<a) (j : ℕ)
    (hj : j∈parityOriginalHistoricalDyadicECentres434 a) :
    a≤parityOriginalHistoricalDyadicEScale434 a j ∧
    parityOriginalHistoricalDyadicEScale434 a j≤1 := by
  have hTop := (Finset.mem_filter.mp hj).2
  have hp : (1:ℝ)≤(2:ℝ)^j := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  unfold parityOriginalHistoricalDyadicEScale434 at hTop ⊢
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hp ha.le],hTop⟩

/-- True source dyadic eta_e REAL nonnegative majorant built from
a finite union of fixed-ratio local smooth bumps and the fixed bump
at the final scale c=1. The number of levels is at most ceil(1/a)+2;
NOT an arbitrary smooth cutoff with unknown shrinking derivatives. -/
def parityOriginalHistoricalDyadicEtaEReal434
    (a : ℝ) (ha : 0<a) (x : ℝ) : ℝ :=
  (∑ j ∈ parityOriginalHistoricalDyadicECentres434 a,
      (parityOriginalHistoricalFixedRatioDyadicBump434
        (parityOriginalHistoricalDyadicEScale434 a j)
        (parity_original_historical_dyadic_e_scale_pos434 a ha j) x : ℝ)) +
    (parityOriginalFixedRatioDyadicReference434 x : ℝ)

/-- Every actual source dyadic eta_e is C∞, despite the moving
source lower scale a; each local bump uses the same fixed reference
profile and finite sums preserve real C∞. -/
theorem parity_original_historical_dyadic_eta_e_smooth434
    (a : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (parityOriginalHistoricalDyadicEtaEReal434 a ha) := by
  unfold parityOriginalHistoricalDyadicEtaEReal434
  have hSum : ContDiff ℝ ∞ (fun x : ℝ =>
      ∑ j ∈ parityOriginalHistoricalDyadicECentres434 a,
        (parityOriginalHistoricalFixedRatioDyadicBump434
          (parityOriginalHistoricalDyadicEScale434 a j)
          (parity_original_historical_dyadic_e_scale_pos434 a ha j) x : ℝ)) :=
    ContDiff.sum (fun j hj =>
      (parityOriginalHistoricalFixedRatioDyadicBump434
        (parityOriginalHistoricalDyadicEScale434 a j)
        (parity_original_historical_dyadic_e_scale_pos434 a ha j)).contDiff)
  exact hSum.add parityOriginalFixedRatioDyadicReference434.contDiff

/-- Source η_e alternative is everywhere NONNEGATIVE, before the
original Cauchy Gram is expanded, with no assumed cancellation. -/
theorem parity_original_historical_dyadic_eta_e_nonneg434
    (a : ℝ) (ha : 0<a) (x : ℝ) :
    0≤parityOriginalHistoricalDyadicEtaEReal434 a ha x := by
  unfold parityOriginalHistoricalDyadicEtaEReal434
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j hj
    exact (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a j)
      (parity_original_historical_dyadic_e_scale_pos434 a ha j)).nonneg
  · exact parityOriginalFixedRatioDyadicReference434.nonneg

/-- Even for moving a=L^-88, EVERY nonzero local source eta_e
component is supported inside the genuine historical interval
(a/2,2), because its true centre lies in [a,1]. -/
theorem parity_original_historical_dyadic_eta_e_component_support434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (j : ℕ) (hj : j∈parityOriginalHistoricalDyadicECentres434 a)
    (x : ℝ)
    (hx : (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a j)
      (parity_original_historical_dyadic_e_scale_pos434 a ha j) x : ℝ) ≠ 0) :
    a/2<x ∧ x<2 := by
  have hcen := parity_original_historical_dyadic_e_centre_range434 a ha j hj
  have hh := parity_original_historical_fixed_ratio_dyadic_bump_support434
    (parityOriginalHistoricalDyadicEScale434 a j)
    (parity_original_historical_dyadic_e_scale_pos434 a ha j) x hx
  constructor
  · linarith [hcen.1,hh.1]
  · linarith [hcen.2,hh.2]

/-- The ENTIRE finite nonnegative source eta_e majorant is
supported inside (a/2,2), not just each individual dyadic bump.
No missing compact-support boundary or fictitious first scale. -/
theorem parity_original_historical_dyadic_eta_e_support434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (x : ℝ)
    (hx : parityOriginalHistoricalDyadicEtaEReal434 a ha x≠0) :
    a/2<x ∧ x<2 := by
  by_contra hbad
  push_neg at hbad
  have hSumZero :
      (∑ j ∈ parityOriginalHistoricalDyadicECentres434 a,
        (parityOriginalHistoricalFixedRatioDyadicBump434
          (parityOriginalHistoricalDyadicEScale434 a j)
          (parity_original_historical_dyadic_e_scale_pos434 a ha j) x : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hn
    have hh := parity_original_historical_dyadic_eta_e_component_support434
      a ha ha1 j hj x hn
    exact (not_lt_of_ge (hbad hh.1)) hh.2
  have hRefZero : (parityOriginalFixedRatioDyadicReference434 x : ℝ)=0 := by
    by_contra hn
    have hh := parity_original_historical_fixed_ratio_dyadic_bump_support434
      1 (by norm_num) x hn
    have hlo : a/2<x := by linarith
    have hhi : x<2 := by linarith
    exact (not_lt_of_ge (hbad hlo)) hhi
  exact hx (by simp only [parityOriginalHistoricalDyadicEtaEReal434,hSumZero,hRefZero,zero_add])
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEtaCover -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Direct source dyadic ordinary-e cover of the shrinking window
[a,2/3): the fixed-ratio bump plateaux at centres 2^j*a and at
the NEXT doubled centre overlap at 4c/3. The chosen j is the true
natural binary-log of floor(x/a), not an unbounded external choice;
all candidate centres remain ≤1 and their count ≤ ceil(1/a)+2. -/
theorem parity_original_historical_dyadic_e_lower_window_plateau434
    (a x : ℝ) (ha : 0<a) (ha1 : a≤1)
    (hxLo : a≤x) (hxHi : x<2/3) :
    ∃ j ∈ parityOriginalHistoricalDyadicECentres434 a,
      (2/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j≤x ∧
      x≤(4/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j := by
  let t : ℝ := x/a
  let q : ℕ := ⌊t⌋₊
  let j : ℕ := Nat.log 2 q
  have hxpos : 0<x := ha.trans_le hxLo
  have ht1 : (1:ℝ)≤t := (le_div_iff₀ ha).mpr (by simpa [t] using hxLo)
  have htpos : 0≤t := by linarith
  have hq1 : 1≤q := Nat.le_floor (by simpa only [Nat.cast_one] using ht1)
  have hq0 : q≠0 := by omega
  have hqle : (q:ℝ)≤t := Nat.floor_le htpos
  have hqt : t < (q:ℝ)+1 := Nat.lt_floor_add_one t
  have hpowlo : 2^j≤q := Nat.pow_log_le_self 2 hq0
  have hpowhi : q < 2^(j+1) := by
    simpa only [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1<2) q)
  have hjle : j≤q := Nat.log_le_self 2 q
  have hqTop : q≤⌈1/a⌉₊ := by
    have hqtTop : t≤1/a := (div_le_div_of_nonneg_right (le_of_lt hxHi |>.trans (by norm_num : (2/3:ℝ)≤1)) ha.le)
    have hFloor : (q:ℝ)≤(⌈1/a⌉₊:ℝ) :=
      hqle.trans (hqtTop.trans (Nat.le_ceil (1/a)))
    exact_mod_cast hFloor
  have hjRange : j<⌈1/a⌉₊+2 := by omega
  have hPRealLo : ((2:ℝ)^j)≤(q:ℝ) := by exact_mod_cast hpowlo
  have hPRealHi : (q:ℝ)+1≤(2:ℝ)^(j+1) := by
    have hh : q+1≤2^(j+1) := by omega
    exact_mod_cast hh
  have htA : t*a=x := by
    dsimp [t]
    field_simp [ha.ne']
  have hcPos : 0<parityOriginalHistoricalDyadicEScale434 a j :=
    parity_original_historical_dyadic_e_scale_pos434 a ha j
  have hcLo : parityOriginalHistoricalDyadicEScale434 a j≤x := by
    unfold parityOriginalHistoricalDyadicEScale434
    calc
      ((2:ℝ)^j)*a ≤ (q:ℝ)*a := mul_le_mul_of_nonneg_right hPRealLo ha.le
      _ ≤ t*a := mul_le_mul_of_nonneg_right hqle ha.le
      _ = x := htA
  have hcHi : x<2*parityOriginalHistoricalDyadicEScale434 a j := by
    have htP : t < (2:ℝ)^(j+1) := lt_of_lt_of_le hqt hPRealHi
    have hh : x < ((2:ℝ)^(j+1))*a := by
      rw [←htA]
      exact mul_lt_mul_of_pos_right htP ha
    simpa only [parityOriginalHistoricalDyadicEScale434,pow_succ,mul_comm,mul_left_comm,mul_assoc] using hh
  have hjMem : j∈parityOriginalHistoricalDyadicECentres434 a := by
    unfold parityOriginalHistoricalDyadicECentres434
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjRange,hcLo.trans hxHi.le |>.trans (by norm_num : (2/3:ℝ)≤1)⟩
  by_cases hPlateau : x≤(4/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j
  · refine ⟨j,hjMem,?_,hPlateau⟩
    nlinarith [hcLo,hcPos]
  · have hNextPos : 0<parityOriginalHistoricalDyadicEScale434 a (j+1) :=
      parity_original_historical_dyadic_e_scale_pos434 a ha (j+1)
    have hNext : parityOriginalHistoricalDyadicEScale434 a (j+1) =
        2*parityOriginalHistoricalDyadicEScale434 a j := by
      simp only [parityOriginalHistoricalDyadicEScale434,pow_succ]
      ring
    have hNextLe : parityOriginalHistoricalDyadicEScale434 a (j+1)≤1 := by
      rw [hNext]
      have hh : (4/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j < x := lt_of_not_ge hPlateau
      nlinarith [hxHi]
    have hjNextRange : j+1<⌈1/a⌉₊+2 := by omega
    have hjNextMem : j+1∈parityOriginalHistoricalDyadicECentres434 a := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjNextRange,hNextLe⟩
    refine ⟨j+1,hjNextMem,?_,?_⟩
    · rw [hNext]
      nlinarith [lt_of_not_ge hPlateau]
    · rw [hNext]
      nlinarith [hcHi]

/-- The shrinking original historical e-window [a,1] is FULLY
covered by the plateaux of the finite fixed-ratio dyadic bumps and
the final fixed-scale bump c=1. No assumption about covering the
moving interval is introduced: it is proved from genuine Nat.log2
bounds and exact overlap of adjacent plateaux. -/
theorem parity_original_historical_dyadic_e_window_covered434
    (a x : ℝ) (ha : 0<a) (ha1 : a≤1)
    (hx : x∈Set.Icc a 1) :
    (2/3:ℝ)≤x ∨
      ∃ j∈parityOriginalHistoricalDyadicECentres434 a,
        (2/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j≤x ∧
        x≤(4/3:ℝ)*parityOriginalHistoricalDyadicEScale434 a j := by
  by_cases hh : (2/3:ℝ)≤x
  · exact Or.inl hh
  · exact Or.inr (parity_original_historical_dyadic_e_lower_window_plateau434
      a x ha ha1 hx.1 (lt_of_not_ge hh))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEtaMajorant -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- A SOURCE-TRUE and QUANTITATIVELY CONSTRUCTIVE η_e majorant:
for every moving historical a∈(0,1], its finite fixed-ratio dyadic
sum is at least ONE on the ENTIRE original e/E interval [a,1].
This is an actual full-interval covering theorem, not a conditional
assumption that the source smoothing can be chosen this way.
It does not assert the sum equals 1; Parity(4.10) requires >=1
on the positive Cauchy square. -/
theorem parity_original_historical_dyadic_eta_e_majorizes_window434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (x : ℝ) (hx : x∈Set.Icc a 1) :
    1≤parityOriginalHistoricalDyadicEtaEReal434 a ha x := by
  obtain hFinal | ⟨j,hj,hjLo,hjHi⟩ :=
    parity_original_historical_dyadic_e_window_covered434 a x ha ha1 hx
  · have hBOne : (parityOriginalFixedRatioDyadicReference434 x:ℝ)=1 :=
      parity_original_historical_fixed_ratio_dyadic_bump_one434
        1 (by norm_num) x ⟨by simpa using hFinal,by linarith [hx.2]⟩
    have hSumNonneg :
        0 ≤ ∑ j∈parityOriginalHistoricalDyadicECentres434 a,
          (parityOriginalHistoricalFixedRatioDyadicBump434
            (parityOriginalHistoricalDyadicEScale434 a j)
            (parity_original_historical_dyadic_e_scale_pos434 a ha j) x : ℝ) := by
      apply Finset.sum_nonneg
      intro i hi
      exact (parityOriginalHistoricalFixedRatioDyadicBump434
        (parityOriginalHistoricalDyadicEScale434 a i)
        (parity_original_historical_dyadic_e_scale_pos434 a ha i)).nonneg
    unfold parityOriginalHistoricalDyadicEtaEReal434
    rw [hBOne]
    linarith
  · have hBOne := parity_original_historical_fixed_ratio_dyadic_bump_one434
      (parityOriginalHistoricalDyadicEScale434 a j)
      (parity_original_historical_dyadic_e_scale_pos434 a ha j)
      x ⟨hjLo,hjHi⟩
    have hSingle :
        (parityOriginalHistoricalFixedRatioDyadicBump434
          (parityOriginalHistoricalDyadicEScale434 a j)
          (parity_original_historical_dyadic_e_scale_pos434 a ha j) x:ℝ) ≤
        ∑ i∈parityOriginalHistoricalDyadicECentres434 a,
          (parityOriginalHistoricalFixedRatioDyadicBump434
            (parityOriginalHistoricalDyadicEScale434 a i)
            (parity_original_historical_dyadic_e_scale_pos434 a ha i) x : ℝ) := by
      apply Finset.single_le_sum (a:=j)
      · intro i hi
        exact (parityOriginalHistoricalFixedRatioDyadicBump434
          (parityOriginalHistoricalDyadicEScale434 a i)
          (parity_original_historical_dyadic_e_scale_pos434 a ha i)).nonneg
      · exact hj
    have hBFinal : (0:ℝ)≤(parityOriginalFixedRatioDyadicReference434 x:ℝ) :=
      parityOriginalFixedRatioDyadicReference434.nonneg
    unfold parityOriginalHistoricalDyadicEtaEReal434
    rw [hBOne] at hSingle
    linarith

/-- The alternative actual original η_e is a C∞ COMPLEX profile,
nonnegative as a real function, with source support in (a/2,2),
and ≥1 on all [a,1]. It has ONE fixed source shape across dyadic
scales, allowing a genuine L-polynomial derivative estimate next. -/
def parityOriginalHistoricalDyadicEtaE434
    (a : ℝ) (ha : 0<a) (x : ℝ) : ℂ :=
  ((parityOriginalHistoricalDyadicEtaEReal434 a ha x:ℝ):ℂ)

theorem parity_original_historical_dyadic_eta_e_complex_smooth434
    (a : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (parityOriginalHistoricalDyadicEtaE434 a ha) :=
  Complex.ofRealCLM.contDiff.comp
    (parity_original_historical_dyadic_eta_e_smooth434 a ha)

theorem parity_original_historical_dyadic_eta_e_complex_support434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (x : ℝ)
    (hx : parityOriginalHistoricalDyadicEtaE434 a ha x ≠ 0) :
    a/2<x ∧ x<2 := by
  apply parity_original_historical_dyadic_eta_e_support434 a ha ha1 x
  intro hz
  exact hx (by simp [parityOriginalHistoricalDyadicEtaE434,hz])

theorem parity_original_historical_dyadic_eta_e_complex_majorant434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (x : ℝ) (hx : x∈Set.Icc a 1) :
    1≤(parityOriginalHistoricalDyadicEtaE434 a ha x).re := by
  simpa only [parityOriginalHistoricalDyadicEtaE434,Complex.ofReal_re] using
    parity_original_historical_dyadic_eta_e_majorizes_window434 a ha ha1 x hx
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEtaDerivatives -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact source eta_e finite dyadic-interval derivative identity:
all bump derivatives and the reference derivative are summed BEFORE
bounding. No nonexistent differentiation of a moving infinite product,
and no source e-window or physical parity factors are discarded. -/
theorem parity_original_historical_dyadic_eta_e_iterated_derivative_sum434
    (a : ℝ) (ha : 0<a) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (parityOriginalHistoricalDyadicEtaEReal434 a ha) x =
      (∑ i∈parityOriginalHistoricalDyadicECentres434 a,
        iteratedDeriv j (fun y : ℝ =>
          (parityOriginalHistoricalFixedRatioDyadicBump434
            (parityOriginalHistoricalDyadicEScale434 a i)
            (parity_original_historical_dyadic_e_scale_pos434 a ha i) y : ℝ)) x) +
      iteratedDeriv j (fun y : ℝ =>
        (parityOriginalFixedRatioDyadicReference434 y : ℝ)) x := by
  let S := parityOriginalHistoricalDyadicECentres434 a
  let F : ℕ → ℝ → ℝ := fun i y =>
    (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i) y : ℝ)
  let R : ℝ → ℝ := fun y => (parityOriginalFixedRatioDyadicReference434 y : ℝ)
  have hSmoothF : ∀ i∈S, ContDiffAt ℝ j (F i) x := by
    intro i hi
    exact (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i)).contDiff.contDiffAt
  have hSumSmooth : ContDiffAt ℝ j (fun y : ℝ => ∑i∈S,F i y) x :=
    (ContDiff.sum (fun i hi =>
      (parityOriginalHistoricalFixedRatioDyadicBump434
        (parityOriginalHistoricalDyadicEScale434 a i)
        (parity_original_historical_dyadic_e_scale_pos434 a ha i)).contDiff)).contDiffAt
  have hRefSmooth : ContDiffAt ℝ j R x :=
    parityOriginalFixedRatioDyadicReference434.contDiff.contDiffAt
  change iteratedDeriv j ((fun y : ℝ => ∑i∈S,F i y)+R) x =
    (∑i∈S,iteratedDeriv j (F i) x)+iteratedDeriv j R x
  rw [iteratedDeriv_add hSumSmooth hRefSmooth]
  have hFun : (fun y : ℝ => ∑i∈S,F i y) = (∑i∈S,F i) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hFun,iteratedDeriv_sum hSmoothF]

/-- FINITE SOURCE eta_e smoothing derivative majorant with ONE
fixed source reference seminorm K_j and explicit scale factor
a^-j*(ceil(1/a)+3). Since a=L^-88, the bound is polynomial in L
for each j. This is the quantitative estimate missing from the
single shrinking-radii bump in the earlier Parity(4.14) Fourier packet.
No analytic moment or TypeII conclusion is assumed here. -/
theorem parity_original_historical_dyadic_eta_e_derivative_norm_le434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEReal434 a ha) x‖ ≤
      (((⌈1/a⌉₊:ℕ):ℝ)+3) * (a⁻¹)^j *
        ((SchwartzMap.seminorm ℝ 0 j)
          parityOriginalFixedRatioDyadicReferenceSchwartz434) := by
  let S := parityOriginalHistoricalDyadicECentres434 a
  let F : ℕ → ℝ → ℝ := fun i y =>
    (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i) y : ℝ)
  let R : ℝ → ℝ := fun y => (parityOriginalFixedRatioDyadicReference434 y : ℝ)
  let K : ℝ := (SchwartzMap.seminorm ℝ 0 j)
    parityOriginalFixedRatioDyadicReferenceSchwartz434
  let B : ℝ := (a⁻¹)^j * K
  have hK : 0≤K := apply_nonneg _ _
  have hAinv : (1:ℝ)≤a⁻¹ := by
    have hh : a⁻¹≥1 := (one_le_inv₀ ha).mpr ha1
    exact hh
  have hBpos : 0≤B := mul_nonneg (pow_nonneg (by positivity) _) hK
  have hLocal (i : ℕ) (hi : i∈S) :
      ‖iteratedDeriv j (F i) x‖ ≤ B := by
    have hc := parity_original_historical_dyadic_e_centre_range434 a ha i hi
    have hBase := parity_original_historical_fixed_ratio_dyadic_derivative_norm_le434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i) j x
    have hci : 0<parityOriginalHistoricalDyadicEScale434 a i :=
      parity_original_historical_dyadic_e_scale_pos434 a ha i
    have hInv : (parityOriginalHistoricalDyadicEScale434 a i)⁻¹≤a⁻¹ :=
      (inv_le_inv₀ hci ha).mpr hc.1
    have hPow : ((parityOriginalHistoricalDyadicEScale434 a i)⁻¹)^j≤(a⁻¹)^j :=
      pow_le_pow_left₀ (inv_nonneg.mpr hci.le) hInv j
    exact hBase.trans (mul_le_mul_of_nonneg_right hPow hK)
  have hSum : ‖∑i∈S,iteratedDeriv j (F i) x‖ ≤
      (S.card:ℝ)*B := by
    calc
      _ ≤ ∑i∈S,‖iteratedDeriv j (F i) x‖ := norm_sum_le S _
      _ ≤ ∑_i∈S,B := Finset.sum_le_sum (fun i hi => hLocal i hi)
      _ = (S.card:ℝ)*B := by simp
  have hRefBase : ‖iteratedDeriv j R x‖≤K := by
    have hFunction : R = (parityOriginalFixedRatioDyadicReferenceSchwartz434:ℝ→ℝ) := by
      funext y
      rfl
    rw [hFunction]
    have hh := SchwartzMap.le_seminorm' ℝ 0 j
      parityOriginalFixedRatioDyadicReferenceSchwartz434 x
    simpa only [pow_zero,one_mul] using hh
  have hRef : ‖iteratedDeriv j R x‖≤B := by
    have hPow : (1:ℝ)≤(a⁻¹)^j := one_le_pow₀ hAinv
    exact hRefBase.trans (by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_right hPow hK])
  have hCard := parity_original_historical_dyadic_e_centres_card434 a
  have hCardR : (S.card:ℝ)≤((⌈1/a⌉₊:ℕ):ℝ)+2 := by
    dsimp [S] at hCard ⊢
    exact_mod_cast hCard
  have hD := parity_original_historical_dyadic_eta_e_iterated_derivative_sum434 a ha j x
  change ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEReal434 a ha) x‖ ≤
      (((⌈1/a⌉₊:ℕ):ℝ)+3)*(a⁻¹)^j*K
  rw [hD]
  calc
    _ ≤ ‖∑i∈S,iteratedDeriv j (F i) x‖+‖iteratedDeriv j R x‖ := norm_add_le _ _
    _ ≤ (S.card:ℝ)*B+B := add_le_add hSum hRef
    _ = ((S.card:ℝ)+1)*B := by ring
    _ ≤ (((⌈1/a⌉₊:ℕ):ℝ)+3)*B :=
      mul_le_mul_of_nonneg_right (by linarith) hBpos
    _ = _ := by dsimp [B,K]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEtaAllLog -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- The actual source historical e smoothing length a=L^-88.
The alternative actual η_e is a finite positive smooth union of
dyadic profile translates; unlike one shrinking-ratio bump, its
native derivative constants are all taken from ONE fixed Schwartz
reference profile independent of L, K0, k,Z, Fourier tail order. -/
def parityOriginalHistoricalDyadicEtaEAtLReal434
    (L : ℝ) (hL : 8≤L) : ℝ → ℝ :=
  parityOriginalHistoricalDyadicEtaEReal434 (L^(-88:ℝ))
    (parity_original_historical_real_e_eta_parameter434 L hL).1

/-- Exact source e length a=L^-88: inverse a^-1 is L^88, so
shrinking smooth source scales are polynomial in L, not exponential
in L or dependent on the original physical k and Fourier precision. -/
theorem parity_original_historical_dyadic_e_inverse_scale434
    (L : ℝ) (hL : 8≤L) :
    (L^(-88:ℝ))⁻¹=L^(88:ℝ) := by
  have hLp : 0<L := by linarith
  rw [Real.rpow_neg hLp.le]
  simp

/-- The actual source number of local η_e cutoffs costs at most
`L^88+2`, a polynomial in logarithmic L, not a moving exponential
or an illegitimate constant independent of the original e-window. -/
theorem parity_original_historical_dyadic_eta_e_level_budget434
    (L : ℝ) (hL : 8≤L) :
    (((⌈1/(L^(-88:ℝ))⌉₊:ℕ):ℝ)+3) ≤ L^(88:ℝ)+4 := by
  have hLp : 0<L := by linarith
  have ha := (parity_original_historical_real_e_eta_parameter434 L hL).1
  have hnonneg : 0≤1/(L^(-88:ℝ)) := by positivity
  have hCeil := Nat.ceil_lt_add_one hnonneg
  have hscale : 1/(L^(-88:ℝ)) = L^(88:ℝ) := by
    rw [one_div]
    exact parity_original_historical_dyadic_e_inverse_scale434 L hL
  rw [hscale] at hCeil
  rw [hscale]
  linarith [hCeil]

/-- The original shrinking e-window requires L^88≥4 for L≥8;
this pays the absolute two endpoint and cardinality constants in
the genuine fixed-ratio dyadic smoothing derivative bound. -/
theorem parity_original_historical_dyadic_e_power88_ge_four434
    (L : ℝ) (hL : 8≤L) :
    (4:ℝ)≤L^(88:ℝ) := by
  have hL2 : (2:ℝ)≤L := by linarith
  have hpow : (2:ℝ)^88≤L^88 :=
    pow_le_pow_left₀ (by norm_num) hL2 88
  have hh : (4:ℝ)≤L^88 :=
    (by norm_num : (4:ℝ)≤(2:ℝ)^88).trans hpow
  simpa only [show (88:ℝ) = ↑(88:ℕ) by norm_num, Real.rpow_natCast] using hh

/-- UNIFORM ORIGINAL Parity(4.10) smooth moving e-majorant ALL-ORDER
source derivative bound in the exact requested polynomial-log shape:
for every integer derivative order j and every real x,

 ‖d^j eta_e,L(x)‖ ≤ 2*K_j*L^(88*(j+1)),

where K_j is ONE actual fixed Schwartz seminorm of the unit dyadic
reference function, CHOSEN BEFORE L, source e,n data, k,Z, target
accuracy and Fourier tail precision. No unknown L-dependent smooth
cutoff constant is hidden. This is a quantitative historical
source-appropriate replacement for the earlier shrinking-ratio bump. -/
theorem parity_original_historical_dyadic_eta_e_all_derivatives_polylog434
    (L : ℝ) (hL : 8≤L) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEAtLReal434 L hL) x‖ ≤
      2 * (L^(88:ℝ))^(j+1) *
        ((SchwartzMap.seminorm ℝ 0 j)
          parityOriginalFixedRatioDyadicReferenceSchwartz434) := by
  let a : ℝ := L^(-88:ℝ)
  let K : ℝ := (SchwartzMap.seminorm ℝ 0 j)
    parityOriginalFixedRatioDyadicReferenceSchwartz434
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hBase := parity_original_historical_dyadic_eta_e_derivative_norm_le434
    a ha.1 ha.2 j x
  have hCount := parity_original_historical_dyadic_eta_e_level_budget434 L hL
  have hExp4 := parity_original_historical_dyadic_e_power88_ge_four434 L hL
  have hPow : 0≤(L^(88:ℝ))^j := by positivity
  have hK : 0≤K := apply_nonneg _ _
  have hScale : (a⁻¹)^j = (L^(88:ℝ))^j := by
    rw [parity_original_historical_dyadic_e_inverse_scale434 L hL]
  have hCount2 : (((⌈1/a⌉₊:ℕ):ℝ)+3)≤2*L^(88:ℝ) := by
    change (((⌈1/(L^(-88:ℝ))⌉₊:ℕ):ℝ)+3)≤2*L^(88:ℝ)
    linarith [hCount,hExp4]
  change ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEReal434 a ha.1) x‖ ≤
    2*(L^(88:ℝ))^(j+1)*K
  calc
    _ ≤ (((⌈1/a⌉₊:ℕ):ℝ)+3)*(a⁻¹)^j*K := hBase
    _ ≤ (2*L^(88:ℝ))*(L^(88:ℝ))^j*K := by
      rw [hScale]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCount2 hPow) hK
    _ = 2*(L^(88:ℝ))^(j+1)*K := by
      rw [pow_succ]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicWeightedJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine SOURCE smoothing for historical Parity (4.10), replacing the
shrinking-base-profile eta_e by a finite fixed-ratio dyadic source
majorant with proven uniform polynomial derivatives. The n cutoff
remains the actual fixed [1,2] native smooth bump. -/
def parityOriginalHistoricalDyadicEtaWeight434
    (L E V : ℝ) (hL : 8 ≤ L) (e n : ℕ) : ℝ :=
  parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E) *
    (parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V)).re

/-- On actual original selected e∈[E L^-88,E], the new QUANTITATIVE
source eta_e is ≥1. The e argument is exactly e/E and not an
independently manufactured e-variable. -/
theorem parity_original_historical_dyadic_eta_e_at_source_ge_one434
    (L E : ℝ) (hL : 8 ≤ L) (hE : 0 < E)
    (e : ℕ) (hwin : parityOriginalHistoricalEWindow434 L E e) :
    1 ≤ parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E) := by
  let a := L^(-88:ℝ)
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hlo : a ≤ (e:ℝ)/E := (le_div_iff₀ hE).mpr (by
    change a*E ≤ (e:ℝ)
    calc
      _ = E*a := by ring
      _ ≤ (e:ℝ) := hwin.1)
  have hhi : (e:ℝ)/E ≤ 1 := (div_le_iff₀ hE).mpr (by
    simpa only [one_mul] using hwin.2)
  exact parity_original_historical_dyadic_eta_e_majorizes_window434
    a ha.1 ha.2 ((e:ℝ)/E) ⟨hlo,hhi⟩

/-- The true two-ended smoothing weight in original Parity(4.10) is ≥1
on all source selected e windows and n/V∈[1,2]. The old source
single-bump eta_e had equality 1, but quantitative control was
missing; this new finite source dyadic majorant only needs ≥1. -/
theorem parity_original_historical_dyadic_eta_weight_source_ge_one434
    (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (e n : ℕ) (hwin : parityOriginalHistoricalEWindow434 L E e)
    (hnLo : V≤(n:ℝ)) (hnHi : (n:ℝ)≤2*V) :
    1≤parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n := by
  unfold parityOriginalHistoricalDyadicEtaWeight434
  rw [parity_original_historical_eta_n_at_source_n_one434 V hV n hnLo hnHi]
  simpa only [Complex.one_re,mul_one] using
    parity_original_historical_dyadic_eta_e_at_source_ge_one434 L E hL hE e hwin

/-- ORIGINAL positive smooth-weighted selected-e Cauchy majorant
with quantitative all-order η_e derivatives, no postulated
smooth cutoff, and true original h=-2 physical Cauchy coefficients. -/
theorem parity_original_historical_dyadic_eta_weighted_Cauchy434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hnRange : ∀ n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
      parityOriginalHistoricalWeightedActiveCauchySquare434
        d L E band slot δ ξ rho K J α signed Y
        (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) := by
  apply parity_original_historical_signed_weighted_active_Cauchy434
    d L E band slot δ ξ rho K J α β signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hL)
  intro e he n hn
  exact parity_original_historical_dyadic_eta_weight_source_ge_one434
    L E V hL hE hV e n (Finset.mem_filter.mp he).2
    (hnRange n hn).1 (hnRange n hn).2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicFullJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- COMPLETE TRUE source Parity(4.10)->(4.13) smooth-weighted Cauchy
WITH an η_e that has an unconditional all-order bound
2*K_j*L^(88(j+1)) proved from a finite family of actual smooth
fixed-ratio dyadic source bumps; the complex n and e source
weights are not replaced by abstract Schwartz multipliers.
AND the exact signed complex character/dyadic-k-Z physical reduction
for both signed ε branches, with genuinely CONSTRUCTED η_e and η_n,
not abstract majorant hypotheses. Its selected-Q e-window includes
the moving L^-88 support, both original physical Q/P gates and all
b629 fine alpha, true h=-2 k and z=m'v, original conjugations,
character modulus 2|k| and physical double source n-fibre.

This proves the complete SOURCE-to-character/dyadic algebra before
(4.17); it does NOT prove uniform Fourier-moment polynomial decay,
the final Parity (4.17) full signed kernel identification, Type II(4.2),
or Green64.green_64. -/
theorem parity_eventually_original_dyadic_eta_alllog_weighted_cauchy_to_character_Z434
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
        (U V E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ) (β : ℕ → ℂ),
      0<U → 0<V → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V
        hLw
      let Ns := parityOriginalHistoricalWeightedActiveCauchySquare434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let D := parityOriginalHistoricalWeightedActiveDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let OD := parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      (‖parityOriginalHistoricalCauchyAtDelta434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
        (∑e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ,
          ∑n∈J,‖parityOriginalHistoricalWindowAE434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2)*Ns)
       ∧ ((Ns:ℝ):ℂ)=((D:ℝ):ℂ)+OD := by
  filter_upwards [parity_eventually_original_historical_weighted_fine_offdiag_character_dyadic434
    S beta gamma K0 hS hbeta hgamma,
    eventually_ge_atTop (8:ℝ)] with L hOff hL8
  refine ⟨hL8,?_⟩
  intro hLw band slot δ ξ U V E rho K J prime signed lFine uFine β
    hU hV hScale hDyad hNrange hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  have hLp : 0<L := by linarith
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hCauchy := parity_original_historical_dyadic_eta_weighted_Cauchy434
    (sourceOriginalLiteralDepth 20 L) L E V hLw hEpos hV
    band slot δ ξ rho K J alpha β signed ⌊2*Real.exp L⌋₊ hNrange
  have hGram := parity_original_historical_weighted_active_square_diag_offdiag434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
    K J alpha signed ⌊2*Real.exp L⌋₊ w
  have hOD := hOff.2 band slot δ ξ U E rho K J prime signed
    lFine uFine w hU hScale hDyad hl hFineLow
  rw [hOD] at hGram
  exact ⟨hCauchy,hGram⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadic3DFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine COMPLEX smoothing function at original L^-88 source
scale, constructed by casting the quantitatively bounded real finite
dyadic eta_e, not by assuming the existence of a smooth cutoff. -/
def parityOriginalHistoricalDyadicEtaEAtLComplex434
    (L : ℝ) (hL : 8 ≤ L) (x : ℝ) : ℂ :=
  ((parityOriginalHistoricalDyadicEtaEAtLReal434 L hL x : ℝ):ℂ)

/-- SOURCE eta_e,L from the finite fixed-ratio majorant is truly
C-infinity over ℝ. The same function has a proved L-polynomial
j-th REAL derivative bound for every j, not just smoothness. -/
theorem parity_original_historical_dyadic_eta_e_L_complex_smooth434
    (L : ℝ) (hL : 8≤L) :
    ContDiff ℝ ∞ (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) := by
  unfold parityOriginalHistoricalDyadicEtaEAtLComplex434
    parityOriginalHistoricalDyadicEtaEAtLReal434
  exact Complex.ofRealCLM.contDiff.comp
    (parity_original_historical_dyadic_eta_e_smooth434
      (L^(-88:ℝ)) (parity_original_historical_real_e_eta_parameter434 L hL).1)

/-- Exact identification of the ACTUAL real smooth Cauchy weight
with the unaltered product of real-valued COMPLEX eta_e and eta_n
functions required by Parity's 3D Fourier inversion. In particular no
complex phase, sign, or modulus is lost in casting the source weight. -/
theorem parity_original_historical_dyadic_eta_weight_is_complex_product434
    (L E V : ℝ) (hL : 8≤L) (e n : ℕ) :
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n : ℝ):ℂ) =
      parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL ((e:ℝ)/E) *
        parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V) := by
  unfold parityOriginalHistoricalDyadicEtaWeight434
    parityOriginalHistoricalDyadicEtaEAtLComplex434
    parityOriginalHistoricalActualEtaN434
  simp only [Complex.ofReal_re,Complex.ofReal_mul]

/-- EXACT Parity (4.14) Fourier inversion for the FULL ACTUAL original
finite fixed-ratio, moving L^-88 dyadic source eta_e paired with the
true fixed smooth η_n(n/V). The fixed auxiliary logarithmic buffer
is constructed inside the theorem; on real SOURCE dyads no spurious
buffer factor survives. Requires the original actual populated Q/P
h=-2 physical n source and canonical z=m'v. The 2π phases are genuine.
This is an analytic identity, not yet the terminal (4.17) saving. -/
theorem parity_original_historical_true_dyadic_eta_3d_fourier_exists434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E)
    (hV : 0<V) (hZ : 0<Z)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ))
    (hzHi : (parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)≤2*Z) :
    ∃ (A : ℝ) (buf : ℝ → ℂ)
      (hBufSmooth : ContDiff ℝ ∞ buf)
      (hBufSupport : ∀ t : ℝ, buf t ≠ 0 →
        -Real.log A≤t ∧ t≤Real.log A),
      64≤A ∧
      parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL ((e:ℝ)/E) *
        parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V) =
        ∫ ξ : EuclideanSpace ℝ (Fin 3),
          (Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) *
           Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
           Complex.exp (((2*Real.pi*(ξ 2)*Real.log
             ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)/Z):ℝ):ℂ)*Complex.I)) *
          (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
            U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
            buf (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
            parityOriginalHistoricalActualEtaN434
            (-Real.log A) (Real.log A)
            hBufSmooth
            (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
            parity_original_historical_actual_eta_n_smooth434 hBufSupport) :
            𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  exact parity_original_historical_true_source_3d_fourier_exists434
    d L band slot δ Y e m mp n he hneq hValid U E V Z
    hU hE hV hZ hmLo hmHi hmpLo hmpHi hzLo hzHi
    (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
    parityOriginalHistoricalActualEtaN434
    (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadic3DTailFinite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ACTUAL constructed original historical Parity (4.14) eta_e
finite dyadic majorant, eta_n source fixed bump, and source-true
three-dimensional logarithmic pullback are assembled into a
Schwartz function with ALL original Fourier 2π normalization,
without postulating an eta_e profile or its smoothness. -/
def parityOriginalHistoricalActualDyadicCutoffSchwartz434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b) :
    𝓢(EuclideanSpace ℝ (Fin 3),ℂ) :=
  parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
    buf (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
    parityOriginalHistoricalActualEtaN434 a b
    hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport

/-- ORIGINAL Parity (4.15) ACTUAL complete three-dimensional
high-frequency Fourier tail with source derivative finite seminorm
instead of an unexplained L,k,Z-dependent Schwartz moment:

  tail_{||xi||>T} <= B_H(source η_e,L η_n)/T^H.

Every source eta is truly constructed, η_e,L has proved
uniform all-order polynomial real derivatives, and this B_H depends
only on finitely many ORIGINAL 3D source cutoff derivatives.
Proving B_H <= L^C is a separate composition estimate. -/
theorem parity_original_historical_true_dyadic_eta_3d_tail_finite434
    (H : ℕ) (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (T : ℝ) (hT : 0<T) :
    (∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T} : Set _)ᶜ,
      ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) ≤
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport) / T^H := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  have ht := parity_original_historical_3d_fourier_tail_le_moment434
    H U E V Z k buf etaE etaN a b
    hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport T hT
  have hm := parity_original_historical_actual_3d_fourier_moment_source_finite434
    H U E V Z k buf etaE etaN a b
    hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport
  change (∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _)ᶜ,
      ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) ≤
    parityOriginal3DSourceMomentFiniteBudget434 H f / T^H
  exact ht.trans (div_le_div_of_nonneg_right hm (pow_nonneg hT.le H))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadic3DTrunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- SOURCE-TRUE native Parity (4.14) actual 3-dimensional Fourier
inversion TRUNCATED to the real Euclidean ball ||xi||<=T, with an
EXPLICIT error bounded by finitely many SOURCE derivatives of the
constructed moving η_e,L and the genuine η_n cutoff. No synthetic
Fourier kernel and no postulated Fourier moment smallness. -/
theorem parity_original_historical_actual_dyadic_eta_3d_truncation434
    (H : ℕ) (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (t : EuclideanSpace ℝ (Fin 3))
    (T : ℝ) (hT : 0<T) :
    ‖parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport t -
      (∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        Complex.exp (((2*Real.pi*⟪ξ,t⟫:ℝ):ℂ)*Complex.I) *
        (𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)‖ ≤
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport) / T^H := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  let g : EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ =>
    Complex.exp (((2*Real.pi*⟪ξ,t⟫:ℝ):ℂ)*Complex.I) * F ξ
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {ξ | ‖ξ‖≤T}
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  have hG : Integrable g := by
    have hF : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => F ξ) := F.integrable
    have hC : Continuous g := by
      dsimp [g]
      fun_prop
    apply hF.mono hC.aestronglyMeasurable
    filter_upwards [] with ξ
    simp only [g,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,le_refl]
  have hInv := parity_original_historical_pulled_3d_fourier_inversion434
    U E V Z k buf etaE etaN a b hBufSmooth
    (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport t
  have hFull : f t = ∫ξ : EuclideanSpace ℝ (Fin 3),g ξ := hInv
  have hSplit := integral_add_compl hS hG
  have hEq : f t - (∫ξ in S,g ξ) = ∫ξ in Sᶜ,g ξ := by
    rw [hFull,←hSplit]
    abel
  change ‖f t - ∫ξ in S,g ξ‖ ≤
    parityOriginal3DSourceMomentFiniteBudget434 H f / T^H
  rw [hEq]
  calc
    ‖∫ξ in Sᶜ,g ξ‖ ≤ ∫ξ in Sᶜ,‖g ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ξ in Sᶜ,‖F ξ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [g,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    _ ≤ _ := parity_original_historical_true_dyadic_eta_3d_tail_finite434
      H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicComplexDeriv -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- For EVERY derivative order, complexification of any smooth REAL
source cutoff commutes with iterated differentiation. This transfers
the fixed-profile real quantitative η_e source estimates to the
actual COMPLEX cutoff used in native 3D Fourier inversion. -/
theorem parity_original_real_to_complex_all_iterated_derivatives434
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => ((f y : ℝ) : ℂ)) x =
      ((iteratedDeriv j f x : ℝ) : ℂ) := by
  have hh := Complex.ofRealCLM.iteratedFDeriv_comp_left
    (hf.contDiffAt (x:=x)) (i := j) (by simp : (j:ℕ∞ω) ≤ ∞)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ f) x)
    (fun _ : Fin j => 1) = _
  rw [hh]
  rfl

/-- ACTUAL SOURCE η_e,L complex 3D Fourier weight satisfies the
same j-th derivative L-polynomial estimate as its real finite
dyadic precursor. Source construction is fully explicit: one
fixed Schwartz profile, ≤ ceil(L^88)+2 local centres and no
shrinking-ratio unknown derivative constants. -/
theorem parity_original_historical_dyadic_complex_eta_e_all_derivatives_polylog434
    (L : ℝ) (hL : 8≤L) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x‖ ≤
      2*(L^(88:ℝ))^(j+1)*
        ((SchwartzMap.seminorm ℝ 0 j)
          parityOriginalFixedRatioDyadicReferenceSchwartz434) := by
  let f := parityOriginalHistoricalDyadicEtaEAtLReal434 L hL
  have hsmooth : ContDiff ℝ ∞ f := by
    exact parity_original_historical_dyadic_eta_e_smooth434
      (L^(-88:ℝ)) (parity_original_historical_real_e_eta_parameter434 L hL).1
  have hEq : iteratedDeriv j
       (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x =
      ((iteratedDeriv j f x:ℝ):ℂ) := by
    exact parity_original_real_to_complex_all_iterated_derivatives434 f hsmooth j x
  rw [hEq,Complex.norm_real]
  exact parity_original_historical_dyadic_eta_e_all_derivatives_polylog434 L hL j x

/-- Fixed original source H-dependent but L-independent derivative
constants, defined exclusively from the REAL fixed reference profile.
No postulated eta_e derivative function K_j. -/
def parityOriginalHistoricalDyadicEtaFixedDerivativeK434 (j : ℕ) : ℝ :=
  2*((SchwartzMap.seminorm ℝ 0 j)
      parityOriginalFixedRatioDyadicReferenceSchwartz434)

theorem parity_original_historical_dyadic_eta_fixed_K_nonneg434
    (j : ℕ) : 0 ≤ parityOriginalHistoricalDyadicEtaFixedDerivativeK434 j := by
  unfold parityOriginalHistoricalDyadicEtaFixedDerivativeK434
  positivity

/-- Native SOURCE quantitative L-derivative budget under the exact
original `sourceLogDerivativeBudget` convention. Its C=88 and
K_j=2*fixedSchwartzSeminorm were proved for the actual moving
finite dyadic η_e,L, not assumed. The argument is the original
real cutoff variable x=e/E; composition with e^t in (4.14)
remains a distinct, explicitly tracked analytic obligation. -/
theorem parity_original_historical_dyadic_complex_eta_source_derivative_budget434
    (L : ℝ) (hL : 8≤L) :
    sourceLogDerivativeBudget 88
      parityOriginalHistoricalDyadicEtaFixedDerivativeK434
      L (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) := by
  intro j x
  have hLpos : 0<L := by linarith
  have hPoint := parity_original_historical_dyadic_complex_eta_e_all_derivatives_polylog434
    L hL j x
  have hp : (L^(88:ℝ))^(j+1) = L^(88*((j:ℝ)+1)) := by
    calc
      _ = (L^(88:ℝ))^(((j+1:ℕ):ℝ)) :=
        (Real.rpow_natCast _ (j+1)).symm
      _ = L^((88:ℝ)*((j+1:ℕ):ℝ)) :=
        (Real.rpow_mul hLpos.le (88:ℝ) _).symm
      _ = _ := by push_cast; ring
  change ‖iteratedDeriv j (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x‖ ≤
    parityOriginalHistoricalDyadicEtaFixedDerivativeK434 j *
      L^(88*((j:ℝ)+1))
  calc
    _ ≤ 2*(L^(88:ℝ))^(j+1)*
      ((SchwartzMap.seminorm ℝ 0 j)
          parityOriginalFixedRatioDyadicReferenceSchwartz434) := hPoint
    _ = parityOriginalHistoricalDyadicEtaFixedDerivativeK434 j *
      L^(88*((j:ℝ)+1)) := by
        rw [←hp]
        unfold parityOriginalHistoricalDyadicEtaFixedDerivativeK434
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEta3DComposition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- True finite-source all-order derivative envelope of the
constructed eta_e,L smoothing profile at order j. Every K_i comes
from one native smooth compact reference bump, independent of L,k,Z. -/
def parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434
    (L : ℝ) (j : ℕ) : ℝ :=
  ∑i∈Finset.range (j+1),
    2*(L^(88:ℝ))^(i+1) *
      ((SchwartzMap.seminorm ℝ 0 i)
        parityOriginalFixedRatioDyadicReferenceSchwartz434)

/-- Nonnegative finite source derivative envelope. -/
theorem parity_original_historical_dyadic_eta_L_derivative_envelope_nonneg434
    (L : ℝ) (hL : 8 ≤ L) (j : ℕ) :
    0≤parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j := by
  unfold parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434
  apply Finset.sum_nonneg
  intro i hi
  have hLp : 0 < L := by linarith
  have hExp : 0 ≤ L^(88:ℝ) := (Real.rpow_pos_of_pos hLp _).le
  exact mul_nonneg
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (pow_nonneg hExp _))
    (apply_nonneg _ _)

/-- Every 0<=i<=j derivative of the original complex eta_e,L
is pointwise bounded by one finite explicit reference C_j(L).
This uses actual real-to-complex Fréchet derivative equality. -/
theorem parity_original_historical_dyadic_eta_L_all_fderivatives_envelope434
    (L : ℝ) (hL : 8≤L) (j i : ℕ) (hi : i≤j) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x‖ ≤
      parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j := by
  have hPoint := parity_original_historical_dyadic_complex_eta_e_all_derivatives_polylog434
    L hL i x
  have hF : ‖iteratedFDeriv ℝ i
      (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x‖ =
      ‖iteratedDeriv i (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) x‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  rw [hF]
  calc
    _ ≤ 2*(L^(88:ℝ))^(i+1)*
      ((SchwartzMap.seminorm ℝ 0 i)
        parityOriginalFixedRatioDyadicReferenceSchwartz434) := hPoint
    _ ≤ parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j := by
      unfold parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434
      have hiMem : i∈Finset.range (j+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
      apply Finset.single_le_sum ?_ hiMem
      intro r hr
      exact mul_nonneg (by positivity) (apply_nonneg _ _)

/-- Quantitative REAL 3D Faà di Bruno for the original Parity(4.14)
eta_e smoothing. For any smooth 3D source real argument g with
first through j-th derivatives bounded by D^i at t, the actual
complex moving eta_e,L composition satisfies
 ||D^j(eta_e,L∘g)(t)|| ≤ j! * C_j(L) * D^j.
The concrete nonlinear source g_e exponential derivative budget
and final uniform 3D Schwartz moment are still OPEN. -/
theorem parity_original_historical_dyadic_eta_3d_composition_fderivative_le434
    (L : ℝ) (hL : 8≤L) (j : ℕ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ContDiff ℝ ∞ g)
    (t : EuclideanSpace ℝ (Fin 3)) (D : ℝ)
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i g t‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ j
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘ g) t‖ ≤
      (j.factorial:ℝ) *
      parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j * D^j := by
  have hOuter := parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL
  exact norm_iteratedFDeriv_comp_le hOuter hg (by simp) t
    (fun i hi => parity_original_historical_dyadic_eta_L_all_fderivatives_envelope434
      L hL j i hi (g t)) hD
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicEtaAmplitude -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Actual source moving η_e(a) built from finitely many native
fixed-ratio dyadic bumps has VALUE at most #active centres+1.
Every summand is nonnegative and ≤1; the pointwise estimate does
NOT claim that its Fourier transform has a fixed total variation. -/
theorem parity_original_historical_dyadic_eta_e_pointwise_card_bound434
    (a : ℝ) (ha : 0<a) (x : ℝ) :
    parityOriginalHistoricalDyadicEtaEReal434 a ha x ≤
      ((parityOriginalHistoricalDyadicECentres434 a).card:ℝ)+1 := by
  let S := parityOriginalHistoricalDyadicECentres434 a
  have hSum :
    (∑ i∈S,(parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i) x:ℝ)) ≤
    ∑_i∈S,(1:ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact (parityOriginalHistoricalFixedRatioDyadicBump434
      (parityOriginalHistoricalDyadicEScale434 a i)
      (parity_original_historical_dyadic_e_scale_pos434 a ha i)).le_one
  change (∑i∈S,(parityOriginalHistoricalFixedRatioDyadicBump434
    (parityOriginalHistoricalDyadicEScale434 a i)
    (parity_original_historical_dyadic_e_scale_pos434 a ha i) x:ℝ)) +
    (parityOriginalFixedRatioDyadicReference434 x:ℝ) ≤ (S.card:ℝ)+1
  calc
    _ ≤ (∑_i∈S,(1:ℝ)) + (1:ℝ) :=
      add_le_add hSum parityOriginalFixedRatioDyadicReference434.le_one
    _ = (S.card:ℝ)+1 := by simp

/-- L-polynomial bound for the VALUE of the actual alternative
source η_e at every x, not merely its j-th derivative. The
worst-case number of active e-scale profiles is paid explicitly:
0 ≤ η_e,L(x) ≤ 2 L^88, L≥8, uniformly over ALL e/E values. -/
theorem parity_original_historical_dyadic_eta_e_value_polylog434
    (L : ℝ) (hL : 8≤L) (x : ℝ) :
    0≤parityOriginalHistoricalDyadicEtaEAtLReal434 L hL x ∧
    parityOriginalHistoricalDyadicEtaEAtLReal434 L hL x ≤ 2*L^(88:ℝ) := by
  let a := L^(-88:ℝ)
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hCard := parity_original_historical_dyadic_e_centres_card434 a
  have hBound := parity_original_historical_dyadic_eta_e_pointwise_card_bound434 a ha.1 x
  have hCount := parity_original_historical_dyadic_eta_e_level_budget434 L hL
  have hPow := parity_original_historical_dyadic_e_power88_ge_four434 L hL
  have hCardR : ((parityOriginalHistoricalDyadicECentres434 a).card:ℝ)+1 ≤
    (((⌈1/a⌉₊:ℕ):ℝ)+3) := by
    have hNat : (parityOriginalHistoricalDyadicECentres434 a).card+1 ≤
      ⌈1/a⌉₊+3 := by omega
    exact_mod_cast hNat
  change 0≤parityOriginalHistoricalDyadicEtaEReal434 a ha.1 x ∧
    parityOriginalHistoricalDyadicEtaEReal434 a ha.1 x ≤ 2*L^(88:ℝ)
  refine ⟨parity_original_historical_dyadic_eta_e_nonneg434 a ha.1 x,?_⟩
  calc
    _ ≤ ((parityOriginalHistoricalDyadicECentres434 a).card:ℝ)+1 := hBound
    _ ≤ (((⌈1/a⌉₊:ℕ):ℝ)+3) := hCardR
    _ ≤ L^(88:ℝ)+4 := hCount
    _ ≤ 2*L^(88:ℝ) := by linarith

/-- In the positive-source original Parity(4.10) weighted square,
the TRUE constructed η_e,L η_n support weight is nonnegative
and bounded pointwise by 2 L^88. This is the quantitative
positive-majorant cost, not a statement about signed offdiagonal
complex cancellation. -/
theorem parity_original_historical_dyadic_eta_weight_polylog434
    (L E V : ℝ) (hL : 8≤L) (e n : ℕ) :
    0≤parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n ∧
    parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n ≤ 2*L^(88:ℝ) := by
  have he := parity_original_historical_dyadic_eta_e_value_polylog434
    L hL ((e:ℝ)/E)
  have hn := parity_original_historical_actual_eta_n_nonneg_le_one434 ((n:ℝ)/V)
  unfold parityOriginalHistoricalDyadicEtaWeight434
  refine ⟨mul_nonneg he.1 hn.1,?_⟩
  calc
    _ ≤ parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E) * 1 :=
      mul_le_mul_of_nonneg_left hn.2 he.1
    _ = parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E) := by ring
    _ ≤ 2*L^(88:ℝ) := he.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicPositiveBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ACTUAL original Parity (4.10) source η_e(e/E)η_n(n/V)-weighted
POSITIVE physical Cauchy square costs at most 2L^88 times its
original unweighted positive square. This inequality is valid on
all selected e/n source carriers, with no assumed fine alpha bound.
It is NOT a bound on the separately complex signed offdiagonal
summation (such monotonicity would be false). -/
theorem parity_original_historical_dyadic_eta_positive_square_le434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalWeightedActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) ≤
    (2*L^(88:ℝ))*parityOriginalHistoricalActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hL
  let F : ℕ → ℕ → ℝ := fun e n =>
    ‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2
  have hS : (∑e∈Q,∑n∈J,w e n*F e n) ≤
      ∑e∈Q,∑n∈J,(2*L^(88:ℝ))*F e n := by
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right
      (parity_original_historical_dyadic_eta_weight_polylog434 L E V hL e n).2
      (sq_nonneg _)
  unfold parityOriginalHistoricalWeightedActiveCauchySquare434
    parityOriginalHistoricalActiveCauchySquare434
  change (∑e∈Q,∑n∈J,w e n*F e n) ≤
    (2*L^(88:ℝ))*(∑e∈Q,∑n∈J,F e n)
  calc
    _ ≤ ∑e∈Q,∑n∈J,(2*L^(88:ℝ))*F e n := hS
    _ = (2*L^(88:ℝ))*(∑e∈Q,∑n∈J,F e n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]

/-- The POSITIVE m=m' diagonal of the ORIGINAL h=-2 Cauchy
signed parity source with actual nonnegative moving dyadic e-weight
costs at most 2 L^88 times the unweighted physical diagonal. The
true signed offdiagonal is kept intact and needs Parity (4.17); no
invalid majorization of that complex term follows from this lemma. -/
theorem parity_original_historical_dyadic_eta_positive_diagonal_le434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalWeightedActiveDiagonal434
      d L E band slot δ ξ rho K J α signed Y
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) ≤
    (2*L^(88:ℝ))*parityOriginalHistoricalActiveCauchyDiagonal434
      d L E band slot δ ξ rho K J α signed Y := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hL
  let F : ℕ → ℕ → ℝ := fun e n =>
    ∑m∈K,‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2
  have hFpos : ∀e n, 0≤F e n := by
    intro e n
    apply Finset.sum_nonneg
    intro m hm
    exact sq_nonneg _
  have hS : (∑e∈Q,∑n∈J,w e n*F e n) ≤
      ∑e∈Q,∑n∈J,(2*L^(88:ℝ))*F e n := by
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right
      (parity_original_historical_dyadic_eta_weight_polylog434 L E V hL e n).2
      (hFpos e n)
  unfold parityOriginalHistoricalWeightedActiveDiagonal434
    parityOriginalHistoricalActiveCauchyDiagonal434
  change (∑e∈Q,∑n∈J,w e n*F e n) ≤
    (2*L^(88:ℝ))*(∑e∈Q,∑n∈J,F e n)
  calc
    _ ≤ ∑e∈Q,∑n∈J,(2*L^(88:ℝ))*F e n := hS
    _ = (2*L^(88:ℝ))*(∑e∈Q,∑n∈J,F e n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicDiagonalPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Source Parity (4.11) TRUE historical Cauchy diagonal after putting
in the full quantitatively regular moving L^-88 eta_e majorant and
fixed eta_n. The complete diagonal is controlled with fixed exponent
2*C_W1+256+88 (up to explicit factor 2), independent of K0 and
Fourier precision. Uses only the original positive divisor-moment
diagonal, NOT any false monotonicity of signed offdiagonal complex
terms. All source physical h=-2, Q/P and original H0 are retained. -/
theorem parity_eventually_original_historical_dyadic_weighted_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256 ≤ L ∧ 8 ≤ L ∧
      ∀ (hLw : 8 ≤ L) (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ), 0 ≤ Acoef →
        (∀m∈K, ‖α m‖≤Acoef) →
      parityOriginalHistoricalWeightedActiveDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed ⌊2*Real.exp L⌋₊
        (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) ≤
        2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) := by
  filter_upwards [parity_eventually_original_historical_active_diagonal_polylog434,
    eventually_ge_atTop (8:ℝ)] with L hDiag hL
  refine ⟨hDiag.1,hL,?_⟩
  intro hLw band slot δ ξ E V rho K J α signed Acoef hA hα
  let c : ℝ := 2*L^(88:ℝ)
  have hLp : 0<L := by linarith
  have hC : 0≤ c := by dsimp [c]; positivity
  have hW := parity_original_historical_dyadic_eta_positive_diagonal_le434
    (sourceOriginalLiteralDepth 20 L) L E V hLw band slot δ ξ rho
    K J α signed ⌊2*Real.exp L⌋₊
  have hD := hDiag.2 band slot δ ξ E rho K J α signed Acoef hA hα
  have hMul := mul_le_mul_of_nonneg_left hD hC
  have hPower : L^(88:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256) =
    L^(2*parityOriginalW1PolylogExponent434+344) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ c*parityOriginalHistoricalActiveCauchyDiagonal434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J α signed ⌊2*Real.exp L⌋₊ := hW
    _ ≤ c*(Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256)) := hMul
    _ = 2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) := by
      dsimp [c]
      rw [←hPower]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDyadicCauchyDiagonalJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Original Parity (4.10)--(4.11), with the REAL built dyadic
eta_e and fixed original eta_n, and the ORIGINAL smooth-weighted
signed complex character/Z offdiagonal, in ONE native statement.
The full historical b629 fine alpha Q/P physical H0 and source
signed epsilon are unchanged. The moving eta_e is C-infinity and
has previously proved L^(88(j+1)) derivative budget. The
weighted diagonal is bounded by 2*Acoef^2*x*L^(2*C_W1+344),
not a hypothesized unweighted signed offdiagonal saving.
This still does not prove original full Parity (4.17)/(4.2). -/
theorem parity_eventually_original_historical_dyadic_Cauchy_diag_character_join434
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
        (U V E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ) (β : ℕ → ℂ)
        (Acoef : ℝ),
      0<U → 0<V → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      0≤Acoef →
      (∀m∈K,‖(restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)) m‖≤Acoef) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      let Ns := parityOriginalHistoricalWeightedActiveCauchySquare434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let D := parityOriginalHistoricalWeightedActiveDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let OD := parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      (‖parityOriginalHistoricalCauchyAtDelta434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
        (∑e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ,
          ∑n∈J,‖parityOriginalHistoricalWindowAE434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2)*Ns)
      ∧ (((Ns:ℝ):ℂ)=((D:ℝ):ℂ)+OD)
      ∧ (D ≤ 2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344)) := by
  filter_upwards [parity_eventually_original_dyadic_eta_alllog_weighted_cauchy_to_character_Z434
      S beta gamma K0 hS hbeta hgamma,
    parity_eventually_original_historical_dyadic_weighted_diagonal_polylog434]
    with L hSource hD
  refine ⟨hD.1, hSource.1, ?_⟩
  intro hLw band slot δ ξ U V E rho K J prime signed lFine uFine β Acoef
    hU hV hScale hDyad hNrange hl hFineLow hA hAlpha
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  have hSrc := hSource.2 hLw band slot δ ξ U V E rho K J prime signed
    lFine uFine β hU hV hScale hDyad hNrange hl hFineLow
  have hDiag := hD.2.2 hLw band slot δ ξ E V rho K J alpha signed Acoef hA hAlpha
  exact ⟨hSrc.1,hSrc.2,hDiag⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaNFixedBudget -/

section

open Filter Topology Real MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ACTUAL original historical eta_n(n/V), constructed from a
fixed C∞ bump on [1,2] supported in (1/2,3), has compact support
without postulating a different n cutoff or a hidden L-dependent
source regularity coefficient. -/
theorem parity_original_historical_actual_eta_n_compact434 :
    HasCompactSupport parityOriginalHistoricalActualEtaN434 := by
  have hsub : Function.support parityOriginalHistoricalActualEtaN434 ⊆
      Set.Icc (0:ℝ) (4:ℝ) := by
    intro x hx
    have hpos := parity_original_historical_actual_eta_n_support434 x hx
    exact ⟨by linarith,by linarith⟩
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal hsub isClosed_Icc

/-- Genuine exact source eta_n as a native COMPLEX Schwartz function.
The function is the SAME eta_n present in the original weighted
Cauchy square and actual Parity (4.14) 3D Fourier pullback. -/
def parityOriginalHistoricalActualEtaNSchwartz434 : 𝓢(ℝ,ℂ) :=
  parity_original_historical_actual_eta_n_compact434.toSchwartzMap
    parity_original_historical_actual_eta_n_smooth434

theorem parity_original_historical_actual_eta_n_schwartz_apply434
    (x : ℝ) :
    parityOriginalHistoricalActualEtaNSchwartz434 x =
      parityOriginalHistoricalActualEtaN434 x := rfl

/-- Fixed source n cutoff derivative constants chosen before L,
physical k/Z, ell1 character and requested Fourier precision. -/
def parityOriginalHistoricalEtaNFixedDerivativeK434 (j : ℕ) : ℝ :=
  (SchwartzMap.seminorm ℂ 0 j) parityOriginalHistoricalActualEtaNSchwartz434

theorem parity_original_historical_eta_n_fixed_K_nonneg434 (j : ℕ) :
    0≤parityOriginalHistoricalEtaNFixedDerivativeK434 j := by
  unfold parityOriginalHistoricalEtaNFixedDerivativeK434
  exact apply_nonneg _ _

/-- The genuine source eta_n has C=0 ALL-ORDER native
`sourceLogDerivativeBudget` with explicit fixed Schwartz constants,
independent of every source L,k,Z and Fourier-tail order. Together
with the proved C=88 η_e budget this closes both one-dimensional
regularity inputs of Parity (4.14), leaving only 3D Faà di Bruno
composition and the terminal (4.17) application. -/
theorem parity_original_historical_actual_eta_n_source_derivative_budget434
    (L : ℝ) :
    sourceLogDerivativeBudget 0
      parityOriginalHistoricalEtaNFixedDerivativeK434
      L parityOriginalHistoricalActualEtaN434 := by
  intro j x
  have h := SchwartzMap.le_seminorm' ℂ 0 j
    parityOriginalHistoricalActualEtaNSchwartz434 x
  change ‖iteratedDeriv j parityOriginalHistoricalActualEtaN434 x‖ ≤
    parityOriginalHistoricalEtaNFixedDerivativeK434 j * L^(0*((j:ℝ)+1))
  simp only [zero_mul,Real.rpow_zero,mul_one,
    parityOriginalHistoricalEtaNFixedDerivativeK434]
  have hFun : parityOriginalHistoricalActualEtaN434 =
      (parityOriginalHistoricalActualEtaNSchwartz434 : ℝ→ℂ) := by
    funext y
    exact (parity_original_historical_actual_eta_n_schwartz_apply434 y).symm
  rw [hFun]
  simpa only [pow_zero,one_mul] using h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEta3DPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The j-dependent but L-independent one-dimensional SOURCE
reference budget required by the exact 3D Faà di Bruno inequality. -/
def parityOriginalEtaEDerivativeFixedEnvelope434 (j : ℕ) : ℝ :=
  ∑i∈Finset.range (j+1), 2 *
    ((SchwartzMap.seminorm ℝ 0 i)
      parityOriginalFixedRatioDyadicReferenceSchwartz434)

/-- The actual ORIGINAL moving η_e,L Fréchet derivative envelope,
previously a finite L-dependent sum, is bounded by ONE fixed
reference constant times L^(88(j+1)), for EVERY order j and L≥8. -/
theorem parity_original_historical_dyadic_eta_L_derivative_envelope_polylog434
    (L : ℝ) (hL : 8≤L) (j : ℕ) :
    parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j ≤
      parityOriginalEtaEDerivativeFixedEnvelope434 j *
        (L^(88:ℝ))^(j+1) := by
  have hLp : 0 < L := by linarith
  have hL1 : (1:ℝ) ≤ L^(88:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  unfold parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434
    parityOriginalEtaEDerivativeFixedEnvelope434
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hii : i+1≤j+1 := Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hp : (L^(88:ℝ))^(i+1)≤(L^(88:ℝ))^(j+1) :=
    pow_le_pow_right₀ hL1 hii
  have hK : 0≤(SchwartzMap.seminorm ℝ 0 i)
      parityOriginalFixedRatioDyadicReferenceSchwartz434 := apply_nonneg _ _
  calc
    2*(L^(88:ℝ))^(i+1)*((SchwartzMap.seminorm ℝ 0 i)
      parityOriginalFixedRatioDyadicReferenceSchwartz434) ≤
      2*(L^(88:ℝ))^(j+1)*((SchwartzMap.seminorm ℝ 0 i)
      parityOriginalFixedRatioDyadicReferenceSchwartz434) := by
        gcongr
    _ = (2*((SchwartzMap.seminorm ℝ 0 i)
      parityOriginalFixedRatioDyadicReferenceSchwartz434)) *
      (L^(88:ℝ))^(j+1) := by ring

/-- The ORIGINAL η_e source composition with any real 3D log
argument g whose first j derivatives cost (L^C)^i has an explicit
UNIFORM polynomial L^( (88+C)(j+1)) bound. This is unconditional
in η_e and in the outer 3D chain rule, and conditional only on the
true particular inner argument derivative bound. -/
theorem parity_original_historical_dyadic_eta_e_3d_composition_polylog434
    (L : ℝ) (hL : 8≤L) (j : ℕ) (C : ℝ) (hC : 0≤C)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : ContDiff ℝ ∞ g)
    (t : EuclideanSpace ℝ (Fin 3))
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i g t‖ ≤ (L ^ C) ^ i) :
    ‖iteratedFDeriv ℝ j
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘ g) t‖ ≤
    (j.factorial:ℝ) * parityOriginalEtaEDerivativeFixedEnvelope434 j *
      L^((88+C)*((j:ℝ)+1)) := by
  have hLp : 0<L := by linarith
  have hL1 : (1:ℝ)≤L := by linarith
  have hK : 0≤parityOriginalEtaEDerivativeFixedEnvelope434 j := by
    unfold parityOriginalEtaEDerivativeFixedEnvelope434
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by norm_num) (apply_nonneg _ _)
  have houter := parity_original_historical_dyadic_eta_3d_composition_fderivative_le434
    L hL j g hg t (L^C) hD
  have hE := parity_original_historical_dyadic_eta_L_derivative_envelope_polylog434 L hL j
  have hTpow : (L^(88:ℝ))^(j+1)*(L^C)^j ≤ L^((88+C)*((j:ℝ)+1)) := by
    have hp1 : (L^(88:ℝ))^(j+1)=L^(88*((j:ℝ)+1)) := by
      rw [←Real.rpow_natCast (L^(88:ℝ)) (j+1)]
      rw [←Real.rpow_mul hLp.le]
      push_cast
      ring
    have hp2 : (L^C)^j=L^(C*(j:ℝ)) := by
      rw [←Real.rpow_natCast (L^C) j]
      rw [←Real.rpow_mul hLp.le]
    rw [hp1,hp2,←Real.rpow_add hLp]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)*parityOriginalHistoricalDyadicEtaLDerivativeEnvelope434 L j * (L^C)^j := houter
    _ ≤ (j.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 j *
      (L^(88:ℝ))^(j+1)*(L^C)^j := by
        have hm := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg j.factorial)
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hm (pow_nonneg (Real.rpow_nonneg hLp.le _) _))
    _ ≤ (j.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 j *
        L^((88+C)*((j:ℝ)+1)) := by
        have hCoef : 0≤(j.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 j := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hTpow hCoef]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaN3DPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- TRUE native source η_n fixed real 3D outer cutoff envelope,
consisting of finitely many derivatives of the ACTUAL original
fixed [1,2]-plateau complex Schwartz bump. No L-dependent constants. -/
def parityOriginalEtaNDerivativeFixedEnvelope434 (j : ℕ) : ℝ :=
  ∑i∈Finset.range (j+1),
    (SchwartzMap.seminorm ℂ 0 i) parityOriginalHistoricalActualEtaNSchwartz434

/-- Every order i≤j of actual original eta_n has FDeriv operator
norm bounded by one fixed explicit finite sum independent of L,k,Z. -/
theorem parity_original_historical_eta_n_all_fderivatives_fixed_envelope434
    (j i : ℕ) (hi : i≤j) (x : ℝ) :
    ‖iteratedFDeriv ℝ i parityOriginalHistoricalActualEtaN434 x‖ ≤
      parityOriginalEtaNDerivativeFixedEnvelope434 j := by
  have hfun : parityOriginalHistoricalActualEtaN434 =
      (parityOriginalHistoricalActualEtaNSchwartz434 : ℝ→ℂ) := by
    funext y
    exact (parity_original_historical_actual_eta_n_schwartz_apply434 y).symm
  rw [hfun,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  calc
    _ ≤ (SchwartzMap.seminorm ℂ 0 i) parityOriginalHistoricalActualEtaNSchwartz434 := by
      have hh := SchwartzMap.le_seminorm' ℂ 0 i parityOriginalHistoricalActualEtaNSchwartz434 x
      simpa only [pow_zero,one_mul] using hh
    _ ≤ parityOriginalEtaNDerivativeFixedEnvelope434 j := by
      unfold parityOriginalEtaNDerivativeFixedEnvelope434
      apply Finset.single_le_sum ?_ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      intro r hr
      exact apply_nonneg _ _

/-- SOURCE actual 3D eta_n composition: arbitrary-order native
Faà di Bruno with fixed constant K^n_j independent of L and
one inner real three-dimensional function g_n. Its derivative
complexity is precisely j!*K^n_j*D^j. -/
theorem parity_original_historical_eta_n_3d_composition_fderivative_le434
    (j : ℕ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ContDiff ℝ ∞ g) (t : EuclideanSpace ℝ (Fin 3)) (D : ℝ)
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i g t‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ j (parityOriginalHistoricalActualEtaN434 ∘ g) t‖ ≤
      (j.factorial:ℝ) * parityOriginalEtaNDerivativeFixedEnvelope434 j * D^j := by
  exact norm_iteratedFDeriv_comp_le
    parity_original_historical_actual_eta_n_smooth434 hg (by simp) t
    (fun i hi => parity_original_historical_eta_n_all_fderivatives_fixed_envelope434 j i hi (g t)) hD

/-- True original fixed η_n three-dimensional composition has
explicit L^C(j+1) bound whenever the real physical source
logarithmic argument has derivative size (L^C)^i, for C≥0,L≥8.
The analytic cost C=0 of η_n itself is PROVED, not assumed. -/
theorem parity_original_historical_eta_n_3d_composition_polylog434
    (L : ℝ) (hL : 8≤L) (j : ℕ) (C : ℝ) (hC : 0≤C)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : ContDiff ℝ ∞ g)
    (t : EuclideanSpace ℝ (Fin 3))
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i g t‖ ≤ (L^C)^i) :
    ‖iteratedFDeriv ℝ j (parityOriginalHistoricalActualEtaN434 ∘ g) t‖ ≤
      (j.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 j *
      L^(C*((j:ℝ)+1)) := by
  have hLp : 0<L := by linarith
  have hL1 : (1:ℝ)≤L := by linarith
  have hK : 0≤parityOriginalEtaNDerivativeFixedEnvelope434 j := by
    unfold parityOriginalEtaNDerivativeFixedEnvelope434
    exact Finset.sum_nonneg (fun i hi => apply_nonneg _ _)
  have hOuter := parity_original_historical_eta_n_3d_composition_fderivative_le434
    j g hg t (L^C) hD
  have hPow : (L^C)^j ≤ L^(C*((j:ℝ)+1)) := by
    have hp : (L^C)^j = L^(C*(j:ℝ)) := by
      rw [←Real.rpow_natCast (L^C) j,←Real.rpow_mul hLp.le]
    rw [hp]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have hj : (0:ℝ)≤C := hC
    nlinarith
  calc
    _ ≤ (j.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 j * (L^C)^j := hOuter
    _ ≤ (j.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 j *
      L^(C*((j:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hPow (mul_nonneg (Nat.cast_nonneg _) hK)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalExpCoordinate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- A genuine Euclidean R^3 coordinate functional is a REAL
continuous linear map with operator norm at most one. No sup-norm
substitution is made in the original Fourier Schwartz space. -/
theorem parity_original_euclidean_coord_linear_norm_le_one434
    (i : Fin 3) : ‖(EuclideanSpace.proj i :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro t
  have h := PiLp.norm_apply_le t i
  change ‖t i‖ ≤ 1*‖t‖
  simpa only [one_mul] using h

/-- ALL positive-order Fréchet derivatives of a genuine linear
coordinate projection have operator norm ≤1: the first derivative
is the original coordinate functional, every higher one is zero. -/
theorem parity_original_euclidean_linear_coord_derivatives_le_one434
    (i : Fin 3) (j : ℕ) (hj : 1≤j)
    (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) => x i) t‖ ≤ 1 := by
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj i
  have hP : ‖P‖≤1 := parity_original_euclidean_coord_linear_norm_le_one434 i
  have hFun : (fun x : EuclideanSpace ℝ (Fin 3) => x i)=(P : _ → ℝ) := by
    funext x
    rfl
  rw [hFun]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [←norm_iteratedFDeriv_fderiv]
  have hD : (fderiv ℝ (P : EuclideanSpace ℝ (Fin 3) → ℝ)) = fun _ => P := by
    funext x
    exact P.fderiv
  rw [hD]
  cases n with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero] using hP
  | succ n =>
    simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
    norm_num

/-- REAL exponential has exact all-order Fréchet derivative norm
exp(s) at the same argument s, including derivative order zero. -/
theorem parity_original_real_exp_all_fderiv_norm434 (j : ℕ) (s : ℝ) :
    ‖iteratedFDeriv ℝ j Real.exp s‖=Real.exp s := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul j (1:ℝ)) s
  have heq : iteratedDeriv j Real.exp s=Real.exp s := by
    simpa only [one_mul,one_pow] using h
  rw [heq,Real.norm_eq_abs,abs_of_pos (Real.exp_pos s)]

/-- The TRUE real Euclidean source function exp(t_i) has order-j
three-dimensional derivative norm ≤ j! exp(t_i), uniformly for
all real t and every i=0,1,2. This is a quantitative native
Faà di Bruno source bound with exact coordinate derivative norms. -/
theorem parity_original_real_3d_exp_coordinate_fderiv_le434
    (i : Fin 3) (j : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j
        (fun x : EuclideanSpace ℝ (Fin 3) => Real.exp (x i)) t‖ ≤
      (j.factorial:ℝ)*Real.exp (t i) := by
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => x i
  have hf : ContDiff ℝ ∞ f := contDiff_apply ℝ ℝ i |>.comp
    (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  have hc : ∀ (r : ℕ), r≤j →
      ‖iteratedFDeriv ℝ r Real.exp (f t)‖≤Real.exp (t i) := by
    intro r hr
    exact le_of_eq (parity_original_real_exp_all_fderiv_norm434 r (f t))
  have hd : ∀ (r : ℕ), 1≤ r → r≤j →
      ‖iteratedFDeriv ℝ r f t‖≤(1:ℝ)^r := by
    intro r h1 hr
    simpa only [one_pow] using
      (parity_original_euclidean_linear_coord_derivatives_le_one434 i r h1 t)
  have hh := norm_iteratedFDeriv_comp_le Real.contDiff_exp hf (by simp) t hc hd
  simpa only [Function.comp_def,pow_one,one_pow,mul_one] using hh


/-- The exponential of ANY real continuous linear functional of
Euclidean 3-space with operator norm ≤1 has j-th Fréchet derivative
bounded by j!*exp(P t). This treats both +t_i and -t_i source
exponents in the physical Parity (4.14) pullback with the SAME lemma. -/
theorem parity_original_real_3d_exp_linear_fderiv_le434
    (P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hP : ‖P‖≤1) (j : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) => Real.exp (P x)) t‖ ≤
      (j.factorial:ℝ)*Real.exp (P t) := by
  have hDer (r : ℕ) (hr : 1≤ r) :
      ‖iteratedFDeriv ℝ r (P : EuclideanSpace ℝ (Fin 3) → ℝ) t‖ ≤ 1 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [←norm_iteratedFDeriv_fderiv]
    have hG : (fderiv ℝ (P : EuclideanSpace ℝ (Fin 3) → ℝ)) = fun _ => P := by
      funext x
      exact P.fderiv
    rw [hG]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hP
    | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num
  have hc : ∀ (r : ℕ), r≤j →
      ‖iteratedFDeriv ℝ r Real.exp (P t)‖ ≤ Real.exp (P t) := by
    intro r hr
    exact le_of_eq (parity_original_real_exp_all_fderiv_norm434 r (P t))
  have hd : ∀ (r : ℕ), 1≤ r → r≤j →
      ‖iteratedFDeriv ℝ r (P : EuclideanSpace ℝ (Fin 3) → ℝ) t‖ ≤ (1:ℝ)^r := by
    intro r hr1 hr2
    simpa only [one_pow] using hDer r hr1
  have h := norm_iteratedFDeriv_comp_le
    (Real.contDiff_exp : ContDiff ℝ ∞ Real.exp)
    (P.contDiff : ContDiff ℝ ∞ (P : EuclideanSpace ℝ (Fin 3) → ℝ))
    (by simp : (j : ℕ∞ω) ≤ ∞) t hc hd
  simpa only [Function.comp_def,one_pow,mul_one] using h

/-- The original source negative log-coordinate exponential
exp(-t_i), with exact native Euclidean 3D derivatives. -/
theorem parity_original_real_3d_exp_negative_coordinate_fderiv_le434
    (i : Fin 3) (j : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j
      (fun x : EuclideanSpace ℝ (Fin 3) => Real.exp (-(x i))) t‖ ≤
      (j.factorial:ℝ)*Real.exp (-(t i)) := by
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := -(EuclideanSpace.proj i)
  have hP : ‖P‖ ≤ 1 := by
    simpa only [P,norm_neg] using
      (parity_original_euclidean_coord_linear_norm_le_one434 i)
  exact parity_original_real_3d_exp_linear_fderiv_le434 P hP j t

/-- On a real ORIGINAL fixed logarithmic box [-log A,log A],
both exp(±t_i) have pointwise values ≤A, with no dependence
on original L,k,Z or on the chosen Fourier accuracy. -/
theorem parity_original_real_3d_coordinate_exp_fixed_box434
    (A : ℝ) (hA : 0<A) (i : Fin 3)
    (t : EuclideanSpace ℝ (Fin 3))
    (ht : -(Real.log A)≤t i ∧ t i≤Real.log A) :
    Real.exp (t i)≤A ∧ Real.exp (-(t i))≤A := by
  constructor
  · calc
      Real.exp (t i) ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr ht.2
      _ = A := Real.exp_log hA
  · calc
      Real.exp (-(t i)) ≤ Real.exp (Real.log A) := by
        apply Real.exp_le_exp.mpr
        linarith [ht.1]
      _ = A := Real.exp_log hA
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaELogArgFDeriv -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The true original source Parity (4.14) η_e argument
 a*(exp(t₂)-exp(t₁)), with a=U/(kE), has order-j Euclidean
3D derivative bounded by 2|a| j! A on the genuine fixed
logarithmic buffer box exp(ti)≤A. Both signs of nonzero k
are retained; no positive-a assumption or artificial theta. -/
theorem parity_original_historical_eta_e_real_3d_fderiv_log_box434
    (A : ℝ) (hA : 0<A) (a : ℝ) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A) :
    ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) =>
      a*(Real.exp (x 1)-Real.exp (x 0))) t‖ ≤
    2*|a| *(j.factorial:ℝ)*A := by
  let f1 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Real.exp (x 1)
  let f0 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Real.exp (x 0)
  have hs1 : ContDiff ℝ ∞ f1 := by
    dsimp [f1]
    fun_prop
  have hs0 : ContDiff ℝ ∞ f0 := by
    dsimp [f0]
    fun_prop
  have hExp1 := parity_original_real_3d_exp_coordinate_fderiv_le434 1 j t
  have hExp0 := parity_original_real_3d_exp_coordinate_fderiv_le434 0 j t
  have hb1 := (parity_original_real_3d_coordinate_exp_fixed_box434 A hA 1 t h1).1
  have hb0 := (parity_original_real_3d_coordinate_exp_fixed_box434 A hA 0 t h0).1
  have hn1 : ‖iteratedFDeriv ℝ j f1 t‖≤(j.factorial:ℝ)*A :=
    hExp1.trans (mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _))
  have hn0 : ‖iteratedFDeriv ℝ j f0 t‖≤(j.factorial:ℝ)*A :=
    hExp0.trans (mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg _))
  have hsub : ‖iteratedFDeriv ℝ j (fun x => f1 x-f0 x) t‖ ≤
      2*(j.factorial:ℝ)*A := by
    change ‖iteratedFDeriv ℝ j (f1-f0) t‖ ≤ 2*(j.factorial:ℝ)*A
    rw [iteratedFDeriv_sub_apply
      (hs1.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))
      (hs0.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f1 t‖+‖iteratedFDeriv ℝ j f0 t‖ := norm_sub_le _ _
      _ ≤ (j.factorial:ℝ)*A+(j.factorial:ℝ)*A := add_le_add hn1 hn0
      _ = 2*(j.factorial:ℝ)*A := by ring
  have hscalar :
      iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) => a*(f1 x-f0 x)) t =
      a • iteratedFDeriv ℝ j (fun x => f1 x-f0 x) t := by
    exact (iteratedFDeriv_const_smul_apply (a:=a)
      ((hs1.sub hs0).contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞)))
  rw [hscalar]
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |a| *(2*(j.factorial:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hsub (abs_nonneg a)
    _ = 2*|a| *(j.factorial:ℝ)*A := by ring

/-- ORIGINAL literal SOURCE g_e(t)=U/(kE)*(exp t₂-exp t₁)
on the true Euclidean 3D log box; source E=U L^-K0 and k≠0
imply ∥D^j g_e∥≤2 L^K0 j! A. The bound is independent of
chosen χ, physical z and signed parity epsilon. -/
theorem parity_original_historical_eta_e_log_arg_3d_polylog434
    (L U E K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hU : 0<U) (hE : E=U*L^(-K0))
    (hk : k≠0) (hA : 0<A) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A) :
    ‖iteratedFDeriv ℝ j
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaELogArg434 U E k (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
      2*L^K0*(j.factorial:ℝ)*A := by
  have hLp : 0<L := by linarith
  have hcoeff := parity_original_historical_eta_e_parameter_polylog434
    L U E K0 k hLp hU hE hk
  have hApos : 0≤(j.factorial:ℝ)*A := mul_nonneg (Nat.cast_nonneg _) hA.le
  have hs := parity_original_historical_eta_e_real_3d_fderiv_log_box434
    A hA (U/((k:ℝ)*E)) j t h0 h1
  have hIdent : (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaELogArg434 U E k (EuclideanSpace.equiv (Fin 3) ℝ t)) =
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        (U/((k:ℝ)*E))*(Real.exp (x 1)-Real.exp (x 0))) := by
    funext x
    rfl
  rw [hIdent]
  calc
    _ ≤ 2*|U/((k:ℝ)*E)| *(j.factorial:ℝ)*A := hs
    _ ≤ 2*L^K0*(j.factorial:ℝ)*A := by
      have h := mul_le_mul_of_nonneg_right hcoeff hApos
      nlinarith [h]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaELogArgUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The ACTUAL historical original Parity (4.14) e-logarithmic
argument has all positive-order Euclidean 3D Fréchet derivatives
bounded by a SINGLE source polynomial base:

  ‖D^i [(U/(kE)) (e^t₂-e^t₁)](t)‖ ≤ (L^(K0+1))^i,
  1≤ i≤J,

on the fixed logarithmic box |t₀|,|t₁|≤log A. This follows from
source E=UL^-K0 and nonzero integer k, explicit high-order exp
bound i!A, and L≥2AJ!. The threshold depends on fixed J,A, not
on k,Z, sign or Fourier frequency. This is the real source 3D
inner-derivative gate needed by native Faà di Bruno. -/
theorem parity_original_historical_eta_e_log_arg_all_derivatives_uniform434
    (L U E K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hU : 0<U)
    (hE : E=U*L^(-K0)) (hk : k≠0)
    (hA : 0<A) (J : ℕ)
    (hLarge : 2*A*(J.factorial:ℝ)≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A) :
    ∀ (i : ℕ), 1 ≤ i → i ≤ J →
      ‖iteratedFDeriv ℝ i
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaELogArg434 U E k
            (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
      (L^(K0+1))^i := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hLpow : 0<L^K0 := Real.rpow_pos_of_pos hLp _
  have hLbase : 1≤L^(K0+1) := Real.one_le_rpow hL1 (by linarith)
  intro i hi hJ
  have hFactNat : i.factorial≤J.factorial := Nat.factorial_le hJ
  have hFact : (i.factorial:ℝ)≤(J.factorial:ℝ) := by exact_mod_cast hFactNat
  have hBound := parity_original_historical_eta_e_log_arg_3d_polylog434
    L U E K0 A k hL hU hE hk hA i t h0 h1
  have hAfac : 0≤2*L^K0*A := by positivity
  have hFactBound : 2*L^K0*(i.factorial:ℝ)*A ≤
       2*L^K0*(J.factorial:ℝ)*A := by
    nlinarith [mul_le_mul_of_nonneg_left hFact hAfac]
  have hRpowBound : 2*L^K0*(J.factorial:ℝ)*A ≤ L^(K0+1) := by
    have hmul := mul_le_mul_of_nonneg_right hLarge hLpow.le
    have hPow : L^(K0+1)=L^K0*L := by
      rw [Real.rpow_add hLp,Real.rpow_one]
    rw [hPow]
    nlinarith [hmul]
  have hDle : (L^(K0+1))≤(L^(K0+1))^i := by
    have hh := pow_le_pow_right₀ hLbase hi
    simpa only [pow_one] using hh
  exact hBound.trans (hFactBound.trans (hRpowBound.trans hDle))

/-- Original Parity (4.14) SOURCE eta_e smoothing in genuine
Euclidean R^3 has order-J derivative ≤
  J! K^e_J L^((K0+89)(J+1))
for L≥8 and L≥2A J!, E=U L^-K0, k≠0 and the actual fixed
logarithmic box. This is the FIRST COMPLETE SOURCE-SPECIFIC
three-dimensional quantitative composition bound; it uses no
hypothetical derivative of the inner exponential argument. -/
theorem parity_original_historical_actual_eta_e_3d_composed_polylog434
    (L U E K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hU : 0<U)
    (hE : E=U*L^(-K0)) (hk : k≠0)
    (hA : 0<A) (J : ℕ)
    (hLarge : 2*A*(J.factorial:ℝ)≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘
       (fun t : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaELogArg434 U E k
           (EuclideanSpace.equiv (Fin 3) ℝ t))) t‖ ≤
    (J.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 J *
      L^((K0+89)*((J:ℝ)+1)) := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun t =>
    parityOriginalHistoricalEtaELogArg434 U E k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  have hg : ContDiff ℝ ∞ g :=
    (parity_original_historical_eta_e_log_arg_smooth434 U E k).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  have hD := parity_original_historical_eta_e_log_arg_all_derivatives_uniform434
    L U E K0 A k hL hK0 hU hE hk hA J hLarge t h0 h1
  have h := parity_original_historical_dyadic_eta_e_3d_composition_polylog434
    L hL J (K0+1) (by linarith) g hg t hD
  simpa only [show (88:ℝ)+(K0+1)=K0+89 by ring] using h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalExpLinearTwo -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The exponential of a REAL Euclidean linear form of operator norm
≤D, D≥1, satisfies native order-j derivative bound
j! exp(Pt) D^j. In original Parity n-pullback the forms are
 t3-t1 and t3-t2, of norm at most 2; this uniform D=2 bound
prevents any incorrect loss from the product of two exponentials. -/
theorem parity_original_real_3d_exp_linear_fderiv_le_D434
    (P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (D : ℝ) (hD : 1≤D) (hP : ‖P‖≤D)
    (j : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) => Real.exp (P x)) t‖ ≤
      (j.factorial:ℝ)*Real.exp (P t)*D^j := by
  have hDer (r : ℕ) (hr : 1≤ r) :
      ‖iteratedFDeriv ℝ r (P : EuclideanSpace ℝ (Fin 3) → ℝ) t‖ ≤ D := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
    rw [←norm_iteratedFDeriv_fderiv]
    have hG : fderiv ℝ (P : EuclideanSpace ℝ (Fin 3) → ℝ) = fun _ => P := by
      funext x
      exact P.fderiv
    rw [hG]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hP
    | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; linarith
  have hc : ∀ (r : ℕ),r≤j →
      ‖iteratedFDeriv ℝ r Real.exp (P t)‖≤Real.exp (P t) := by
    intro r hr
    exact le_of_eq (parity_original_real_exp_all_fderiv_norm434 r (P t))
  have hd : ∀ (r : ℕ), 1≤ r → r≤j →
      ‖iteratedFDeriv ℝ r (P : EuclideanSpace ℝ (Fin 3) → ℝ) t‖≤D^r := by
    intro r hr hrj
    have hp := pow_le_pow_right₀ hD hr
    exact (hDer r hr).trans (by simpa only [pow_one] using hp)
  have h := norm_iteratedFDeriv_comp_le
    (Real.contDiff_exp : ContDiff ℝ ∞ Real.exp)
    (P.contDiff : ContDiff ℝ ∞ (P : EuclideanSpace ℝ (Fin 3) → ℝ))
    (by simp : (j : ℕ∞ω)≤∞) t hc hd
  simpa only [Function.comp_def] using h

/-- The REAL original Parity signed two-coordinate logarithmic form
t3-t1 or t3-t2 has Euclidean operator norm ≤2, and no dependence
on source L,k,Z or Fourier precision. -/
theorem parity_original_real_3d_coordinate_difference_linear_norm_le_two434
    (i j : Fin 3) :
    ‖((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) -
       EuclideanSpace.proj j)‖ ≤ 2 := by
  have hi := parity_original_euclidean_coord_linear_norm_le_one434 i
  have hj := parity_original_euclidean_coord_linear_norm_le_one434 j
  have h := norm_sub_le
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  linarith

/-- The exact native 3D second pullback exponent exp(t3-t1)
(or exp(t3-t2)) has order-j derivative norm at most
j! exp(t3-ti) 2^j; both signs in the difference are true real
linear forms, with no synthetic signed Fourier weight. -/
theorem parity_original_real_3d_exp_coordinate_difference_fderiv_le434
    (i j : Fin 3) (n : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ n
      (fun x : EuclideanSpace ℝ (Fin 3) => Real.exp (x i - x j)) t‖ ≤
      (n.factorial:ℝ)*Real.exp (t i-t j)*(2:ℝ)^n := by
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    EuclideanSpace.proj i - EuclideanSpace.proj j
  have hP : ‖P‖≤2 :=
    parity_original_real_3d_coordinate_difference_linear_norm_le_two434 i j
  exact parity_original_real_3d_exp_linear_fderiv_le_D434 P 2 (by norm_num) hP n t

/-- On the ORIGINAL fixed logarithmic box, exp(t3-ti)≤A²
for each true real i=0,1,2; each of the two factors is positive
and independently bounded by A. -/
theorem parity_original_real_3d_exp_difference_fixed_box434
    (A : ℝ) (hA : 0<A) (i j : Fin 3)
    (t : EuclideanSpace ℝ (Fin 3))
    (hi : -(Real.log A)≤t i ∧ t i≤Real.log A)
    (hj : -(Real.log A)≤t j ∧ t j≤Real.log A) :
    Real.exp (t i-t j) ≤ A^2 := by
  have h1 := (parity_original_real_3d_coordinate_exp_fixed_box434 A hA i t hi).1
  have h2 := (parity_original_real_3d_coordinate_exp_fixed_box434 A hA j t hj).2
  have hprod := mul_le_mul h1 h2 (Real.exp_pos _).le hA.le
  calc
    Real.exp (t i-t j) = Real.exp (t i)*Real.exp (-(t j)) := by
      rw [sub_eq_add_neg,Real.exp_add]
    _ ≤ A*A := hprod
    _ = A^2 := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaNLogArgFDeriv -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Actual original h=-2 Parity (4.14) η_n argument in Euclidean
log coordinates, rewritten using genuine exp(t3-ti) identities:
 (Z/(kUV))*(exp(t3-t1)-exp(t3-t2))+(2/UV)*exp(-t1).
The 2/(UV) shift correction is retained EXACTLY. -/
theorem parity_original_historical_eta_n_log_arg_exp_difference434
    (U V Z : ℝ) (k : ℤ) (t : EuclideanSpace ℝ (Fin 3)) :
    parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t) =
    (Z/((k:ℝ)*U*V)) *
      (Real.exp (t 2-t 0)-Real.exp (t 2-t 1)) +
      (2/(U*V))*Real.exp (-(t 0)) := by
  change (Z/((k:ℝ)*U*V))*Real.exp (t 2)*
      (Real.exp (-(t 0))-Real.exp (-(t 1)))+
      (2/(U*V))*Real.exp (-(t 0)) = _
  have h20 : Real.exp (t 2-t 0) = Real.exp (t 2)*Real.exp (-(t 0)) := by
    rw [sub_eq_add_neg,Real.exp_add]
  have h21 : Real.exp (t 2-t 1) = Real.exp (t 2)*Real.exp (-(t 1)) := by
    rw [sub_eq_add_neg,Real.exp_add]
  rw [h20,h21]
  ring

/-- ALL Euclidean 3D derivatives of the true log-coordinate
Parity (4.14) n-pullback, including the essential h=-2 correction.
For arbitrary signed a=Z/(kUV) and nonnegative b=2/(UV), every
order j on the fixed 3D box has exact bound
  2|a| j! A² 2^j + |b| j! A.
This bound never assumes n is independently expressible without
its original shift term. -/
theorem parity_original_historical_eta_n_real_3d_fderiv_log_box434
    (A : ℝ) (hA : 0<A) (a b : ℝ) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) =>
      a*(Real.exp (x 2-x 0)-Real.exp (x 2-x 1))+
      b*Real.exp (-(x 0))) t‖ ≤
      2*|a| *(j.factorial:ℝ)*A^2*(2:ℝ)^j+
        |b| *(j.factorial:ℝ)*A := by
  let f20 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Real.exp (x 2-x 0)
  let f21 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Real.exp (x 2-x 1)
  let f0 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Real.exp (-(x 0))
  have hs20 : ContDiff ℝ ∞ f20 := by dsimp [f20];fun_prop
  have hs21 : ContDiff ℝ ∞ f21 := by dsimp [f21];fun_prop
  have hs0 : ContDiff ℝ ∞ f0 := by dsimp [f0];fun_prop
  have hp20 := parity_original_real_3d_exp_coordinate_difference_fderiv_le434 2 0 j t
  have hp21 := parity_original_real_3d_exp_coordinate_difference_fderiv_le434 2 1 j t
  have hp0 := parity_original_real_3d_exp_negative_coordinate_fderiv_le434 0 j t
  have hb20 := parity_original_real_3d_exp_difference_fixed_box434 A hA 2 0 t h2 h0
  have hb21 := parity_original_real_3d_exp_difference_fixed_box434 A hA 2 1 t h2 h1
  have hb0 := (parity_original_real_3d_coordinate_exp_fixed_box434 A hA 0 t h0).2
  have hjp : 0≤(j.factorial:ℝ)*(2:ℝ)^j := by positivity
  have hn20 : ‖iteratedFDeriv ℝ j f20 t‖≤(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    calc
      _ ≤ (j.factorial:ℝ)*Real.exp (t 2-t 0)*(2:ℝ)^j := hp20
      _ ≤ (j.factorial:ℝ)*A^2*(2:ℝ)^j := by
        nlinarith [mul_le_mul_of_nonneg_left hb20 hjp]
  have hn21 : ‖iteratedFDeriv ℝ j f21 t‖≤(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    calc
      _ ≤ (j.factorial:ℝ)*Real.exp (t 2-t 1)*(2:ℝ)^j := hp21
      _ ≤ (j.factorial:ℝ)*A^2*(2:ℝ)^j := by
        nlinarith [mul_le_mul_of_nonneg_left hb21 hjp]
  have hn0 : ‖iteratedFDeriv ℝ j f0 t‖≤(j.factorial:ℝ)*A :=
    hp0.trans (mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg _))
  let q1 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => a*(f20 x-f21 x)
  let q2 : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => b*f0 x
  have hsub : ‖iteratedFDeriv ℝ j (fun x=>f20 x-f21 x) t‖ ≤
      2*(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    change ‖iteratedFDeriv ℝ j (f20-f21) t‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      (hs20.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))
      (hs21.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f20 t‖+‖iteratedFDeriv ℝ j f21 t‖ := norm_sub_le _ _
      _ ≤ (j.factorial:ℝ)*A^2*(2:ℝ)^j+(j.factorial:ℝ)*A^2*(2:ℝ)^j :=
        add_le_add hn20 hn21
      _ = _ := by ring
  have hs1 : ContDiff ℝ ∞ q1 := by dsimp [q1];fun_prop
  have hs2 : ContDiff ℝ ∞ q2 := by dsimp [q2];fun_prop
  have hq1 : ‖iteratedFDeriv ℝ j q1 t‖ ≤
      2*|a| *(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    have hscalar : iteratedFDeriv ℝ j q1 t =
        a • iteratedFDeriv ℝ j (fun x=>f20 x-f21 x) t := by
      exact iteratedFDeriv_const_smul_apply (a:=a)
        ((hs20.sub hs21).contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))
    rw [hscalar,norm_smul,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_left hsub (abs_nonneg a)
    nlinarith [hm]
  have hq2 : ‖iteratedFDeriv ℝ j q2 t‖≤|b| *(j.factorial:ℝ)*A := by
    have hscalar : iteratedFDeriv ℝ j q2 t =
        b • iteratedFDeriv ℝ j f0 t := by
      exact iteratedFDeriv_const_smul_apply (a:=b)
        (hs0.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))
    rw [hscalar,norm_smul,Real.norm_eq_abs]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hn0 (abs_nonneg b))
  change ‖iteratedFDeriv ℝ j (q1+q2) t‖ ≤ _
  rw [iteratedFDeriv_add_apply
    (hs1.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))
    (hs2.contDiffAt.of_le (by simp : (j:ℕ∞ω)≤∞))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j q1 t‖+‖iteratedFDeriv ℝ j q2 t‖ := norm_add_le _ _
    _ ≤ 2*|a| *(j.factorial:ℝ)*A^2*(2:ℝ)^j+
      |b| *(j.factorial:ℝ)*A := add_le_add hq1 hq2

/-- LITERAL ORIGINAL Parity(4.14) h=-2 η_n logarithmic argument:
using source U*V≥exp L, E and Z polynomial geometry and k≠0,
the true 3D order-j derivative is at most
  8*L^(K0+88)*j!*A²*2^j + j!*A.
The 2/(UV)*exp(-t1) correction is present and paid; this is
not the incorrect h=0 two-exponential formula. -/
theorem parity_original_historical_eta_n_log_arg_3d_polylog434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hk : k≠0)
    (hZ : 0≤Z) (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ j
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
    8*L^(K0+88)*(j.factorial:ℝ)*A^2*(2:ℝ)^j+(j.factorial:ℝ)*A := by
  have hLp : 0<L := by linarith
  let a := Z/((k:ℝ)*U*V)
  let b := 2/(U*V)
  have ha := parity_original_historical_eta_n_parameter_polylog434
    L U V Z K0 k hLp hU hV hk hUV hZ hZupper
  have hb := (parity_original_historical_eta_n_shift_parameter_le_one434
    L U V hL hU hV hUV)
  have hbase := parity_original_historical_eta_n_real_3d_fderiv_log_box434
    A hA a b j t h0 h1 h2
  have hFun : (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) =
      (fun t => a*(Real.exp (t 2-t 0)-Real.exp (t 2-t 1)) +
        b*Real.exp (-(t 0))) := by
    funext x
    exact parity_original_historical_eta_n_log_arg_exp_difference434 U V Z k x
  rw [hFun]
  have hleft : 0≤2*(j.factorial:ℝ)*A^2*(2:ℝ)^j := by positivity
  have hright : 0≤(j.factorial:ℝ)*A := by positivity
  have haBound : 2*|a| *(j.factorial:ℝ)*A^2*(2:ℝ)^j ≤
      8*L^(K0+88)*(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    have hm := mul_le_mul_of_nonneg_right ha hleft
    nlinarith [hm]
  have hbAbs : |b|≤1 := by
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hbBound : |b| *(j.factorial:ℝ)*A≤(j.factorial:ℝ)*A := by
    nlinarith [mul_le_mul_of_nonneg_right hbAbs hright]
  exact hbase.trans (add_le_add haBound hbBound)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalEtaNLogArgUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The FULL original Parity(4.14) h=-2 n-argument has genuine
all-positive-order Euclidean derivative bound with ONE source
polylog base:
  ||D^i g_n(t)|| ≤ (L^(K0+89))^i   for 1≤ i≤J
on fixed |t_r|≤log A, from the original physical Z upper range,
UV≥exp L, nonzero k, and no missing 2/(UV) correction.
The lower threshold on L depends only on fixed J and fixed A. -/
theorem parity_original_historical_eta_n_log_arg_all_derivatives_uniform434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A ≤ L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ∀ (i : ℕ), 1 ≤ i → i ≤ J →
      ‖iteratedFDeriv ℝ i
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaNLogArg434 U V Z k
            (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
      (L^(K0+89))^i := by
  have hLp : 0<L := by linarith
  have hL1 : (1:ℝ)≤L := by linarith
  have hBpos : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
  have hB1 : (1:ℝ)≤L^(K0+88) := Real.one_le_rpow hL1 (by linarith)
  have hbase1 : (1:ℝ)≤L^(K0+89) := Real.one_le_rpow hL1 (by linarith)
  intro i hi hJ
  have hfactNat : i.factorial≤J.factorial := Nat.factorial_le hJ
  have hfact : (i.factorial:ℝ)≤(J.factorial:ℝ) := by exact_mod_cast hfactNat
  have h2pow : (2:ℝ)^i≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hJ
  have hBase := parity_original_historical_eta_n_log_arg_3d_polylog434
    L U V Z K0 A k hL hU hV hUV hk hZ hZupper hA i t h0 h1 h2
  have hFactPow : (i.factorial:ℝ)*(2:ℝ)^i ≤ (J.factorial:ℝ)*(2:ℝ)^J :=
    mul_le_mul hfact h2pow (by positivity) (by positivity)
  have hTerm1 : 8*L^(K0+88)*(i.factorial:ℝ)*A^2*(2:ℝ)^i ≤
      8*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J := by
    have hh := mul_le_mul_of_nonneg_left hFactPow (by positivity : 0≤8*L^(K0+88)*A^2)
    nlinarith [hh]
  have hTerm2 : (i.factorial:ℝ)*A≤(J.factorial:ℝ)*A :=
    mul_le_mul_of_nonneg_right hfact hA.le
  have hTerm : 8*L^(K0+88)*(i.factorial:ℝ)*A^2*(2:ℝ)^i+
      (i.factorial:ℝ)*A ≤
      8*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J+
      (J.factorial:ℝ)*A := add_le_add hTerm1 hTerm2
  have hD :
      8*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J+
        (J.factorial:ℝ)*A ≤ L^(K0+89) := by
    have hm := mul_le_mul_of_nonneg_right hLarge hBpos.le
    have hpow : L^(K0+89)=L^(K0+88)*L := by
      have hEq : K0+89=(K0+88)+1 := by ring
      rw [hEq,Real.rpow_add hLp,Real.rpow_one]
    have hlast : (J.factorial:ℝ)*A ≤ (J.factorial:ℝ)*A*L^(K0+88) := by
      have hC : (0:ℝ)≤(J.factorial:ℝ)*A := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hB1 hC]
    rw [hpow]
    nlinarith [hm,hlast]
  have hPow : L^(K0+89)≤(L^(K0+89))^i := by
    have hh := pow_le_pow_right₀ hbase1 hi
    simpa only [pow_one] using hh
  exact hBase.trans (hTerm.trans (hD.trans hPow))

/-- The ACTUAL historical original h=-2 η_n pulledback
THREE-DIMENSIONAL cutoff now has uniform pointwise order-J
Fréchet derivative bound
  J! K^n_J L^((K0+89)(J+1))
for every physical Euclidean log point in the fixed buffer box,
with the actual source Z/(kUV) and 2/(UV) correction. No missing
source Fourier factor or analytic hypothesis; remaining original
3D Schwartz seminorm proof is a finite product with η_e and buffers. -/
theorem parity_original_historical_actual_eta_n_3d_composed_polylog434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
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
      L^((K0+89)*((J:ℝ)+1)) := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun t =>
    parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  have hg : ContDiff ℝ ∞ g :=
    (parity_original_historical_eta_n_log_arg_smooth434 U V Z k).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  have hd := parity_original_historical_eta_n_log_arg_all_derivatives_uniform434
    L U V Z K0 A k hL hK0 hU hV hUV hk hZ hZupper
    hA J hLarge t h0 h1 h2
  exact parity_original_historical_eta_n_3d_composition_polylog434
    L hL J (K0+89) (by linarith) g hg t hd
end Green64Analytic.Parity

end

end

