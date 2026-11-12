module

public import Mathlib
public import Green64.Library.Analysis.Estimates.Part001
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.MellinTransform
public import Green64.Library.Analysis.Compactness.Part002
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Weights / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## CoprimeSpacing -/

section

namespace Green64SourceC6

/-! A rational approximant with coprime numerator cannot have
 a short nonzero integer difference with vanishing reduced residue. -/
theorem rational_difference_nonzero
    (a r d z : ℤ) (hr : 0 < r) (hd : 0 < d)
    (hdr : d < r) (hacop : Int.gcd a r = 1) :
    a * d - z * r ≠ 0 := by
  intro hzero
  have hrdiv : r ∣ a * d := by
    refine ⟨z, ?_⟩
    nlinarith [hzero]
  have hgc : Int.gcd r a = 1 := by simpa [Int.gcd_comm] using hacop
  have hrdivd : r ∣ d := by
    apply Int.dvd_of_dvd_mul_left_of_gcd_one (c := a) ?_ hgc
    simpa [mul_comm] using hrdiv
  have hmodzero := Int.emod_eq_zero_of_dvd hrdivd
  have hmodd := Int.emod_eq_of_lt (le_of_lt hd) hdr
  omega

end Green64SourceC6

namespace Green64SourceC6

/-- Literal source rational-arc separation, for every integer center z.
This is uniform for arbitrary real beta of magnitude ≤ r⁻². -/
theorem short_rational_arc_separation
    (a r d z : ℤ) (beta : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hhalf : 2 * d ≤ r)
    (hacop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    (1 : ℝ) / (2 * (r : ℝ)) ≤
      |((a : ℝ) / (r : ℝ) + beta) * (d : ℝ) - (z : ℝ)| := by
  have hdr : d < r := by omega
  have hnz : a * d - z * r ≠ 0 :=
    rational_difference_nonzero a r d z hr hd hdr hacop
  have hnumInt : (1 : ℤ) ≤ |a * d - z * r| := by
    have hh : 0 < |a * d - z * r| := abs_pos.mpr hnz
    omega
  have hnum : (1 : ℝ) ≤ |((a * d - z * r : ℤ) : ℝ)| := by
    exact_mod_cast hnumInt
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hhR : (2 : ℝ) * (d : ℝ) ≤ (r : ℝ) := by exact_mod_cast hhalf
  have hrat : (a : ℝ) / (r : ℝ) * (d : ℝ) - (z : ℝ) =
      ((a * d - z * r : ℤ) : ℝ) / (r : ℝ) := by
    push_cast
    field_simp
  have hratLower : (1 : ℝ) / (r : ℝ) ≤
      |(a : ℝ) / (r : ℝ) * (d : ℝ) - (z : ℝ)| := by
    rw [hrat, abs_div, abs_of_pos hrR]
    exact (div_le_div_iff_of_pos_right hrR).mpr hnum
  have hbetaMul : |beta * (d : ℝ)| ≤ 1 / (2 * (r : ℝ)) := by
    rw [abs_mul, abs_of_pos hdR]
    have hn : 0 ≤ (1 : ℝ) / (r : ℝ)^2 := by positivity
    calc
      |beta| * (d : ℝ) ≤ (1 / ((r : ℝ)^2)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbeta (le_of_lt hdR)
      _ ≤ (1 / ((r : ℝ)^2)) * ((r : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hhR]) hn
      _ = 1 / (2 * (r : ℝ)) := by field_simp
  have htri : |(a : ℝ) / (r : ℝ) * (d : ℝ) - (z : ℝ)| ≤
      |((a : ℝ) / (r : ℝ) + beta) * (d : ℝ) - (z : ℝ)| +
        |beta * (d : ℝ)| := by
    calc
      _ = |(((a : ℝ) / (r : ℝ) + beta) * (d : ℝ) - (z : ℝ)) -
          beta * (d : ℝ)| := by congr 1; ring
      _ ≤ |((a : ℝ) / (r : ℝ) + beta) * (d : ℝ) - (z : ℝ)| +
          |beta * (d : ℝ)| := by simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le (((a : ℝ) / (r : ℝ) + beta) * (d : ℝ) - (z : ℝ))
                (-(beta * (d : ℝ))))
  have heq : (1 : ℝ) / (r : ℝ) = 2 * (1 / (2 * (r : ℝ))) := by
    field_simp
  rw [heq] at hratLower
  linarith

end Green64SourceC6

end

/-! ## ExactAdditiveKernel -/

section

namespace Green64SourceC6

/-- The literal e(theta*n) factor from source C6. -/
noncomputable def integerPhase (theta : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * theta * (n : ℝ) : ℝ) : ℂ) * Complex.I)

theorem integerPhase_unit (theta : ℝ) (n : ℤ) :
    ‖integerPhase theta n‖ = 1 := by
  simp [integerPhase, Complex.norm_exp, Complex.mul_re]

theorem integerPhase_add (theta : ℝ) (n m : ℤ) :
    integerPhase theta (n + m) = integerPhase theta n * integerPhase theta m := by
  unfold integerPhase
  rw [Int.cast_add]
  convert Complex.exp_add _ _ using 1 <;> push_cast <;> ring

theorem integerPhase_nat (theta : ℝ) (n : ℕ) :
    integerPhase theta (n : ℤ) = (integerPhase theta 1)^n := by
  induction n with
  | zero => simp [integerPhase]
  | succ n ih =>
      have hs : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_cast
      rw [hs, integerPhase_add, ih, pow_succ]

end Green64SourceC6

end

/-! ## SourceOriginalC6FourierPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL source03 integer C6 phase is EXACTLY the
Fourier product phase for actual NATURAL products n*m:
exp(2πi*(theta*m)*n)=exp(2πi*theta*(n*m)).
The C6 prime atom window convention uses the B product m
inside the phase argument, so this identity prevents an
incorrect swap/conjugation when coupled to original -kθ. -/
theorem source_original_C6_integer_phase_natural_product434
    (theta : ℝ) (n m : ℕ) :
    Green64SourceC6.integerPhase (theta*(m:ℝ)) (n:ℤ) =
      Green64SourceC6.integerPhase theta ((n*m:ℕ):ℤ) := by
  unfold Green64SourceC6.integerPhase
  apply congrArg Complex.exp
  push_cast
  ring

/-- SOURCE03's ORIGINAL Fourier convention uses -kθ for
the shifted translation w' = w+k D_A D_B. When
Dirichlet's approximation is written exactly as
-kθ = a/r+beta, the C6 integer multiplier on the two
selected original A/B products is identical to the true
Fourier multiplier without any dropped imaginary sign,
modulus or 2π factor. -/
theorem source_original_C6_integer_phase_dirichlet_exact434
    (theta : ℝ) (k a : ℤ) (r : ℕ)
    (beta : ℝ) (n m : ℕ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta) :
    Green64SourceC6.integerPhase
      (((a:ℝ)/(r:ℝ)+beta)*(m:ℝ)) (n:ℤ) =
    Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) ((n*m:ℕ):ℤ) := by
  rw [←hApprox]
  exact source_original_C6_integer_phase_natural_product434
    (-(k:ℝ)*theta) n m
end Green64Analytic.CorrelationSquare

end

/-! ## ChordLower -/

section

namespace Green64SourceC6

/-- The exact chord inequality needed to turn a geometric kernel into
 a distance-to-integers kernel. -/
theorem fundamental_chord_lower (theta : ℝ)
    (hzero : 0 ≤ theta) (hhalf : theta ≤ 1/2) :
    4 * theta ≤ ‖1 - integerPhase theta 1‖ := by
  have hbound : 2 * theta ≤ Real.sin (Real.pi * theta) := by
    have hh := Real.le_sin_mul (x := 2 * theta) (by linarith) (by linarith)
    convert hh using 1 <;> ring
  have hsin : 0 ≤ Real.sin (Real.pi * theta) := by linarith
  have hphase :
      ‖1 - integerPhase theta 1‖ =
      ‖Complex.exp (Complex.I * ((2 * Real.pi * theta : ℝ) : ℂ)) - 1‖ := by
    rw [norm_sub_rev]
    congr 1
    unfold integerPhase
    push_cast
    ring
  rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : ((2 * Real.pi * theta : ℝ) / 2) = Real.pi * theta := by ring
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sin (Real.pi * theta))]
  linarith

end Green64SourceC6

namespace Green64SourceC6

theorem phase_chord_identity (theta : ℝ) :
    ‖1 - integerPhase theta 1‖ = 2 * |Real.sin (Real.pi * theta)| := by
  have hphase : ‖1 - integerPhase theta 1‖ =
      ‖Complex.exp (Complex.I * ((2 * Real.pi * theta : ℝ) : ℂ)) - 1‖ := by
    rw [norm_sub_rev]
    congr 1
    unfold integerPhase
    push_cast
    ring
  rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : ((2 * Real.pi * theta : ℝ) / 2) = Real.pi * theta := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

theorem signed_fundamental_chord_lower (theta : ℝ)
    (hbound : |theta| ≤ 1/2) :
    4 * |theta| ≤ ‖1 - integerPhase theta 1‖ := by
  rcases le_total 0 theta with hpos | hneg
  · rw [abs_of_nonneg hpos]
    exact fundamental_chord_lower theta hpos (by rwa [abs_of_nonneg hpos] at hbound)
  · have hp : 0 ≤ -theta := by linarith
    have hb : -theta ≤ 1/2 := by rw [abs_of_nonpos hneg] at hbound; exact hbound
    have hh := fundamental_chord_lower (-theta) hp hb
    rw [phase_chord_identity] at hh ⊢
    simp only [mul_neg, Real.sin_neg, abs_neg] at hh
    simpa [abs_of_nonpos hneg] using hh

end Green64SourceC6

namespace Green64SourceC6

/-- Additive phase is literally periodic by each integer in frequency. -/
theorem integerPhase_frequency_period (theta : ℝ) (z : ℤ) :
    integerPhase (theta - (z : ℝ)) 1 = integerPhase theta 1 := by
  unfold integerPhase
  have harg :
      ((2 * Real.pi * (theta - (z : ℝ)) * (1 : ℝ) : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * theta * (1 : ℝ) : ℝ) : ℂ) * Complex.I +
        ((-z : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [Int.cast_one, mul_one] at harg ⊢
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A nearest integer center works uniformly, including exact half-integers. -/
theorem nearest_integer_chord (theta : ℝ) :
    ∃ z : ℤ, |theta - (z : ℝ)| ≤ 1/2 ∧
      4 * |theta - (z : ℝ)| ≤ ‖1 - integerPhase theta 1‖ := by
  let z := ⌊theta + 1/2⌋
  have hlow : (z : ℝ) ≤ theta + 1/2 := Int.floor_le _
  have hhigh : theta + 1/2 < (z : ℝ) + 1 := Int.lt_floor_add_one _
  have hdist : |theta - (z : ℝ)| ≤ 1/2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨z, hdist, ?_⟩
  have hh := signed_fundamental_chord_lower (theta - (z : ℝ)) hdist
  rw [integerPhase_frequency_period] at hh
  exact hh

end Green64SourceC6

end

/-! ## ExactOrderedTuples -/

section

set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Canonical finite set of ALL ordered prime lists with ell entries,
formed from the exact prime factors of actual rough integers.
The permutation list may contain duplicates; toFinset removes duplicates,
while the overcount is bounded by ell!. -/
noncomputable def allPrimeTuples (ell : ℕ) (z x : ℝ) :
    Finset (List ℕ) := by
  classical
  exact (roughSet z x).biUnion (fun n =>
    if n.primeFactorsList.length = ell
    then n.primeFactorsList.permutations.toFinset else ∅)

theorem mem_roughSet_iff (z x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    n ∈ roughSet z x ↔
      0 < n ∧ (n:ℝ) ≤ x ∧
        ∀ p : ℕ, Nat.Prime p → (p:ℝ) ≤ z → ¬p ∣ n := by
  simp only [roughSet, Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.le_floor_iff hx]
  tauto


/-- Every canonical ordered tuple belongs to an actual rough integer,
and the converse holds. This covers empty lists (ell=0, n=1)
and repeated prime factors without a squarefree assumption. -/
theorem mem_allPrimeTuples_iff (ell : ℕ) (z x : ℝ)
    (hx : 0 ≤ x) (l : List ℕ) :
    l ∈ allPrimeTuples ell z x ↔
      l.length = ell ∧
      (∀ p ∈ l, Nat.Prime p ∧ z < (p:ℝ)) ∧
      0 < l.prod ∧ (l.prod:ℝ) ≤ x := by
  classical
  constructor
  · intro hl
    rcases (Finset.mem_biUnion.mp (by simpa only [allPrimeTuples] using hl)) with
      ⟨n, hn, hl'⟩
    have hnrough := (mem_roughSet_iff z x hx n).mp hn
    by_cases hnlen : n.primeFactorsList.length = ell
    · have hperm : l.Perm n.primeFactorsList := by
        simpa only [ite_eq_left hnlen, List.mem_toFinset,
          List.mem_permutations] using hl'
      have hn0 : n ≠ 0 := Nat.ne_of_gt hnrough.1
      have hprod : l.prod = n :=
        hperm.prod_eq.trans (Nat.prod_primeFactorsList hn0)
      have hlength : l.length = ell := hperm.length_eq.trans hnlen
      refine ⟨hlength,?_,?_,?_⟩
      · intro p hp
        have hpm : p ∈ n.primeFactorsList := hperm.mem_iff.mp hp
        have hprime := Nat.prime_of_mem_primeFactorsList hpm
        refine ⟨hprime,?_⟩
        by_contra hbad
        exact hnrough.2.2 p hprime (le_of_not_gt hbad)
          (Nat.dvd_of_mem_primeFactorsList hpm)
      · rw [hprod]
        exact hnrough.1
      · rw [hprod]
        exact hnrough.2.1
    · simp [hnlen] at hl'
  · rintro ⟨hlen,hall,hpos,hbound⟩
    have hpr : ∀ p ∈ l, Nat.Prime p := fun p hp => (hall p hp).1
    have hbig : ∀ p ∈ l, z < (p:ℝ) := fun p hp => (hall p hp).2
    have hn : l.prod ∈ roughSet z x := by
      apply (mem_roughSet_iff z x hx l.prod).mpr
      exact ⟨hpos,hbound,prime_list_product_rough l z hpr hbig⟩
    have hperm : l.Perm (l.prod).primeFactorsList :=
      Nat.primeFactorsList_unique rfl hpr
    have hlenCanon : (l.prod).primeFactorsList.length = ell :=
      hperm.length_eq.symm.trans hlen
    apply (Finset.mem_biUnion).mpr
    refine ⟨l.prod,hn,?_⟩
    simp only [ite_eq_left hlenCanon, List.mem_toFinset, List.mem_permutations]
    exact hperm

/-- The exact finite SOURCE ordered prime family is bounded by
ell! times the ACTUAL rough integer count. No distinct-prime,
squarefree, or positivity-of-prime-mass assumptions. -/
theorem allPrimeTuples_card_le_rough (ell : ℕ) (z x : ℝ)
    (hx : 0 ≤ x) :
    (allPrimeTuples ell z x).card ≤
      ell.factorial * (roughSet z x).card := by
  apply prime_tuple_card_le_rough_card
    (allPrimeTuples ell z x) ell z x
  · intro l hl
    exact ((mem_allPrimeTuples_iff ell z x hx l).mp hl).1
  · intro l hl p hp
    exact (((mem_allPrimeTuples_iff ell z x hx l).mp hl).2.1 p hp).1
  · intro l hl p hp
    exact (((mem_allPrimeTuples_iff ell z x hx l).mp hl).2.1 p hp).2
  · intro l hl
    exact ((mem_allPrimeTuples_iff ell z x hx l).mp hl).2.2.2

end Green64Analytic.OrderedPrimeRough

end

/-! ## DisjointLengthClasses -/

section

set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Green64Analytic.OrderedPrimeRough

/-- Real-cutoff rough integers of one exact Omega(n) length.
This is a partition by multiplicity-counted prime factor length;
nothing here assumes squarefreeness. -/
noncomputable def roughLengthClass (ell : ℕ) (z x : ℝ) : Finset ℕ :=
  (roughSet z x).filter (fun n => n.primeFactorsList.length = ell)

theorem roughLengthClass_subset_rough (ell : ℕ) (z x : ℝ) :
    roughLengthClass ell z x ⊆ roughSet z x := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

theorem roughLengthClass_disjoint (i j : ℕ) (z x : ℝ) (hij : i ≠ j) :
    Disjoint (roughLengthClass i z x) (roughLengthClass j z x) := by
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hi := (Finset.mem_filter.mp hni).2
  have hj := (Finset.mem_filter.mp hnj).2
  exact hij (hi.symm.trans hj)

/-- No sum-over-ell overcount: length classes have disjoint support. -/
theorem lengthClass_total_card_le_rough
    (K : Finset ℕ) (z x : ℝ) :
    (∑ ell ∈ K, (roughLengthClass ell z x).card) ≤
      (roughSet z x).card := by
  classical
  have hd : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      Disjoint (roughLengthClass i z x) (roughLengthClass j z x) := by
    intro i hi j hj hij
    exact roughLengthClass_disjoint i j z x hij
  have hc : (K.biUnion (fun ell => roughLengthClass ell z x)).card =
      ∑ ell ∈ K, (roughLengthClass ell z x).card :=
    Finset.card_biUnion hd
  have hs : (K.biUnion (fun ell => roughLengthClass ell z x)) ⊆ roughSet z x := by
    intro n hn
    obtain ⟨ell, hK, he⟩ := Finset.mem_biUnion.mp hn
    exact roughLengthClass_subset_rough ell z x he
  calc
    ∑ ell ∈ K, (roughLengthClass ell z x).card =
      (K.biUnion (fun ell => roughLengthClass ell z x)).card := hc.symm
    _ ≤ (roughSet z x).card := Finset.card_le_card hs

/-- Stronger exact-support form of the old factorial bound. -/
theorem allPrimeTuples_card_le_lengthClass (ell : ℕ) (z x : ℝ)
    (hx : 0 ≤ x) :
    (allPrimeTuples ell z x).card ≤
      ell.factorial * (roughLengthClass ell z x).card := by
  classical
  apply ordered_prime_lists_card_le_factorial_mul
    (allPrimeTuples ell z x) (roughLengthClass ell z x) ell
  · intro l hl
    exact ((mem_allPrimeTuples_iff ell z x hx l).mp hl).1
  · intro l hl p hp
    exact (((mem_allPrimeTuples_iff ell z x hx l).mp hl).2.1 p hp).1
  · intro l hl
    have hinfo := (mem_allPrimeTuples_iff ell z x hx l).mp hl
    have hpr : ∀ p ∈ l, Nat.Prime p :=
      fun p hp => (hinfo.2.1 p hp).1
    have hbig : ∀ p ∈ l, z < (p : ℝ) :=
      fun p hp => (hinfo.2.1 p hp).2
    have hperm : l.Perm (l.prod).primeFactorsList :=
      Nat.primeFactorsList_unique rfl hpr
    have hlength : (l.prod).primeFactorsList.length = ell :=
      hperm.length_eq.symm.trans hinfo.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlength⟩
    apply (mem_roughSet_iff z x hx l.prod).mpr
    exact ⟨hinfo.2.2.1, hinfo.2.2.2,
      prime_list_product_rough l z hpr hbig⟩

/-- Each factorial-normalized ordered prime term is charged only to its
OWN exact Ω-length class of nonsquarefree rough integers. -/
theorem single_length_div_factorial_le (ell : ℕ) (z x : ℝ)
    (hx : 0 ≤ x) :
    ((allPrimeTuples ell z x).card : ℝ) / (ell.factorial : ℝ) ≤
      ((roughLengthClass ell z x).card : ℝ) := by
  have hc := allPrimeTuples_card_le_lengthClass ell z x hx
  have hcR : ((allPrimeTuples ell z x).card : ℝ) ≤
      (ell.factorial : ℝ) * ((roughLengthClass ell z x).card : ℝ) := by
    exact_mod_cast hc
  exact (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos ell)).mpr (by
    simpa only [mul_comm] using hcR)

/-- The missing finite simultaneous ell-sum comparison.
The factor (number of lengths) does NOT appear: prime factorization
lengths are disjoint even for repeated prime factors and n=1. -/
theorem all_lengths_factorial_sum_le_rough
    (K : Finset ℕ) (z x : ℝ) (hx : 0 ≤ x) :
    (∑ ell ∈ K,
      ((allPrimeTuples ell z x).card : ℝ) / (ell.factorial : ℝ)) ≤
      ((roughSet z x).card : ℝ) := by
  calc
    (∑ ell ∈ K,
        ((allPrimeTuples ell z x).card : ℝ) / (ell.factorial : ℝ)) ≤
        ∑ ell ∈ K, ((roughLengthClass ell z x).card : ℝ) := by
          apply Finset.sum_le_sum
          intro ell he
          exact single_length_div_factorial_le ell z x hx
    _ = ((∑ ell ∈ K, (roughLengthClass ell z x).card) : ℝ) := by
        rfl
    _ ≤ ((roughSet z x).card : ℝ) := by
        exact_mod_cast lengthClass_total_card_le_rough K z x

end Green64Analytic.OrderedPrimeRough

end

/-! ## G1Convergence -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem lfunction_periodic_remainder_convergence :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ), 1 ≤ Y → 1 < s.re →
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ);
  let B : ℝ → ℂ := fun u =>
    (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) - (u:ℂ)*c;
  DirichletCharacter.LFunction χ s =
    (∑ n ∈ Finset.range (⌊Y⌋₊+1),
      if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) +
    c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
    s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1) :=
by
  intro q inst χ Y s hY hs
  have hIdentity : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Y : ℝ) (s : ℂ), 1 ≤ Y → 1 < s.re →
      let A : ℝ → ℂ := fun u => ∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)
      DirichletCharacter.LFunction χ s =
        (∑ n ∈ Finset.range (⌊Y⌋₊+1),
          if n = 0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) -
        (Y:ℂ)^(-s) * A Y -
        ∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u := by
      intro q inst χ Y s hY hs
      let A : ℝ → ℂ := fun u => ∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)
      have habel : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
            (Y M : ℝ) (s : ℂ), 1 ≤ Y → Y ≤ M →
          (∑ n ∈ Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊, ((n:ℂ)^(-s)) * χ (n : ZMod q)) =
            (M:ℂ)^(-s) * (∑ i ∈ Finset.range ⌊M⌋₊, χ ((i+1 : ℕ) : ZMod q)) -
            (Y:ℂ)^(-s) * (∑ i ∈ Finset.range ⌊Y⌋₊, χ ((i+1 : ℕ) : ZMod q)) -
            ∫ t in Set.Ioc Y M, ((-s)*(t:ℂ)^(-s-1)) *
              (∑ i ∈ Finset.range ⌊t⌋₊, χ ((i+1 : ℕ) : ZMod q)) := by
          intro q inst χ Y M s hY hYM
          let f : ℝ → ℂ := fun t => (t:ℂ)^(-s)
          have habel : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Y M : ℝ) (f : ℝ → ℂ),
          1 ≤ Y → Y ≤ M →
          (∀ t ∈ Set.Icc Y M, DifferentiableAt ℝ f t) →
          MeasureTheory.IntegrableOn (deriv f) (Set.Icc Y M) →
          (∑ n ∈ Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊, f (n : ℝ) * χ (n : ZMod q)) =
            f M * (∑ i ∈ Finset.range ⌊M⌋₊, χ ((i+1 : ℕ) : ZMod q)) -
            f Y * (∑ i ∈ Finset.range ⌊Y⌋₊, χ ((i+1 : ℕ) : ZMod q)) -
            ∫ t in Set.Ioc Y M, deriv f t * (∑ i ∈ Finset.range ⌊t⌋₊, χ ((i+1 : ℕ) : ZMod q)) := by
              intro q inst χ Y M f hY hYM hdiff hint
              let c : ℕ → ℂ := fun n => if n = 0 then 0 else χ (n : ZMod q)
              have hc : c 0 = 0 := by simp [c]
              have hrange : ∀ n : ℕ, (∑ k ∈ Finset.Icc 0 n, c k) =
                  (∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q)) := by
                intro n
                have hprefix : ∀ (d : ℕ → ℂ), d 0 = 0 → ∀ n : ℕ,
                    (∑ k ∈ Finset.Icc 0 n, d k) = (∑ i ∈ Finset.range n, d (i+1)) := by
                  intro d hd n
                  induction n with
                  | zero => simp [hd]
                  | succ n ih =>
                    rw [← Finset.insert_Icc_right_eq_Icc_add_one (Nat.zero_le (n+1)),
                        Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
                    ring
                rw [hprefix c hc n]
                apply Finset.sum_congr rfl
                intro i hi
                simp [c]
              have hsum :
                  (∑ n ∈ Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊, f (n : ℝ) * c n) =
                  (∑ n ∈ Finset.Ioc ⌊Y⌋₊ ⌊M⌋₊, f (n : ℝ) * χ (n : ZMod q)) := by
                apply Finset.sum_congr rfl
                intro n hn
                have hn0 : n ≠ 0 := by
                  have hlt := (Finset.mem_Ioc.mp hn).1
                  omega
                simp [c, hn0]
              have hab := sum_mul_eq_sub_sub_integral_mul c (by linarith) hYM hdiff hint
              simp only [hsum, hrange] at hab
              exact hab
          have hready : ∀ (Y M : ℝ) (s : ℂ), 1 ≤ Y → Y ≤ M →
          (∀ t ∈ Set.Icc Y M, DifferentiableAt ℝ (fun u : ℝ => (u:ℂ)^(-s)) t) ∧
          MeasureTheory.IntegrableOn (deriv (fun u : ℝ => (u:ℂ)^(-s))) (Set.Icc Y M) := by
              intro Y M s hY hYM
              have hderiv : ∀ t ∈ Set.Icc Y M,
                  deriv (fun u : ℝ => (u:ℂ)^(-s)) t = (-s)*(t:ℂ)^(-s-1) := by
                intro t ht
                have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < Y) ht.1
                by_cases hs : s = 0
                · subst s
                  simp
                · exact Complex.deriv_ofReal_cpow_const (ne_of_gt ht0) (neg_ne_zero.mpr hs)
              have hd : ∀ t ∈ Set.Icc Y M,
                   DifferentiableAt ℝ (fun u : ℝ => (u:ℂ)^(-s)) t := by
                intro t ht
                have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < Y) ht.1
                by_cases hs : s = 0
                · subst s
                  simpa using (differentiableAt_const (c := (1:ℂ)) (x := t))
                · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt ht0)
                    (neg_ne_zero.mpr hs)).differentiableAt
              have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-s-1)) (Set.Icc Y M) := by
                intro t ht
                have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < Y) ht.1
                exact (continuousAt_const.mul
                  (Complex.continuousAt_ofReal_cpow_const t (-s-1) (Or.inr ht0.ne'))).continuousWithinAt
              refine ⟨hd, ?_⟩
              exact (hcont.integrableOn_Icc).congr_fun
                (fun t ht => (hderiv t ht).symm) measurableSet_Icc
          obtain ⟨hd, hint⟩ := hready Y M s hY hYM
          have hab := habel q χ Y M f hY hYM hd hint
          have hInt :
              (∫ t in Set.Ioc Y M, deriv f t *
                (∑ i ∈ Finset.range ⌊t⌋₊, χ ((i+1 : ℕ) : ZMod q))) =
              (∫ t in Set.Ioc Y M, ((-s)*(t:ℂ)^(-s-1)) *
                (∑ i ∈ Finset.range ⌊t⌋₊, χ ((i+1 : ℕ) : ZMod q))) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
            intro t ht
            apply congrArg (fun z : ℂ => z *
              (∑ i ∈ Finset.range ⌊t⌋₊, χ ((i+1 : ℕ) : ZMod q)))
            change deriv (fun u : ℝ => (u:ℂ)^(-s)) t = (-s)*(t:ℂ)^(-s-1)
            have ht0 : 0 < t := lt_trans (by linarith : 0 < Y) ht.1
            by_cases hs : s = 0
            · subst s
              simp
            · exact Complex.deriv_ofReal_cpow_const (ne_of_gt ht0) (neg_ne_zero.mpr hs)
          rw [hInt] at hab
          simpa only [f, Complex.ofReal_natCast] using hab
      have hLseries : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
          1 < s.re →
          Filter.Tendsto (fun N : ℕ =>
            ∑ n ∈ Finset.range N,
              if n = 0 then (0:ℂ) else χ (n : ZMod q) * (n:ℂ)^(-s))
              Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
          intro q inst χ s hs
          have hsumm : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
            DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
          have heq : ∀ n : ℕ, LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n =
              (if n = 0 then (0:ℂ) else χ (n : ZMod q) * (n:ℂ)^(-s)) := by
            intro n
            by_cases hn : n = 0
            · simp [hn, LSeries.term]
            · simp [hn, LSeries.term_of_ne_zero, Complex.cpow_neg, div_eq_mul_inv]
          rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
          have htend : Filter.Tendsto
              (fun N : ℕ => ∑ n ∈ Finset.range N, LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n)
              Filter.atTop (nhds (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
            simpa only [LSeries] using hsumm.hasSum.tendsto_sum_nat
          convert htend using 1
          ext N
          apply Finset.sum_congr rfl
          intro n hn
          exact (heq n).symm
      have hBoundary : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
          1 < s.re →
          Filter.Tendsto (fun N : ℕ => (N:ℂ)^(-s) *
            (∑ i ∈ Finset.range N, χ ((i+1 : ℕ) : ZMod q)))
          Filter.atTop (nhds 0) := by
          intro q inst χ s hs
          have hsum : ∀ N : ℕ, ‖∑ i ∈ Finset.range N, χ ((i+1 : ℕ) : ZMod q)‖ ≤ (N:ℝ) := by
            intro N
            calc
              _ ≤ ∑ i ∈ Finset.range N, ‖χ ((i+1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
              _ ≤ ∑ _i ∈ Finset.range N, (1:ℝ) :=
                Finset.sum_le_sum (fun i hi => χ.norm_le_one _)
              _ = (N:ℝ) := by simp
          apply squeeze_zero_norm'
          · filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with N hN
            have hn : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1:ℕ)) hN)
            have hpos : 0 ≤ (N:ℝ)^(-s.re) := Real.rpow_nonneg hn.le _
            calc
              ‖(N:ℂ)^(-s) * (∑ i ∈ Finset.range N, χ ((i+1 : ℕ) : ZMod q))‖ =
                (N:ℝ)^(-s.re) * ‖∑ i ∈ Finset.range N, χ ((i+1 : ℕ) : ZMod q)‖ := by
                rw [norm_mul, Complex.norm_natCast_cpow_of_pos
                  (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hN) (-s)]
                simp
              _ ≤ (N:ℝ)^(-s.re) * (N:ℝ) :=
                mul_le_mul_of_nonneg_left (hsum N) hpos
              _ = (N:ℝ)^(-(s.re-1)) := by
                rw [show -(s.re-1) = -s.re+1 by ring, Real.rpow_add hn]
                simp
          · exact (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
              tendsto_natCast_atTop_atTop
      have hAint : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
            (Y : ℝ) (s : ℂ), 0 < Y → 1 < s.re →
          MeasureTheory.IntegrableOn
            (fun u : ℝ => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) *
              (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
          intro q inst χ Y s hY hs
          have hsum : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q)‖ ≤ (n:ℝ) := by
            intro n
            calc
              _ ≤ ∑ i ∈ Finset.range n, ‖χ ((i+1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
              _ ≤ ∑ _i ∈ Finset.range n, (1:ℝ) := Finset.sum_le_sum (fun i hi => χ.norm_le_one _)
              _ = (n:ℝ) := by simp
          have hg : MeasureTheory.IntegrableOn (fun u : ℝ => u^(-s.re)) (Set.Ioi Y) :=
            integrableOn_Ioi_rpow_of_lt (by linarith) hY
          have hm : Measurable
              (fun u : ℝ => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) * (u:ℂ)^(-s-1)) := by
            have hprefix : Measurable
              (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q)) :=
              (continuous_of_discreteTopology : Continuous (fun n : ℕ =>
                 ∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q))).measurable
            exact (hprefix.comp Nat.measurable_floor).mul (by fun_prop)
          apply hg.mono' hm.aestronglyMeasurable
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
          have hu0 : 0 < u := hY.trans hu
          have hn : ‖∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)‖ ≤ u := by
            exact (hsum ⌊u⌋₊).trans (Nat.floor_le hu0.le)
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
          calc
            _ ≤ u * u^(-s.re-1) :=
              mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hu0.le _)
            _ = u^(-s.re) := by
              rw [show -s.re = 1 + (-s.re-1) by ring, Real.rpow_add hu0]
              simp [mul_comm]
      have hDint : ∀ (A : ℝ → ℂ) (Y : ℝ) (s : ℂ),
          MeasureTheory.IntegrableOn (fun u : ℝ => A u * (u:ℂ)^(-s-1)) (Set.Ioi Y) →
          MeasureTheory.IntegrableOn (fun u : ℝ => ((-s)*(u:ℂ)^(-s-1)) * A u) (Set.Ioi Y) := by
          intro A Y s h
          have h' : MeasureTheory.IntegrableOn
              (fun u : ℝ => (-s) * (A u * (u:ℂ)^(-s-1))) (Set.Ioi Y) :=
            h.const_mul (-s)
          exact h'.congr_fun (fun u hu => by ring) measurableSet_Ioi
      have hIntegralLim : ∀ (f : ℝ → ℂ) (Y : ℝ),
          MeasureTheory.IntegrableOn f (Set.Ioi Y) →
          Filter.Tendsto (fun N : ℕ => ∫ u : ℝ in Set.Ioc Y (N:ℝ), f u)
              Filter.atTop (nhds (∫ u : ℝ in Set.Ioi Y, f u)) := by
          intro f Y hf
          have ht : Filter.Tendsto (fun N : ℕ => ∫ u : ℝ in Y..(N:ℝ), f u)
              Filter.atTop (nhds (∫ u : ℝ in Set.Ioi Y, f u)) :=
            MeasureTheory.intervalIntegral_tendsto_integral_Ioi Y hf tendsto_natCast_atTop_atTop
          refine ht.congr' ?_
          filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
            (Filter.eventually_ge_atTop Y)] with N hN
          rw [intervalIntegral.integral_of_le hN]
      have hSplit : ∀ (f : ℕ → ℂ) (y N : ℕ), y ≤ N →
          (∑ n ∈ Finset.Ioc y N, f n) =
          (∑ n ∈ Finset.range (N+1), if n=0 then (0:ℂ) else f n) -
          (∑ n ∈ Finset.range (y+1), if n=0 then (0:ℂ) else f n) := by
          intro f y N hyN
          let g : ℕ → ℂ := fun n => if n = 0 then 0 else f n
          have hset : Finset.Ioc y N =
              Finset.range (N+1) \ Finset.range (y+1) := by
            ext n
            simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range]
            omega
          have hsubset : Finset.range (y+1) ⊆ Finset.range (N+1) :=
            Finset.range_mono (Nat.add_le_add_right hyN 1)
          have hsum : (∑ n ∈ Finset.Ioc y N, g n) =
              (∑ n ∈ Finset.range (N+1), g n) -
              (∑ n ∈ Finset.range (y+1), g n) := by
            rw [hset, eq_sub_iff_add_eq]
            exact Finset.sum_sdiff hsubset
          convert hsum using 1
          apply Finset.sum_congr rfl
          intro n hn
          have : n ≠ 0 := by
            have hh := (Finset.mem_Ioc.mp hn).1
            omega
          simp [g, this]
      let F : ℕ → ℂ := fun n => (n:ℂ)^(-s) * χ (n : ZMod q)
      let S : ℕ → ℂ := fun N =>
        ∑ n ∈ Finset.range (N+1), if n = 0 then (0:ℂ) else F n
      let C : ℂ := ∑ n ∈ Finset.range (⌊Y⌋₊+1), if n = 0 then (0:ℂ) else F n
      let D : ℝ → ℂ := fun u => ((-s)*(u:ℂ)^(-s-1)) * A u
      let ybd : ℂ := (Y:ℂ)^(-s) * A Y
      have hLs : Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N, if n = 0 then (0:ℂ) else F n)
          Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
        convert hLseries q χ s hs using 1
        ext N
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hzero : n = 0
        · simp [F, hzero]
        · simp only [if_neg hzero, F]
          ring
      have hS : Filter.Tendsto S Filter.atTop
          (nhds (DirichletCharacter.LFunction χ s)) := by
        simpa only [S, Function.comp_def] using hLs.comp (Filter.tendsto_add_atTop_nat 1)
      have hB : Filter.Tendsto
          (fun N : ℕ => (N:ℂ)^(-s) * A (N:ℝ))
          Filter.atTop (nhds (0:ℂ)) := by
        simpa only [A, Nat.floor_natCast] using hBoundary q χ s hs
      have hInt : MeasureTheory.IntegrableOn D (Set.Ioi Y) := by
        have h := hAint q χ Y s (by linarith) hs
        change MeasureTheory.IntegrableOn
          (fun u : ℝ => A u * (u:ℂ)^(-s-1)) (Set.Ioi Y) at h
        exact hDint A Y s h
      have hIlim : Filter.Tendsto
          (fun N : ℕ => ∫ u : ℝ in Set.Ioc Y (N:ℝ), D u)
          Filter.atTop (nhds (∫ u : ℝ in Set.Ioi Y, D u)) :=
        hIntegralLim D Y hInt
      have hFin : ∀ᶠ (N : ℕ) in Filter.atTop,
          S N = C + (N:ℂ)^(-s) * A (N:ℝ) - ybd -
            (∫ u : ℝ in Set.Ioc Y (N:ℝ), D u) := by
        filter_upwards [Filter.eventually_ge_atTop ⌊Y⌋₊,
          (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
            (Filter.eventually_ge_atTop Y)] with N hN hNY
        have hAb := habel q χ Y (N:ℝ) s hY hNY
        simp only [Nat.floor_natCast] at hAb
        have hsp := hSplit F ⌊Y⌋₊ N hN
        have hsp' : (∑ n ∈ Finset.Ioc ⌊Y⌋₊ N, F n) = S N - C := by
          simpa only [S, C] using hsp
        have hAb' : (∑ n ∈ Finset.Ioc ⌊Y⌋₊ N, F n) =
            (N:ℂ)^(-s) * A (N:ℝ) - ybd -
              (∫ u : ℝ in Set.Ioc Y (N:ℝ), D u) := by
          simpa only [F, A, D, ybd, Nat.floor_natCast, Complex.ofReal_natCast] using hAb
        calc
          S N = (S N - C) + C := by ring
          _ = (∑ n ∈ Finset.Ioc ⌊Y⌋₊ N, F n) + C := by rw [hsp']
          _ = ((N:ℂ)^(-s) * A (N:ℝ) - ybd -
              (∫ u : ℝ in Set.Ioc Y (N:ℝ), D u)) + C := by rw [hAb']
          _ = C + (N:ℂ)^(-s) * A (N:ℝ) - ybd -
              (∫ u : ℝ in Set.Ioc Y (N:ℝ), D u) := by ring
      have hConst : Filter.Tendsto (fun _ : ℕ => C)
          Filter.atTop (nhds C) := tendsto_const_nhds
      have hR : Filter.Tendsto
          (fun N : ℕ => C + (N:ℂ)^(-s) * A (N:ℝ) - ybd -
            (∫ u : ℝ in Set.Ioc Y (N:ℝ), D u))
          Filter.atTop (nhds (C - ybd - ∫ u : ℝ in Set.Ioi Y, D u)) := by
        simpa only [add_zero] using ((hConst.add hB).sub_const ybd).sub hIlim
      have hLim : Filter.Tendsto S Filter.atTop
          (nhds (C - ybd - ∫ u : ℝ in Set.Ioi Y, D u)) :=
        hR.congr' (hFin.mono (fun N h => h.symm))
      have heq : DirichletCharacter.LFunction χ s =
          C - ybd - ∫ u : ℝ in Set.Ioi Y, D u :=
        tendsto_nhds_unique hS hLim
      simpa only [C, ybd, D, F] using heq
  have hIntegrable : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Y : ℝ) (s : ℂ), 0 < Y → 1 < s.re →
      MeasureTheory.IntegrableOn
        (fun u : ℝ => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) *
          (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
      intro q inst χ Y s hY hs
      have hsum : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q)‖ ≤ (n:ℝ) := by
        intro n
        calc
          _ ≤ ∑ i ∈ Finset.range n, ‖χ ((i+1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range n, (1:ℝ) := Finset.sum_le_sum (fun i hi => χ.norm_le_one _)
          _ = (n:ℝ) := by simp
      have hg : MeasureTheory.IntegrableOn (fun u : ℝ => u^(-s.re)) (Set.Ioi Y) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hY
      have hm : Measurable
          (fun u : ℝ => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) * (u:ℂ)^(-s-1)) := by
        have hprefix : Measurable
          (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q)) :=
          (continuous_of_discreteTopology : Continuous (fun n : ℕ =>
             ∑ i ∈ Finset.range n, χ ((i+1 : ℕ) : ZMod q))).measurable
        exact (hprefix.comp Nat.measurable_floor).mul (by fun_prop)
      apply hg.mono' hm.aestronglyMeasurable
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hY.trans hu
      have hn : ‖∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)‖ ≤ u := by
        exact (hsum ⌊u⌋₊).trans (Nat.floor_le hu0.le)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      calc
        _ ≤ u * u^(-s.re-1) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hu0.le _)
        _ = u^(-s.re) := by
          rw [show -s.re = 1 + (-s.re-1) by ring, Real.rpow_add hu0]
          simp [mul_comm]
  have hNegDeriv : ∀ (A : ℝ → ℂ) (Y : ℝ) (s : ℂ),
      MeasureTheory.IntegrableOn (fun u : ℝ => A u * (u:ℂ)^(-s-1)) (Set.Ioi Y) →
      -(∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u) =
        s * ∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1) := by
      intro A Y s h
      have hint : (∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u) =
          (-s) * ∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1) := by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        ring
      rw [hint]
      ring
  have hSplit : ∀ (A : ℝ → ℂ) (Y : ℝ) (s c : ℂ),
      0 < Y → 1 < s.re →
      MeasureTheory.IntegrableOn (fun u : ℝ => A u * (u:ℂ)^(-s-1)) (Set.Ioi Y) →
      let B : ℝ → ℂ := fun u => A u - (u:ℂ)*c;
      -(Y:ℂ)^(-s) * A Y +
        s * (∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1)) =
      c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
        s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)) := by
      intro A Y s c hY hs hA
      let B : ℝ → ℂ := fun u => A u - (u:ℂ)*c
      have hPoint : ∀ (u : ℝ) (s c : ℂ), 0 < u →
          ((u:ℂ)*c) * (u:ℂ)^(-s-1) = c * (u:ℂ)^(-s) := by
          intro u s c hu
          have hne : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
          have hpow : (u:ℂ) * (u:ℂ)^(-s-1) = (u:ℂ)^(-s) := by
            calc
              (u:ℂ) * (u:ℂ)^(-s-1) =
                  (u:ℂ)^(1:ℂ) * (u:ℂ)^(-s-1) := by simp
              _ = (u:ℂ)^((1:ℂ)+(-s-1)) := (Complex.cpow_add _ _ hne).symm
              _ = (u:ℂ)^(-s) := by congr 1 <;> ring
          calc
            ((u:ℂ)*c) * (u:ℂ)^(-s-1) = c * ((u:ℂ)*(u:ℂ)^(-s-1)) := by ring
            _ = c * (u:ℂ)^(-s) := by rw [hpow]
      have hIntpow : ∀ (Y : ℝ) (s : ℂ), 0 < Y → 1 < s.re →
          (∫ u : ℝ in Set.Ioi Y, (u:ℂ)^(-s)) = (Y:ℂ)^(1-s)/(s-1) := by
          intro Y s hY hs
          have hpow : (-s).re < -1 := by simp; linarith
          rw [integral_Ioi_cpow_of_lt hpow hY]
          have he : -s + (1:ℂ) = 1 - s := by ring
          rw [he]
          have hsne : s ≠ 1 := by
            intro heq
            rw [heq] at hs
            norm_num at hs
          have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
          have h2 : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr hsne.symm
          field_simp
          ring
      have hpow : MeasureTheory.IntegrableOn
          (fun u : ℝ => (u:ℂ)^(-s)) (Set.Ioi Y) :=
        integrableOn_Ioi_cpow_of_lt (by simp; linarith) hY
      have hmean : MeasureTheory.IntegrableOn
          (fun u : ℝ => ((u:ℂ)*c) * (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
        have hi : MeasureTheory.IntegrableOn
            (fun u : ℝ => c * (u:ℂ)^(-s)) (Set.Ioi Y) :=
          hpow.const_mul c
        exact hi.congr_fun
          (fun u hu => (hPoint u s c (hY.trans hu)).symm) measurableSet_Ioi
      have hB : MeasureTheory.IntegrableOn
          (fun u : ℝ => B u * (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
        have hd : MeasureTheory.IntegrableOn
            (fun u : ℝ => A u * (u:ℂ)^(-s-1) -
               ((u:ℂ)*c) * (u:ℂ)^(-s-1)) (Set.Ioi Y) :=
          hA.sub hmean
        exact hd.congr_fun (fun u hu => by dsimp [B]; ring) measurableSet_Ioi
      have hMeanIntegral :
          (∫ u : ℝ in Set.Ioi Y, ((u:ℂ)*c) * (u:ℂ)^(-s-1)) =
          c * (Y:ℂ)^(1-s)/(s-1) := by
        calc
          _ = ∫ u : ℝ in Set.Ioi Y, c * (u:ℂ)^(-s) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            exact hPoint u s c (hY.trans hu)
          _ = c * (∫ u : ℝ in Set.Ioi Y, (u:ℂ)^(-s)) := by
            rw [MeasureTheory.integral_const_mul]
          _ = c * (Y:ℂ)^(1-s)/(s-1) := by
            rw [hIntpow Y s hY hs]
            ring
      have hIntegral :
          (∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1)) =
          (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)) +
            c * (Y:ℂ)^(1-s)/(s-1) := by
        calc
          _ = ∫ u : ℝ in Set.Ioi Y,
              B u * (u:ℂ)^(-s-1) + ((u:ℂ)*c) * (u:ℂ)^(-s-1) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            dsimp [B]
            ring
          _ = (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)) +
              (∫ u : ℝ in Set.Ioi Y, ((u:ℂ)*c) * (u:ℂ)^(-s-1)) := by
            rw [MeasureTheory.integral_add hB hmean]
          _ = _ := by rw [hMeanIntegral]
      have hY0 : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
      have hYpow : (Y:ℂ)^(-s) * (Y:ℂ) = (Y:ℂ)^(1-s) := by
        calc
          _ = (Y:ℂ)^(-s) * (Y:ℂ)^(1:ℂ) := by simp
          _ = (Y:ℂ)^(-s+1) := (Complex.cpow_add _ _ hY0).symm
          _ = (Y:ℂ)^(1-s) := by congr 1 <;> ring
      have hBoundary : (Y:ℂ)^(-s) * A Y =
          (Y:ℂ)^(-s) * B Y + c * (Y:ℂ)^(1-s) := by
        calc
          _ = (Y:ℂ)^(-s) * (B Y + (Y:ℂ)*c) := by dsimp [B]; ring
          _ = (Y:ℂ)^(-s) * B Y + c * ((Y:ℂ)^(-s) * (Y:ℂ)) := by ring
          _ = _ := by rw [hYpow]
      have hsne : s ≠ 1 := by
        intro heq
        rw [heq] at hs
        norm_num at hs
      have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
      change -(Y:ℂ)^(-s) * A Y +
        s * (∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1)) =
        c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
        s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1))
      rw [hIntegral]
      have hNeg : -(Y:ℂ)^(-s) * A Y =
          -((Y:ℂ)^(-s)*B Y + c*(Y:ℂ)^(1-s)) := by
        linear_combination -hBoundary
      rw [hNeg]
      field_simp
      ring
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ)
  let A : ℝ → ℂ := fun u => ∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)
  let B : ℝ → ℂ := fun u => A u - (u:ℂ)*c
  have hInt : MeasureTheory.IntegrableOn
      (fun u : ℝ => A u * (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
    simpa only [A] using hIntegrable q χ Y s (by linarith) hs
  have hId : DirichletCharacter.LFunction χ s =
      (∑ n ∈ Finset.range (⌊Y⌋₊+1),
        if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) -
      (Y:ℂ)^(-s) * A Y -
      (∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u) := by
    simpa only [A] using hIdentity q χ Y s hY hs
  have hN := hNegDeriv A Y s hInt
  have hS := hSplit A Y s c (by linarith : 0 < Y) hs hInt
  change -(Y:ℂ)^(-s) * A Y +
      s * (∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1)) =
      c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
      s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)) at hS
  let S : ℂ := ∑ n ∈ Finset.range (⌊Y⌋₊+1),
      if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)
  change DirichletCharacter.LFunction χ s =
    S + c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
      s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1))
  change DirichletCharacter.LFunction χ s =
      S - (Y:ℂ)^(-s) * A Y -
      (∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u) at hId
  calc
    DirichletCharacter.LFunction χ s =
        S - (Y:ℂ)^(-s) * A Y -
        (∫ u : ℝ in Set.Ioi Y, ((-s)*(u:ℂ)^(-s-1)) * A u) := hId
    _ = S + (-(Y:ℂ)^(-s) * A Y +
        s * (∫ u : ℝ in Set.Ioi Y, A u * (u:ℂ)^(-s-1))) := by
          linear_combination hN
    _ = S + (c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
        s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1))) := by rw [hS]
    _ = _ := by ring
end Green64Analytic.LongPrime

end

/-! ## G1DiskGeometry -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem disk_source_geometry :
∀ (L δ v : ℝ) (w : ℂ),
  2 ≤ L → 0 < δ → δ ≤ 1/100 →
  20 ≤ |v| → |v| ≤ 2*(Real.exp L)^2 →
  ‖w - (((1+δ:ℝ):ℝ):ℂ) - (v:ℂ)*Complex.I‖ ≤ 8*δ →
  1-8*δ ≤ w.re ∧ (1:ℝ)/2 ≤ w.re ∧ w ≠ 1 ∧
  1 ≤ ‖w-1‖ ∧ ‖w‖ ≤ 5*(Real.exp L)^2 :=
by
  intro L δ v w hL hδ hδmax hvlo hvhi hball
  let center : ℂ := ((1+δ:ℝ):ℂ) + (v:ℂ)*Complex.I
  have hd : ‖w-center‖ ≤ 8*δ := by simpa only [center, sub_add_eq_sub_sub] using hball
  have hre : |w.re-(1+δ)| ≤ 8*δ := by
    calc
      _ = |(w-center).re| := by simp [center, Complex.sub_re, Complex.add_re]
      _ ≤ ‖w-center‖ := Complex.abs_re_le_norm _
      _ ≤ 8*δ := hd
  have him : |w.im-v| ≤ 8*δ := by
    calc
      _ = |(w-center).im| := by simp [center, Complex.sub_im, Complex.add_im]
      _ ≤ ‖w-center‖ := Complex.abs_im_le_norm _
      _ ≤ 8*δ := hd
  have hx : 1 ≤ (Real.exp L)^2 := by
    have hx0 : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg (Real.exp L)]
  have hrelo : 1-8*δ ≤ w.re := by
    have h := (abs_le.mp hre).1
    linarith
  have hrehalf : (1:ℝ)/2 ≤ w.re := by linarith
  have himlo : 1 ≤ |w.im| := by
    have htriangle : |v| ≤ |w.im| + |w.im-v| := by
      calc
        |v| = |w.im - (w.im-v)| := by ring
        _ ≤ |w.im|+|w.im-v| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le w.im 0 (w.im-v)
    linarith
  have hnormsub : 1 ≤ ‖w-1‖ := by
    have h := Complex.abs_im_le_norm (w-1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact himlo.trans h
  have hne : w ≠ 1 := by
    intro heq
    subst w
    norm_num at hnormsub
  have hcenter : ‖center‖ ≤ (1+δ)+|v| := by
    calc
      _ ≤ ‖((1+δ:ℝ):ℂ)‖ + ‖(v:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = (1+δ)+|v| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1+δ)]
  have hnorm : ‖w‖ ≤ 5*(Real.exp L)^2 := by
    calc
      ‖w‖ = ‖(w-center)+center‖ := by congr 1 <;> ring
      _ ≤ ‖w-center‖+‖center‖ := norm_add_le _ _
      _ ≤ 8*δ + ((1+δ)+|v|) := add_le_add hd hcenter
      _ ≤ 5*(Real.exp L)^2 := by linarith
  exact ⟨hrelo,hrehalf,hne,hnormsub,hnorm⟩
end Green64Analytic.LongPrime

end

/-! ## G1DiskLogNumeric -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem disk_norm_to_log :
∀ (L δ a : ℝ), 2 ≤ L → 0 ≤ δ → 0 ≤ a →
  a ≤ 100*L*Real.exp (40*δ*L) →
  Real.log a ≤ 50*(Real.log L + δ*L) :=
by
  intro L δ a hL hδ ha hBound
  have hLpos : 0 < L := by linarith
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hδL : 0 ≤ δ*L := mul_nonneg hδ hLpos.le
  have h100 : Real.log (100:ℝ) ≤ 7*Real.log L := by
    have he : (100:ℝ) ≤ L^7 := by
      calc
        (100:ℝ) ≤ (2:ℝ)^7 := by norm_num
        _ ≤ L^7 := by gcongr
    calc
      Real.log (100:ℝ) ≤ Real.log (L^7) :=
        Real.log_le_log (by norm_num) he
      _ = 7*Real.log L := by rw [Real.log_pow]; norm_num
  have hUpper : Real.log a ≤ Real.log (100*L*Real.exp (40*δ*L)) := by
    by_cases ha0 : a = 0
    · subst a
      simp
      have hp : 1 ≤ 100*L*Real.exp (40*δ*L) := by
        have hexp : 1 ≤ Real.exp (40*δ*L) := Real.one_le_exp (by positivity)
        nlinarith
      exact Real.log_nonneg hp
    · exact Real.log_le_log (lt_of_le_of_ne ha (Ne.symm ha0)) hBound
  have hFormula : Real.log (100*L*Real.exp (40*δ*L)) =
      Real.log 100 + Real.log L + 40*δ*L := by
    rw [Real.log_mul (by positivity : (100*L:ℝ) ≠ 0)
      (Real.exp_ne_zero _), Real.log_mul (by norm_num : (100:ℝ) ≠ 0)
      (ne_of_gt hLpos), Real.log_exp]
  rw [hFormula] at hUpper
  calc
    Real.log a ≤ Real.log (100:ℝ) + Real.log L + 40*δ*L := hUpper
    _ ≤ 7*Real.log L + Real.log L + 40*δ*L := by linarith
    _ ≤ 50*(Real.log L + δ*L) := by nlinarith
end Green64Analytic.LongPrime

end

/-! ## G1DiskNumeric -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem disk_numeric_bound :
∀ (L δ σ q H : ℝ), 2 ≤ L → 0 ≤ δ →
  1-8*δ ≤ σ → 0 ≤ q → q ≤ Real.exp L →
  0 ≤ H → H ≤ 5*Real.exp (2*L) →
  (1+5*L)*Real.exp (40*δ*L) +
    Real.exp (5*L*(1-σ)) +
    4*q*(1+H)*Real.exp (-5*L*σ) ≤
  100*L*Real.exp (40*δ*L) :=
by
  intro L δ σ q H hL hδ hσ hq hqtop hH hHtop
  let M : ℝ := Real.exp (40*δ*L)
  have hL0 : 0 ≤ L := by linarith
  have h5L : 0 ≤ 5*L := by positivity
  have hx : 1 ≤ Real.exp (2*L) := Real.one_le_exp (by linarith)
  have h1H : 1+H ≤ 6*Real.exp (2*L) := by linarith
  have hσbound : 5*L*(1-σ) ≤ 40*δ*L := by
    have hh := mul_le_mul_of_nonneg_left hσ h5L
    nlinarith
  have hσbound2 : -5*L*σ ≤ -5*L + 40*δ*L := by nlinarith [hσbound]
  have hPole : Real.exp (5*L*(1-σ)) ≤ M :=
    Real.exp_le_exp.mpr hσbound
  have hProd : 4*q*(1+H) ≤ 24*Real.exp (3*L) := by
    calc
      _ ≤ 4*(Real.exp L)*(1+H) := by gcongr
      _ ≤ 4*(Real.exp L)*(6*Real.exp (2*L)) := by gcongr
      _ = 24*(Real.exp L * Real.exp (2*L)) := by ring
      _ = 24*Real.exp (3*L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hR : 4*q*(1+H)*Real.exp (-5*L*σ) ≤ 24*M := by
    calc
      _ ≤ (24*Real.exp (3*L))*Real.exp (-5*L*σ) :=
        mul_le_mul_of_nonneg_right hProd (Real.exp_nonneg _)
      _ ≤ (24*Real.exp (3*L))*Real.exp (-5*L+40*δ*L) := by
        gcongr
      _ = 24*Real.exp (-2*L+40*δ*L) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ ≤ 24*M := by
        dsimp [M]
        gcongr
        linarith
  have hm : 0 ≤ M := Real.exp_nonneg _
  have hmBound : (1+5*L)*M + M + 24*M ≤ 100*L*M := by
    have hlc : 26+5*L ≤ 100*L := by linarith
    nlinarith
  change (1+5*L)*M + Real.exp (5*L*(1-σ)) +
    4*q*(1+H)*Real.exp (-5*L*σ) ≤ 100*L*M
  exact (add_le_add (add_le_add le_rfl hPole) hR).trans hmBound
end Green64Analytic.LongPrime

end

/-! ## G1Error -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem explicit_character_remainder :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Y : ℝ),
let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ):ZMod q))/(q:ℂ)
let B : ℝ → ℂ := fun u => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ):ZMod q)) - (u:ℂ)*c
let E : ℂ → ℂ := fun s => -B Y * (Y:ℂ)^(-s) +
  s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)
0 < Y →
DifferentiableOn ℂ E {s : ℂ | 0 < s.re} ∧
∀ s : ℂ, (1:ℝ)/2 ≤ s.re → ‖E s‖ ≤ 4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) :=
by
  have disc :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ):ZMod q))/(q:ℂ)
    ‖c‖ ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u →
      ‖(∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ):ZMod q)) - (u:ℂ)*c‖ ≤ 2*(q:ℝ) := by
    have periodic : ∀ (q : ℕ), 0 < q → ∀ (a : ℕ → ℂ), (∀ n, a (n+q) = a n) →
  (∀ n, ‖a n‖ ≤ 1) →
  let c : ℂ := (∑ i ∈ Finset.range q, a (i+1))/(q:ℂ)
  ‖c‖ ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u →
    ‖(∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (u:ℂ)*c‖ ≤ 2*(q:ℝ) := by
      have nat_bound : ∀ (q : ℕ), 0 < q → ∀ (a : ℕ → ℂ), (∀ n, a (n+q) = a n) →
    (∀ n, ‖a n‖ ≤ 1) →
    let c : ℂ := (∑ i ∈ Finset.range q, a (i+1))/(q:ℂ)
    ‖c‖ ≤ 1 ∧ ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, a (i+1)) - (n:ℂ)*c‖ ≤ 2*(n%q:ℕ) := by
        have block : ∀ (q : ℕ) (a : ℕ → ℂ), (∀ n, a (n+q) = a n) → ∀ m r : ℕ,
        (∑ i ∈ Finset.range (m*q+r), a (i+1)) = (m:ℂ)*(∑ i ∈ Finset.range q, a (i+1)) + ∑ i ∈ Finset.range r, a (i+1) := by
          intro q a hp
          have shift : ∀ m n : ℕ, a (m*q+n) = a n := by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
              intro n
              have he : (m+1)*q+n = (m*q+n)+q := by ring
              rw [he, hp, ih]
          have block : ∀ m : ℕ, (∑ i ∈ Finset.range (m*q), a (i+1)) =
              (m:ℂ)*(∑ i ∈ Finset.range q, a (i+1)) := by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
              rw [Nat.succ_mul, Finset.sum_range_add, ih]
              have he : (∑ i ∈ Finset.range q, a (m*q+i+1)) =
                  ∑ i ∈ Finset.range q, a (i+1) := by
                apply Finset.sum_congr rfl
                intro i hi
                simpa only [Nat.add_assoc] using shift m (i+1)
              rw [he]
              push_cast
              ring
          intro m r
          rw [Finset.sum_range_add, block]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [Nat.add_assoc] using shift m (i+1)
        intro q hq a hp hb c
        have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
        have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
        have sum_bound (r : ℕ) : ‖∑ i ∈ Finset.range r, a (i+1)‖ ≤ (r:ℝ) := by
          calc
            _ ≤ ∑ i ∈ Finset.range r, ‖a (i+1)‖ := norm_sum_le _ _
            _ ≤ ∑ _i ∈ Finset.range r, (1:ℝ) := Finset.sum_le_sum fun i hi => hb (i+1)
            _ = (r:ℝ) := by simp
        have hc : ‖c‖ ≤ 1 := by
          dsimp [c]
          rw [norm_div, Complex.norm_natCast]
          exact (div_le_one hqr).mpr (sum_bound q)
        refine ⟨hc, ?_⟩
        intro n
        have hn : n / q * q + n % q = n := by simpa only [Nat.mul_comm] using Nat.div_add_mod n q
        have hncast : (n:ℂ) = (n/q:ℕ)*(q:ℂ)+(n%q:ℕ) := by
          exact_mod_cast hn.symm
        have hs := block q a hp (n/q) (n%q)
        rw [hn] at hs
        have hid : (∑ i ∈ Finset.range n, a (i+1)) - (n:ℂ)*c =
            (∑ i ∈ Finset.range (n%q), a (i+1)) - (n%q:ℕ)*c := by
          rw [hs, hncast]
          dsimp [c]
          field_simp
          <;> ring
        rw [hid]
        calc
          _ ≤ ‖∑ i ∈ Finset.range (n%q), a (i+1)‖ + ‖(n%q:ℕ)*c‖ := norm_sub_le _ _
          _ ≤ (n%q:ℕ) + (n%q:ℕ) := by
            rw [norm_mul, Complex.norm_natCast]
            gcongr
            exact sum_bound _
            simpa using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (n%q))
          _ = 2*(n%q:ℕ) := by ring
      intro q hq a hp hb c
      obtain ⟨hc, hn⟩ := nat_bound q hq a hp hb
      change ‖c‖ ≤ 1 at hc
      refine ⟨hc, ?_⟩
      intro u hu
      have hf : (⌊u⌋₊:ℝ) ≤ u := Nat.floor_le hu
      have hg : u < (⌊u⌋₊:ℝ)+1 := Nat.lt_floor_add_one u
      have hm : ⌊u⌋₊%q + 1 ≤ q := Nat.mod_lt _ hq
      have hmr : (⌊u⌋₊%q:ℕ)+1 ≤ (q:ℝ) := by exact_mod_cast hm
      have he : (∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (u:ℂ)*c =
        ((∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (⌊u⌋₊:ℂ)*c) -
          ((u:ℂ)-(⌊u⌋₊:ℂ))*c := by ring
      rw [he]
      have hnorm : ‖((u:ℂ)-(⌊u⌋₊:ℂ))*c‖ ≤ u-(⌊u⌋₊:ℝ) := by
        rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hf)]
        exact mul_le_of_le_one_right (sub_nonneg.mpr hf) hc
      calc
        _ ≤ ‖(∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (⌊u⌋₊:ℂ)*c‖ +
          ‖((u:ℂ)-(⌊u⌋₊:ℂ))*c‖ := norm_sub_le _ _
        _ ≤ 2*(⌊u⌋₊%q:ℕ) + (u-(⌊u⌋₊:ℝ)) := add_le_add (hn _) hnorm
        _ ≤ 2*(q:ℝ) := by linarith
    intro q hq χ
    apply periodic q (Nat.pos_of_ne_zero (NeZero.ne q)) (fun n => χ (n:ZMod q))
    · intro n
      simp
    · intro n
      exact χ.norm_le_one (n:ZMod q)
  have tail_holo :
    ∀ (B : ℝ → ℂ) (Y b : ℝ), 0 < Y → 0 ≤ b →
    Measurable B → (∀ u : ℝ, Y < u → ‖B u‖ ≤ b) →
    DifferentiableOn ℂ (fun s : ℂ => ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1))
      {s : ℂ | 0 < s.re} := by
    intro B Y b hY hb hB hbound
    let g : ℝ → ℂ := (Set.Ioi Y).indicator B
    have hg : Measurable g := hB.indicator measurableSet_Ioi
    have hgb (u : ℝ) : ‖g u‖ ≤ b := by
      by_cases hu : Y < u
      · simpa [g, Set.indicator_apply, hu] using hbound u hu
      · simp [g, Set.indicator_apply, hu, hb]
    have hloc : MeasureTheory.LocallyIntegrable g :=
      (MeasureTheory.locallyIntegrable_const (b:ℝ)).mono hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs, abs_of_nonneg hb] using hgb u)
    have htop : Asymptotics.IsBigO Filter.atTop g (fun u : ℝ => u^(-(0:ℝ))) := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨b, Filter.Eventually.of_forall ?_⟩
      intro u
      simpa using hgb u
    have heq (s : ℂ) : mellin g (-s) = ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1) := by
      unfold mellin
      simp only [g, ← Set.indicator_smul]
      rw [MeasureTheory.integral_indicator measurableSet_Ioi,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ioi]
      have hset : Set.Ioi Y ∩ Set.Ioi (0:ℝ) = Set.Ioi Y :=
        Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hY.le)
      rw [hset]
      simp only [smul_eq_mul, mul_comm]
    intro s hs
    change 0 < s.re at hs
    have hbot : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Set.Ioi 0)) g
        (fun u : ℝ => u^(-((-s).re-1))) := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨0, ?_⟩
      have he : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < Y :=
        (gt_mem_nhds hY).filter_mono nhdsWithin_le_nhds
      filter_upwards [he] with u hu
      simp [g, Set.indicator_apply, not_lt_of_ge hu.le]
    have hd : DifferentiableAt ℂ (mellin g) (-s) :=
      mellin_differentiableAt_of_isBigO_rpow (hloc.locallyIntegrableOn _)
        htop (by simpa using neg_lt_zero.mpr hs) hbot (by linarith)
    have hh : DifferentiableAt ℂ (fun z : ℂ => mellin g (-z)) s :=
      hd.comp s (differentiableAt_id.neg)
    simpa only [heq] using hh.differentiableWithinAt
  have err_bound :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Y : ℝ) (s : ℂ),
    let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ):ZMod q))/(q:ℂ)
    let B : ℝ → ℂ := fun u => (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ):ZMod q)) - (u:ℂ)*c
    0 < Y → (1:ℝ)/2 ≤ s.re →
    MeasureTheory.IntegrableOn (fun u : ℝ => B u * (u:ℂ)^(-s-1)) (Set.Ioi Y) ∧
    ‖-B Y * (Y:ℂ)^(-s) + s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)‖
      ≤ 4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) := by
    have disc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ):ZMod q))/(q:ℂ)
  ‖c‖ ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u →
    ‖(∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ):ZMod q)) - (u:ℂ)*c‖ ≤ 2*(q:ℝ) := by
      have periodic : ∀ (q : ℕ), 0 < q → ∀ (a : ℕ → ℂ), (∀ n, a (n+q) = a n) →
    (∀ n, ‖a n‖ ≤ 1) →
    let c : ℂ := (∑ i ∈ Finset.range q, a (i+1))/(q:ℂ)
    ‖c‖ ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u →
      ‖(∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (u:ℂ)*c‖ ≤ 2*(q:ℝ) := by
        have nat_bound : ∀ (q : ℕ), 0 < q → ∀ (a : ℕ → ℂ), (∀ n, a (n+q) = a n) →
      (∀ n, ‖a n‖ ≤ 1) →
      let c : ℂ := (∑ i ∈ Finset.range q, a (i+1))/(q:ℂ)
      ‖c‖ ≤ 1 ∧ ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, a (i+1)) - (n:ℂ)*c‖ ≤ 2*(n%q:ℕ) := by
          have block : ∀ (q : ℕ) (a : ℕ → ℂ), (∀ n, a (n+q) = a n) → ∀ m r : ℕ,
          (∑ i ∈ Finset.range (m*q+r), a (i+1)) = (m:ℂ)*(∑ i ∈ Finset.range q, a (i+1)) + ∑ i ∈ Finset.range r, a (i+1) := by
            intro q a hp
            have shift : ∀ m n : ℕ, a (m*q+n) = a n := by
              intro m
              induction m with
              | zero => simp
              | succ m ih =>
                intro n
                have he : (m+1)*q+n = (m*q+n)+q := by ring
                rw [he, hp, ih]
            have block : ∀ m : ℕ, (∑ i ∈ Finset.range (m*q), a (i+1)) =
                (m:ℂ)*(∑ i ∈ Finset.range q, a (i+1)) := by
              intro m
              induction m with
              | zero => simp
              | succ m ih =>
                rw [Nat.succ_mul, Finset.sum_range_add, ih]
                have he : (∑ i ∈ Finset.range q, a (m*q+i+1)) =
                    ∑ i ∈ Finset.range q, a (i+1) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  simpa only [Nat.add_assoc] using shift m (i+1)
                rw [he]
                push_cast
                ring
            intro m r
            rw [Finset.sum_range_add, block]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            simpa only [Nat.add_assoc] using shift m (i+1)
          intro q hq a hp hb c
          have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
          have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
          have sum_bound (r : ℕ) : ‖∑ i ∈ Finset.range r, a (i+1)‖ ≤ (r:ℝ) := by
            calc
              _ ≤ ∑ i ∈ Finset.range r, ‖a (i+1)‖ := norm_sum_le _ _
              _ ≤ ∑ _i ∈ Finset.range r, (1:ℝ) := Finset.sum_le_sum fun i hi => hb (i+1)
              _ = (r:ℝ) := by simp
          have hc : ‖c‖ ≤ 1 := by
            dsimp [c]
            rw [norm_div, Complex.norm_natCast]
            exact (div_le_one hqr).mpr (sum_bound q)
          refine ⟨hc, ?_⟩
          intro n
          have hn : n / q * q + n % q = n := by simpa only [Nat.mul_comm] using Nat.div_add_mod n q
          have hncast : (n:ℂ) = (n/q:ℕ)*(q:ℂ)+(n%q:ℕ) := by
            exact_mod_cast hn.symm
          have hs := block q a hp (n/q) (n%q)
          rw [hn] at hs
          have hid : (∑ i ∈ Finset.range n, a (i+1)) - (n:ℂ)*c =
              (∑ i ∈ Finset.range (n%q), a (i+1)) - (n%q:ℕ)*c := by
            rw [hs, hncast]
            dsimp [c]
            field_simp
            <;> ring
          rw [hid]
          calc
            _ ≤ ‖∑ i ∈ Finset.range (n%q), a (i+1)‖ + ‖(n%q:ℕ)*c‖ := norm_sub_le _ _
            _ ≤ (n%q:ℕ) + (n%q:ℕ) := by
              rw [norm_mul, Complex.norm_natCast]
              gcongr
              exact sum_bound _
              simpa using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (n%q))
            _ = 2*(n%q:ℕ) := by ring
        intro q hq a hp hb c
        obtain ⟨hc, hn⟩ := nat_bound q hq a hp hb
        change ‖c‖ ≤ 1 at hc
        refine ⟨hc, ?_⟩
        intro u hu
        have hf : (⌊u⌋₊:ℝ) ≤ u := Nat.floor_le hu
        have hg : u < (⌊u⌋₊:ℝ)+1 := Nat.lt_floor_add_one u
        have hm : ⌊u⌋₊%q + 1 ≤ q := Nat.mod_lt _ hq
        have hmr : (⌊u⌋₊%q:ℕ)+1 ≤ (q:ℝ) := by exact_mod_cast hm
        have he : (∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (u:ℂ)*c =
          ((∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (⌊u⌋₊:ℂ)*c) -
            ((u:ℂ)-(⌊u⌋₊:ℂ))*c := by ring
        rw [he]
        have hnorm : ‖((u:ℂ)-(⌊u⌋₊:ℂ))*c‖ ≤ u-(⌊u⌋₊:ℝ) := by
          rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hf)]
          exact mul_le_of_le_one_right (sub_nonneg.mpr hf) hc
        calc
          _ ≤ ‖(∑ i ∈ Finset.range ⌊u⌋₊, a (i+1)) - (⌊u⌋₊:ℂ)*c‖ +
            ‖((u:ℂ)-(⌊u⌋₊:ℂ))*c‖ := norm_sub_le _ _
          _ ≤ 2*(⌊u⌋₊%q:ℕ) + (u-(⌊u⌋₊:ℝ)) := add_le_add (hn _) hnorm
          _ ≤ 2*(q:ℝ) := by linarith
      intro q hq χ
      apply periodic q (Nat.pos_of_ne_zero (NeZero.ne q)) (fun n => χ (n:ZMod q))
      · intro n
        simp
      · intro n
        exact χ.norm_le_one (n:ZMod q)
    have tail : ∀ (B : ℝ → ℂ) (Y b : ℝ) (s : ℂ), 0 < Y → 0 ≤ b → 0 < s.re →
  Measurable B → (∀ u : ℝ, Y < u → ‖B u‖ ≤ b) →
  MeasureTheory.IntegrableOn (fun u : ℝ => B u * (u:ℂ)^(-s-1)) (Set.Ioi Y) ∧
  ‖∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)‖ ≤ b * Y^(-s.re) / s.re := by
      intro B Y b s hY hb hs hB hbound
      have hexp : -s.re-1 < -1 := by linarith
      have hg : MeasureTheory.IntegrableOn (fun u : ℝ => b*u^(-s.re-1)) (Set.Ioi Y) :=
        (integrableOn_Ioi_rpow_of_lt hexp hY).const_mul b
      have hpoint (u : ℝ) (hu : Y < u) :
          ‖B u * (u:ℂ)^(-s-1)‖ ≤ b*u^(-s.re-1) := by
        have hu0 : 0 < u := hY.trans hu
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
        exact mul_le_mul_of_nonneg_right (hbound u hu) (Real.rpow_nonneg hu0.le _)
      have hfmeas : Measurable (fun u : ℝ => B u * (u:ℂ)^(-s-1)) := by
        fun_prop
      have hf : MeasureTheory.IntegrableOn (fun u : ℝ => B u * (u:ℂ)^(-s-1)) (Set.Ioi Y) := by
        apply hg.mono' hfmeas.aestronglyMeasurable
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        exact hpoint u hu
      refine ⟨hf, ?_⟩
      calc
        _ ≤ ∫ u : ℝ in Set.Ioi Y, b*u^(-s.re-1) := by
          apply MeasureTheory.norm_integral_le_of_norm_le hg
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
          exact hpoint u hu
        _ = b * Y^(-s.re) / s.re := by
          rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hexp hY]
          have he : -s.re-1+1 = -s.re := by ring
          rw [he]
          ring
    intro q hq χ Y s c B hY hs
    have hsp : 0 < s.re := by linarith
    have hdisc := (disc q χ).2
    change ∀ u : ℝ, 0 ≤ u → ‖B u‖ ≤ 2*(q:ℝ) at hdisc
    have hm : Measurable B := by
      have hsum : Measurable (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ):ZMod q)) :=
        (continuous_of_discreteTopology : Continuous (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ):ZMod q))).measurable
      exact (hsum.comp Nat.measurable_floor).sub (by fun_prop)
    obtain ⟨hi, hb⟩ := tail B Y (2*(q:ℝ)) s hY (by positivity) hsp hm
      (fun u hu => hdisc u (hY.trans hu).le)
    refine ⟨hi, ?_⟩
    have he : ‖-B Y * (Y:ℂ)^(-s)‖ ≤ 2*(q:ℝ)*Y^(-s.re) := by
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hY, Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (hdisc Y hY.le) (Real.rpow_nonneg hY.le _)
    have hb' : ‖∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)‖ ≤ 4*(q:ℝ)*Y^(-s.re) := by
      apply hb.trans
      apply (div_le_iff₀ hsp).mpr
      have hp : 0 ≤ (q:ℝ)*Y^(-s.re) := by positivity
      nlinarith
    calc
      _ ≤ ‖-B Y * (Y:ℂ)^(-s)‖ + ‖s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)‖ := norm_add_le _ _
      _ ≤ 2*(q:ℝ)*Y^(-s.re) + ‖s‖*(4*(q:ℝ)*Y^(-s.re)) := by
        rw [norm_mul s]
        exact add_le_add he (mul_le_mul_of_nonneg_left hb' (norm_nonneg _))
      _ ≤ 4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) := by
        have hp : 0 ≤ (q:ℝ)*Y^(-s.re) := by positivity
        nlinarith
  intro q hq χ Y c B E hY
  have hdisc := (disc q χ).2
  change ∀ u : ℝ, 0 ≤ u → ‖B u‖ ≤ 2*(q:ℝ) at hdisc
  have hm : Measurable B := by
    have hsum : Measurable (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ):ZMod q)) :=
      (continuous_of_discreteTopology : Continuous (fun n : ℕ => ∑ i ∈ Finset.range n, χ ((i+1 : ℕ):ZMod q))).measurable
    exact (hsum.comp Nat.measurable_floor).sub (by fun_prop)
  have ht := tail_holo B Y (2*(q:ℝ)) hY (by positivity) hm
    (fun u hu => hdisc u (hY.trans hu).le)
  constructor
  · have hYc : (Y:ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    have hp : DifferentiableOn ℂ (fun s : ℂ => -B Y * (Y:ℂ)^(-s)) {s : ℂ | 0 < s.re} := by
      fun_prop (disch := aesop)
    exact hp.add (differentiableOn_id.mul ht)
  · intro s hs
    exact (err_bound q χ Y s hY hs).2
end Green64Analytic.LongPrime

end

/-! ## G1ExpDominates -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem eventual_exp_dominates_rpow :
∀ (C : ℝ), ∃ L₀ : ℝ, 2 ≤ L₀ ∧
  ∀ L : ℝ, L₀ ≤ L → L^C ≤ Real.exp L :=
by
  intro C
  have h := (tendsto_exp_div_rpow_atTop C).eventually
    (Filter.eventually_ge_atTop (1:ℝ))
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 h
  refine ⟨max 2 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLP : 0 < L^C := Real.rpow_pos_of_pos (by linarith) _
  have hratio : 1 ≤ Real.exp L / L^C :=
    hL₁ L ((le_max_right _ _).trans hL)
  have hh := (le_div_iff₀ hLP).mp hratio
  simpa only [one_mul] using hh
end Green64Analytic.LongPrime

end

/-! ## G1FiniteHolomorphic -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem finite_pole_holomorphic :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Y : ℝ) (c : ℂ),
  0 < Y →
  DifferentiableOn ℂ
    (fun s : ℂ => (∑ n ∈ Finset.range (⌊Y⌋₊+1),
      if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) +
      c * (Y:ℂ)^(1-s)/(s-1))
    {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
by
  intro q inst χ Y c hY
  have hYc : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hf : Differentiable ℂ
      (fun s : ℂ => ∑ n ∈ Finset.range (⌊Y⌋₊+1),
        if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) := by
    apply Differentiable.fun_sum
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hd : Differentiable ℂ (fun s : ℂ => (n:ℂ)^(-s)) :=
        (differentiable_id.neg).const_cpow (.inl hnC)
      simpa only [if_neg hn0] using hd.mul_const (χ (n : ZMod q))
  have hp : DifferentiableOn ℂ
      (fun s : ℂ => c * (Y:ℂ)^(1-s)/(s-1))
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    intro s hs
    have hnum : DifferentiableAt ℂ (fun z : ℂ => c * (Y:ℂ)^(1-z)) s := by
      have hexp : DifferentiableAt ℂ (fun z : ℂ => (1:ℂ)-z) s := by fun_prop
      exact (hexp.const_cpow (.inl hYc)).const_mul c
    have hden : DifferentiableAt ℂ (fun z : ℂ => z-1) s :=
      differentiableAt_id.sub_const 1
    exact (hnum.div hden (sub_ne_zero.mpr hs.2)).differentiableWithinAt
  exact hf.differentiableOn.add hp
end Green64Analytic.LongPrime

end

/-! ## G1FiniteSum -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem character_finite_sum_majorant :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ) (e : ℝ), 1 ≤ Y → 0 ≤ e → 1-e ≤ s.re →
  ‖∑ n ∈ Finset.range (⌊Y⌋₊+1),
    if n = 0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)‖ ≤
    (1+Real.log Y) * Y^e :=
by
  intro q inst χ Y s e hY he hσ
  have hY0 : 0 ≤ Y := by linarith
  have hIcc : (∑ n ∈ Finset.range (⌊Y⌋₊+1),
    if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) =
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℂ)^(-s)*χ (n : ZMod q)) := by
    rw [Nat.range_succ_eq_Icc_zero,
      Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊Y⌋₊), Finset.sum_cons]
    simp only [↓reduceIte, zero_add]
    rw [← Finset.Icc_add_one_left_eq_Ioc 0 ⌊Y⌋₊]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    simp [Nat.ne_of_gt hn1]
  rw [hIcc]
  calc
    ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℂ)^(-s)*χ (n : ZMod q)‖ ≤
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ‖(n:ℂ)^(-s)*χ (n : ZMod q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℝ)^(-s.re) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnp : 0 < n := Nat.zero_lt_of_lt hn1
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnp (-s)]
      simp only [Complex.neg_re]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) (χ.norm_le_one _)
    _ ≤ (1+Real.log Y)*Y^e :=
      by
        have hh : ∀ (Y σ e : ℝ), 1 ≤ Y → 0 ≤ e → 1-e ≤ σ →
          (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℝ)^(-σ)) ≤
            (1+Real.log Y) * Y^e := by
          -- The local pinned harmonic proof will be inserted when packaging.
          exact harmonic_power_majorant
        exact hh Y s.re e hY he hσ
end Green64Analytic.LongPrime

end

/-! ## G1Mean -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem character_mean_norm :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
  ‖(∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ)‖ ≤ 1 :=
by
  intro q inst χ
  have hq : 0 < (q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsum : ‖∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q)‖ ≤ (q:ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range q, ‖χ ((i+1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range q, (1:ℝ) :=
        Finset.sum_le_sum (fun i hi => χ.norm_le_one _)
      _ = (q:ℝ) := by simp
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_one hq).mpr hsum
end Green64Analytic.LongPrime

end

/-! ## G1Uniqueness -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem halfplane_analytic_uniqueness :
∀ (f g : ℂ → ℂ),
  DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z ≠ 1} →
  DifferentiableOn ℂ g {z : ℂ | 0 < z.re ∧ z ≠ 1} →
  (∀ z : ℂ, 1 < z.re → f z = g z) →
  ∀ z : ℂ, 0 < z.re → z ≠ 1 → f z = g z :=
by
  intro f g hf hg hSeed z hz hz1
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  have hPre : IsPreconnected {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
      let U : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}
      let R : Set ℂ := {z | 1 < z.re}
      let D : Set ℂ := {z | 0 < z.re ∧ z.im < 0}
      let L : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
      have hU : IsPathConnected U :=
        ((convex_halfSpace_re_gt 0).inter
          (convex_halfSpace_im_gt 0)).isPathConnected
          ⟨1 + Complex.I, by norm_num [U]⟩
      have hR : IsPathConnected R :=
        (convex_halfSpace_re_gt 1).isPathConnected
          ⟨2, by norm_num [R]⟩
      have hD : IsPathConnected D :=
        ((convex_halfSpace_re_gt 0).inter
          (convex_halfSpace_im_lt 0)).isPathConnected
          ⟨1 - Complex.I, by norm_num [D]⟩
      have hL : IsPathConnected L :=
        ((convex_halfSpace_re_gt 0).inter
          (convex_halfSpace_re_lt 1)).isPathConnected
          ⟨1/2, by norm_num [L]⟩
      have hUR : IsPathConnected (U ∪ R) :=
        hU.union hR ⟨2 + Complex.I, by norm_num [U,R]⟩
      have hURD : IsPathConnected ((U ∪ R) ∪ D) :=
        hUR.union hD ⟨2 - Complex.I, by norm_num [U,R,D]⟩
      have hURDL : IsPathConnected (((U ∪ R) ∪ D) ∪ L) :=
        hURD.union hL ⟨(1/2 : ℂ) + Complex.I, by norm_num [U,R,D,L]⟩
      have hEq : (((U ∪ R) ∪ D) ∪ L) = {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
        ext z
        change ((((0 < z.re ∧ 0 < z.im) ∨ 1 < z.re) ∨
          (0 < z.re ∧ z.im < 0)) ∨ (0 < z.re ∧ z.re < 1)) ↔
          (0 < z.re ∧ z ≠ 1)
        constructor
        · intro h
          rcases h with (((⟨hr,hi⟩ | hr)|⟨hr,hi⟩)|⟨hr,hl⟩)
          · exact ⟨hr, by intro hz; subst z; norm_num at hi⟩
          · exact ⟨by linarith, by intro hz; subst z; norm_num at hr⟩
          · exact ⟨hr, by intro hz; subst z; norm_num at hi⟩
          · exact ⟨hr, by intro hz; subst z; norm_num at hl⟩
        · rintro ⟨hr,hn⟩
          rcases lt_trichotomy z.im 0 with hi | hi | hi
          · exact Or.inl (Or.inr ⟨hr,hi⟩)
          · rcases lt_trichotomy z.re 1 with hl | he | hg
            · exact Or.inr ⟨hr,hl⟩
            · exfalso
              apply hn
              apply Complex.ext
              · simpa using he
              · simpa using hi
            · exact Or.inl (Or.inl (Or.inr hg))
          · exact Or.inl (Or.inl (Or.inl ⟨hr,hi⟩))
      rw [← hEq]
      exact hURDL.isConnected.isPreconnected
  have hU : IsPreconnected U := by simpa only [U] using hPre
  have hOp : IsOpen U := by
    change IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z ≠ 1})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hfA : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hOp
  have hgA : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hOp
  have h2 : (2:ℂ) ∈ U := by simp [U]
  have hEvent : f =ᶠ[nhds (2:ℂ)] g := by
    apply Filter.eventually_of_mem ?_
      (fun w hw => hSeed w hw)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact (hfA.eqOn_of_preconnected_of_eventuallyEq hgA hU h2 hEvent) ⟨hz,hz1⟩
end Green64Analytic.LongPrime

end

/-! ## G1Continuation -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem lfunction_periodic_remainder_continued :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (Y : ℝ) (s : ℂ), 1 ≤ Y → 0 < s.re → s ≠ 1 →
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ);
  let B : ℝ → ℂ := fun u =>
    (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) - (u:ℂ)*c;
  DirichletCharacter.LFunction χ s =
    (∑ n ∈ Finset.range (⌊Y⌋₊+1),
      if n=0 then (0:ℂ) else (n:ℂ)^(-s) * χ (n : ZMod q)) +
    c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
    s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1) :=
by
  intro q inst χ Y s hY hs hs1
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ)
  let B : ℝ → ℂ := fun u =>
    (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) - (u:ℂ)*c
  let E : ℂ → ℂ := fun w =>
    -B Y * (Y:ℂ)^(-w) +
    w * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-w-1)
  let S : ℂ → ℂ := fun w =>
    ∑ n ∈ Finset.range (⌊Y⌋₊+1),
      if n=0 then (0:ℂ) else (n:ℂ)^(-w) * χ (n : ZMod q)
  let F : ℂ → ℂ := fun w =>
    S w + c * (Y:ℂ)^(1-w)/(w-1) + E w
  let U : Set ℂ := {w : ℂ | 0 < w.re ∧ w ≠ 1}
  have hYpos : 0 < Y := by linarith
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw.2)).differentiableWithinAt
  have hFinite : DifferentiableOn ℂ
      (fun w : ℂ => S w + c * (Y:ℂ)^(1-w)/(w-1)) U := by
    simpa only [S, U] using finite_pole_holomorphic q χ Y c hYpos
  have hEopen : DifferentiableOn ℂ E {w : ℂ | 0 < w.re} := by
    exact (explicit_character_remainder q χ Y hYpos).1
  have hEon : DifferentiableOn ℂ E U :=
    hEopen.mono (by intro w hw; exact hw.1)
  have hF : DifferentiableOn ℂ F U := hFinite.add hEon
  have hSeed (w : ℂ) (hw : 1 < w.re) :
      DirichletCharacter.LFunction χ w = F w := by
    have h := lfunction_periodic_remainder_convergence q χ Y w hY hw
    change DirichletCharacter.LFunction χ w =
      S w + c * (Y:ℂ)^(1-w)/(w-1) - B Y * (Y:ℂ)^(-w) +
        w * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-w-1)) at h
    change DirichletCharacter.LFunction χ w =
      S w + c * (Y:ℂ)^(1-w)/(w-1) +
        (-B Y * (Y:ℂ)^(-w) +
        w * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-w-1)))
    rw [h]
    ring
  have hMain : DirichletCharacter.LFunction χ s = F s :=
    halfplane_analytic_uniqueness (DirichletCharacter.LFunction χ) F hL hF hSeed s hs hs1
  change DirichletCharacter.LFunction χ s =
    S s + c * (Y:ℂ)^(1-s)/(s-1) - B Y * (Y:ℂ)^(-s) +
      s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1))
  calc
    DirichletCharacter.LFunction χ s = F s := hMain
    _ = _ := by dsimp [F, E]; ring
end Green64Analytic.LongPrime

end

/-! ## G1NormBound -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem lfunction_growth_master :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Y : ℝ)
    (s : ℂ) (e : ℝ), 1 ≤ Y → (1:ℝ)/2 ≤ s.re → s ≠ 1 →
    0 ≤ e → 1-e ≤ s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (1+Real.log Y)*Y^e +
        Y^(1-s.re)/‖s-1‖ +
          4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) :=
by
  intro q inst χ Y s e hY hs hs1 he hσ
  let c : ℂ := (∑ i ∈ Finset.range q, χ ((i+1 : ℕ) : ZMod q))/(q:ℂ)
  let B : ℝ → ℂ := fun u =>
    (∑ i ∈ Finset.range ⌊u⌋₊, χ ((i+1 : ℕ) : ZMod q)) - (u:ℂ)*c
  let S : ℂ := ∑ n ∈ Finset.range (⌊Y⌋₊+1),
    if n=0 then (0:ℂ) else (n:ℂ)^(-s)*χ (n : ZMod q)
  let P : ℂ := c * (Y:ℂ)^(1-s)/(s-1)
  let E : ℂ := -B Y * (Y:ℂ)^(-s) +
    s * ∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)
  have hYpos : 0 < Y := by linarith
  have hE : ‖E‖ ≤ 4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) := by
    have hh := (explicit_character_remainder q χ Y hYpos).2 s hs
    change ‖E‖ ≤ _ at hh
    exact hh
  have hC : ‖c‖ ≤ 1 := character_mean_norm q χ
  have hP : ‖P‖ ≤ Y^(1-s.re)/‖s-1‖ := by
    dsimp only [P]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.sub_re, Complex.one_re]
    have hy : 0 ≤ Y^(1-s.re) := Real.rpow_nonneg hYpos.le _
    have hden : 0 ≤ ‖s-1‖ := norm_nonneg _
    exact (div_le_div_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hy)
      hden)
  have hS : ‖S‖ ≤ (1+Real.log Y)*Y^e :=
    character_finite_sum_majorant q χ Y s e hY he hσ
  have hEq : DirichletCharacter.LFunction χ s = S + P + E := by
    have hh := lfunction_periodic_remainder_continued q χ Y s hY (by linarith : 0 < s.re) hs1
    change DirichletCharacter.LFunction χ s =
      S + P - B Y * (Y:ℂ)^(-s) +
        s * (∫ u : ℝ in Set.Ioi Y, B u * (u:ℂ)^(-s-1)) at hh
    dsimp only [E]
    linear_combination hh
  rw [hEq]
  calc
    ‖S + P + E‖ ≤ ‖S+P‖+‖E‖ := norm_add_le _ _
    _ ≤ (‖S‖+‖P‖)+‖E‖ := add_le_add_left (norm_add_le S P) _
    _ ≤ (1+Real.log Y)*Y^e + Y^(1-s.re)/‖s-1‖ +
        4*(q:ℝ)*(1+‖s‖)*Y^(-s.re) :=
          add_le_add (add_le_add hS hP) hE
end Green64Analytic.LongPrime

end

/-! ## G1DiskNorm -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem disk_source_norm_bound :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
  (L δ v : ℝ) (w : ℂ),
  2 ≤ L → 0 < δ → δ ≤ 1/100 → 20 ≤ |v| →
  |v| ≤ 2*(Real.exp L)^2 →
  ‖w - (((1+δ:ℝ):ℝ):ℂ) - (v:ℂ)*Complex.I‖ ≤ 8*δ →
  (q:ℝ) ≤ Real.exp L →
  ‖DirichletCharacter.LFunction χ w‖ ≤
    100*L*Real.exp (40*δ*L) :=
by
  intro q inst χ L δ v w hL hδ hδmax hvlo hvhi hball hq
  have hg := disk_source_geometry L δ v w hL hδ hδmax hvlo hvhi hball
  have hGeomBound : ‖w‖ ≤ 5*Real.exp (2*L) := by
    have he : (Real.exp L)^2 = Real.exp (2*L) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [he] using hg.2.2.2.2
  let Y : ℝ := Real.exp (5*L)
  have hY : 1 ≤ Y := by
    dsimp [Y]
    exact Real.one_le_exp (by linarith)
  have hLog : Real.log Y = 5*L := by
    dsimp [Y]
    exact Real.log_exp _
  have hPow (a : ℝ) : Y^a = Real.exp (5*L*a) := by
    dsimp [Y]
    rw [Real.rpow_def_of_pos (Real.exp_pos _) a, Real.log_exp]
  have he0 : 0 ≤ 8*δ := by positivity
  have hmajor := lfunction_growth_master q χ Y w (8*δ)
    hY hg.2.1 hg.2.2.1 he0 (by linarith [hg.1])
  have hdenpos : 0 < ‖w-1‖ := by linarith [hg.2.2.2.1]
  have hyPow : 0 ≤ Y^(1-w.re) := Real.rpow_nonneg (by linarith : 0 ≤ Y) _
  have hP : Y^(1-w.re)/‖w-1‖ ≤ Y^(1-w.re) := by
    apply (div_le_iff₀ hdenpos).2
    have hh := mul_le_mul_of_nonneg_left hg.2.2.2.1 hyPow
    simpa only [mul_one] using hh
  have hnum := disk_numeric_bound L δ w.re (q:ℝ) ‖w‖
    hL hδ.le hg.1 (Nat.cast_nonneg q) hq (norm_nonneg _) hGeomBound
  have he8 : 5*L*(8*δ) = 40*δ*L := by ring
  have heNeg : 5*L*(-w.re) = -5*L*w.re := by ring
  calc
    ‖DirichletCharacter.LFunction χ w‖ ≤
      (1+Real.log Y)*Y^(8*δ) +
        Y^(1-w.re)/‖w-1‖ +
          4*(q:ℝ)*(1+‖w‖)*Y^(-w.re) := hmajor
    _ ≤ (1+Real.log Y)*Y^(8*δ) +
        Y^(1-w.re) +
          4*(q:ℝ)*(1+‖w‖)*Y^(-w.re) :=
      add_le_add (add_le_add le_rfl hP) le_rfl
    _ = (1+5*L)*Real.exp (40*δ*L) +
        Real.exp (5*L*(1-w.re)) +
          4*(q:ℝ)*(1+‖w‖)*Real.exp (-5*L*w.re) := by
      rw [hLog, hPow (8*δ), hPow (1-w.re), hPow (-w.re), he8, heNeg]
    _ ≤ 100*L*Real.exp (40*δ*L) := hnum
end Green64Analytic.LongPrime

end

/-! ## G1DiskGrowth -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem disk_source_log_growth :
∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
  (L δ v : ℝ) (w : ℂ),
  2 ≤ L → 0 < δ → δ ≤ 1/100 → 20 ≤ |v| →
  |v| ≤ 2*(Real.exp L)^2 →
  ‖w - (((1+δ:ℝ):ℝ):ℂ) - (v:ℂ)*Complex.I‖ ≤ 8*δ →
  (q:ℝ) ≤ Real.exp L →
  Real.log ‖DirichletCharacter.LFunction χ w‖ ≤
    50*(Real.log L + δ*L) :=
by
  intro q inst χ L δ v w hL hδ hδmax hvlo hvhi hball hq
  have h := disk_source_norm_bound q χ L δ v w
    hL hδ hδmax hvlo hvhi hball hq
  exact disk_norm_to_log L δ ‖DirichletCharacter.LFunction χ w‖
    hL hδ.le (norm_nonneg _) h
end Green64Analytic.LongPrime

end

/-! ## G1SourceUniformGrowth -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem eventual_source_disk_growth :
∀ (C : ℝ), ∃ L₀ : ℝ, 2 ≤ L₀ ∧
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (L δ v : ℝ) (w : ℂ),
  L₀ ≤ L → 0 < δ → δ ≤ 1/100 → 20 ≤ |v| →
  |v| ≤ 2*(Real.exp L)^2 →
  ‖w - (((1+δ:ℝ):ℝ):ℂ) - (v:ℂ)*Complex.I‖ ≤ 8*δ →
  (q:ℝ) ≤ L^C →
  Real.log ‖DirichletCharacter.LFunction χ w‖ ≤
    50*(Real.log L + δ*L) :=
by
  intro C
  obtain ⟨L₀, hL₀, hExp⟩ := eventual_exp_dominates_rpow C
  refine ⟨L₀,hL₀,?_⟩
  intro q inst χ L δ v w hL hδ hδmax hvlo hvhi hball hq
  have h2 : 2 ≤ L := hL₀.trans hL
  have hqexp : (q:ℝ) ≤ Real.exp L := hq.trans (hExp L hL)
  exact disk_source_log_growth q χ L δ v w
    h2 hδ hδmax hvlo hvhi hball hqexp
end Green64Analytic.LongPrime

end

/-! ## G2CenterLog -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_center_log_budget :
∀ (L δ : ℝ), 0 < L → 1 ≤ Real.log L →
  0 < δ → L⁻¹ ≤ δ →
  -50*Real.log L ≤ Real.log δ - Real.log 2 :=
by
  intro L δ hL hT hδ hA
  have hLogInv : -Real.log L ≤ Real.log δ := by
    have hlog := Real.log_le_log (inv_pos.mpr hL) hA
    simpa only [Real.log_inv] using hlog
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  linarith
end Green64Analytic.LongPrime

end

/-! ## G2Eighth -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_eighth_threshold :
∀ (K : ℝ), 0 < K →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → 800*K ≤ L^(1/8:ℝ) :=
by
  intro K hK
  have hlim : Filter.Tendsto
      (fun L : ℝ => L^(1/8:ℝ)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h := hlim.eventually (Filter.eventually_ge_atTop (800*K))
  obtain ⟨L₁,hL₁⟩ := Filter.eventually_atTop.1 h
  refine ⟨max 3 L₁,le_max_left _ _,?_⟩
  intro L hL
  exact hL₁ L ((le_max_right _ _).trans hL)
end Green64Analytic.LongPrime

end

/-! ## G2Height -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_height_threshold :
∀ (C₅ : ℝ), 0 ≤ C₅ →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    1 ≤ L^C₅ ∧ L^C₅ ≤ Real.exp L ∧
    20 + L^C₅ ≤ L^(C₅+3) :=
by
  intro C₅ hC₅
  obtain ⟨L₁,hL₁,hExp⟩ := Green64Analytic.LongPrime.eventual_exp_dominates_rpow C₅
  refine ⟨max 3 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hH : 1 ≤ L^C₅ := Real.one_le_rpow hL1 hC₅
  have hExpL : L^C₅ ≤ Real.exp L := hExp L ((le_max_right _ _).trans hL)
  have hL3pow : 27 ≤ L^3 := by
    calc
      (27:ℝ) = (3:ℝ)^3 := by norm_num
      _ ≤ L^3 := by gcongr
  have hPow : L^(C₅+3) = L^C₅ * L^3 := by
    rw [Real.rpow_add hLp]
    norm_num
  refine ⟨hH,hExpL,?_⟩
  rw [hPow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr (show (21:ℝ) ≤ L^3 by linarith))]
end Green64Analytic.LongPrime

end

/-! ## G2Log -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_log_power :
∀ (L : ℝ), 1 ≤ L → Real.log L ≤ 8 * L^(1/8:ℝ) :=
by
  intro L hL
  have h := Real.log_le_rpow_div (by linarith : 0 ≤ L)
      (show (0:ℝ) < 1/8 by norm_num)
  convert h using 1 <;> ring
end Green64Analytic.LongPrime

end

/-! ## G2Margins -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_source_height_margins :
∀ (C₅ : ℝ), 0 ≤ C₅ →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ (L δ t y : ℝ), L₀ ≤ L →
    0 ≤ δ → δ ≤ 1/100 →
    L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
    |y| ≤ L^C₅ →
    20 + L^C₅ ≤ |t| ∧ 20 ≤ |y-t| ∧ |y-t| ≤ 2*(Real.exp L)^2 ∧
      |t| + L^C₅ + 8*δ ≤ 3*(Real.exp L)^3 :=
by
  intro C₅ hC₅
  obtain ⟨L₀,hL₀,hThreshold⟩ := g2_height_threshold C₅ hC₅
  refine ⟨L₀,hL₀,?_⟩
  intro L δ t y hL hδ hδmax htlo hthi hy
  obtain ⟨hHone,hHexp,hHlo⟩ := hThreshold L hL
  have hHnonneg : 0 ≤ L^C₅ := by linarith
  have hX : 1 ≤ Real.exp L := Real.one_le_exp (by linarith [hL₀.trans hL])
  have hx2 : Real.exp L ≤ (Real.exp L)^2 := by nlinarith [sq_nonneg (Real.exp L-1)]
  have hx3 : (Real.exp L)^2 ≤ (Real.exp L)^3 := by
    calc
      (Real.exp L)^2 = (Real.exp L)^2*1 := by ring
      _ ≤ (Real.exp L)^2*(Real.exp L) :=
        mul_le_mul_of_nonneg_left hX (sq_nonneg _)
      _ = (Real.exp L)^3 := by ring
  have hx13 : Real.exp L ≤ (Real.exp L)^3 :=
    hx2.trans hx3
  have h1x3 : 1 ≤ (Real.exp L)^3 := hX.trans hx13
  have hδeight : 8*δ ≤ 1 := by linarith
  have hTr : |t| ≤ |y-t| + |y| := by
    have h' := abs_sub_abs_le_abs_sub t y
    rw [abs_sub_comm] at h'
    linarith
  have hUpper : |y-t| ≤ |t|+|y| := by
    rw [abs_sub_comm]
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le t 0 y
  constructor
  · exact hHlo.trans htlo
  constructor
  · linarith
  constructor
  · linarith
  · calc
      |t| + L^C₅ + 8*δ ≤ (Real.exp L)^2 + Real.exp L + 1 := by linarith
      _ ≤ 3*(Real.exp L)^3 := by linarith
end Green64Analytic.LongPrime

end

/-! ## G2Polylog -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_khale_polylog :
∀ (z : ℝ), 1 ≤ z →
  z^(2/3:ℝ) * (Real.log z)^(1/3:ℝ) ≤ 4*z^(3/4:ℝ) :=
by
  intro z hz
  have hzpos : 0 < z := by linarith
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have he : Real.log z ≤ 4*z^(1/4:ℝ) := by
    have hh := Real.log_le_rpow_div hzpos.le (show (0:ℝ) < 1/4 by norm_num)
    convert hh using 1 <;> ring
  have hepow : (Real.log z)^(1/3:ℝ) ≤ (4*z^(1/4:ℝ))^(1/3:ℝ) :=
    Real.rpow_le_rpow hlog he (by norm_num)
  have h4 : (4:ℝ)^(1/3:ℝ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ 4 by norm_num)
      (show (1/3:ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using h
  have hzpower : 0 ≤ z^(2/3:ℝ) := Real.rpow_nonneg hzpos.le _
  calc
    z^(2/3:ℝ) * (Real.log z)^(1/3:ℝ) ≤
      z^(2/3:ℝ) * (4*z^(1/4:ℝ))^(1/3:ℝ) :=
        mul_le_mul_of_nonneg_left hepow hzpower
    _ = (4:ℝ)^(1/3:ℝ) * z^(3/4:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4)
        (Real.rpow_nonneg hzpos.le _), ← Real.rpow_mul hzpos.le]
      calc
        z^(2/3:ℝ) * ((4:ℝ)^(1/3:ℝ) * z^((1/4:ℝ)*(1/3:ℝ))) =
          (4:ℝ)^(1/3:ℝ) *
          (z^(2/3:ℝ) * z^((1/4:ℝ)*(1/3:ℝ))) := by ring
        _ = (4:ℝ)^(1/3:ℝ) * z^((2/3:ℝ)+(1/4:ℝ)*(1/3:ℝ)) := by
          rw [Real.rpow_add hzpos]
        _ = (4:ℝ)^(1/3:ℝ) * z^(3/4:ℝ) := by
          congr 1
          ring
    _ ≤ 4*z^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hzpos.le _)
end Green64Analytic.LongPrime

end

/-! ## G2Q -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_log_Q :
∀ (C L : ℝ), 0 ≤ C → 3 ≤ L →
  Real.log (3*L^C) ≤ (2+8*C)*L^(3/4:ℝ) :=
by
  intro C L hC hL
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hqpos : 0 < L^C := Real.rpow_pos_of_pos hLp _
  have hlog3 : Real.log (3:ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hPow : L^(1/8:ℝ) ≤ L^(3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hOne : 1 ≤ L^(3/4:ℝ) :=
    Real.one_le_rpow hLone (by norm_num)
  have hlog := g2_log_power L hLone
  have hMul := mul_le_mul_of_nonneg_left hlog hC
  calc
    Real.log (3*L^C) = Real.log (3:ℝ) + C*Real.log L := by
      rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt hqpos),
        Real.log_rpow hLp]
    _ ≤ 2+C*(8*L^(1/8:ℝ)) := add_le_add hlog3 hMul
    _ ≤ (2+8*C)*L^(3/4:ℝ) := by
      have hpowmul := mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 8*C)
      nlinarith
end Green64Analytic.LongPrime

end

/-! ## G2Denominator -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_Khale_denominator :
∀ (C L : ℝ), 0 ≤ C → 3 ≤ L →
  let Q : ℝ := 3*L^C
  let V : ℝ := 3*Real.exp (3*L)
  let D : ℝ := 10.5*Real.log Q +
    61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
  0 < D ∧ D ≤ (1100+100*C)*L^(3/4:ℝ) :=
by
  intro C L hC hL Q V D
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQge : 3 ≤ Q := by
    dsimp [Q]
    have h := Real.one_le_rpow hLone hC
    nlinarith
  have hLogQ : Real.log Q ≤ (2+8*C)*L^(3/4:ℝ) := by
    simpa only [Q] using g2_log_Q C L hC hL
  have hLog3pos : 0 < Real.log (3:ℝ) := Real.log_pos (by norm_num)
  have hLog3 : Real.log (3:ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    norm_num at hh
    exact hh
  let z : ℝ := Real.log V
  have hzEq : z = Real.log (3:ℝ)+3*L := by
    dsimp [z,V]
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp]
  have hzlo : 1 ≤ z := by linarith
  have hzhi : z ≤ 4*L := by linarith
  have hzpos : 0 < z := by linarith
  have hQLogpos : 0 < Real.log Q := Real.log_pos (by linarith)
  have hZLog : 0 ≤ Real.log z := Real.log_nonneg hzlo
  have hPnonneg : 0 ≤ z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) :=
    mul_nonneg (Real.rpow_nonneg hzpos.le _)
      (Real.rpow_nonneg hZLog _)
  have h4 : (4:ℝ)^(3/4:ℝ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ 4 by norm_num)
      (show (3/4:ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using h
  have hzPower : z^(3/4:ℝ) ≤ 4*L^(3/4:ℝ) := by
    calc
      z^(3/4:ℝ) ≤ (4*L)^(3/4:ℝ) :=
        Real.rpow_le_rpow hzpos.le hzhi (by norm_num)
      _ = (4:ℝ)^(3/4:ℝ)*L^(3/4:ℝ) :=
        Real.mul_rpow (by norm_num) hLp.le
      _ ≤ 4*L^(3/4:ℝ) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hLp.le _)
  have hP : z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) ≤
      16*L^(3/4:ℝ) := by
    calc
      _ ≤ 4*z^(3/4:ℝ) := g2_khale_polylog z hzlo
      _ ≤ 4*(4*L^(3/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hzPower (by norm_num)
      _ = 16*L^(3/4:ℝ) := by ring
  have hK : 0 < (1100+100*C)*L^(3/4:ℝ) := by
    have hc : 0 < (1100+100*C) := by linarith
    positivity
  change 0 < 10.5*Real.log Q +
    61.5*z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) ∧
    10.5*Real.log Q +
    61.5*z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) ≤
      (1100+100*C)*L^(3/4:ℝ)
  constructor
  · have hSecond : 0 ≤ 61.5*(z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ)) :=
      mul_nonneg (show (0:ℝ) ≤ 61.5 by norm_num) hPnonneg
    nlinarith
  · calc
      10.5*Real.log Q + 61.5*z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) ≤
        10.5*((2+8*C)*L^(3/4:ℝ)) + 61.5*(16*L^(3/4:ℝ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hLogQ (show (0:ℝ) ≤ 10.5 by norm_num)
          · simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hP (show (0:ℝ) ≤ 61.5 by norm_num)
      _ ≤ (1100+100*C)*L^(3/4:ℝ) := by
        have hpow : 0 ≤ L^(3/4:ℝ) := Real.rpow_nonneg hLp.le _
        have hdiff : 0 ≤ (1100+100*C)-(10.5*(2+8*C)+61.5*16) := by
          nlinarith
        nlinarith [mul_nonneg hdiff hpow]
end Green64Analytic.LongPrime

end

/-! ## G2Decay -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_parameter_decay :
∀ (C : ℝ), 0 ≤ C →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧
    ∀ L : ℝ, L₀ ≤ L →
    let Q : ℝ := 3*L^C
    let V : ℝ := 3*Real.exp (3*L)
    let D : ℝ := 10.5*Real.log Q +
      61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
    0 < D ∧ 1 ≤ Real.log L ∧
    100*D ≤ L ∧ 100*D*Real.log L ≤ L :=
by
  intro C hC
  let K : ℝ := 1100+100*C
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨L₁,hL₁,hThreshold⟩ := g2_eighth_threshold K hK
  refine ⟨max (Real.exp 1) L₁, ?_, ?_⟩
  · exact hL₁.trans (le_max_right _ _)
  intro L hL Q V D
  have hL3 : 3 ≤ L := hL₁.trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := by linarith
  have hLle : Real.exp 1 ≤ L := (le_max_left _ _).trans hL
  have hTge : 1 ≤ Real.log L := by
    calc
      (1:ℝ) = Real.log (Real.exp 1) := by simp
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos _) hLle
  have hDen := g2_Khale_denominator C L hC hL3
  change 0 < D ∧ D ≤ K*L^(3/4:ℝ) at hDen
  obtain ⟨hD,hDbound⟩ := hDen
  have hTtop : Real.log L ≤ 8*L^(1/8:ℝ) := g2_log_power L (by linarith)
  have hTh : 800*K ≤ L^(1/8:ℝ) := hThreshold L ((le_max_right _ _).trans hL)
  have hP7 : L^(3/4:ℝ)*L^(1/8:ℝ) = L^(7/8:ℝ) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hP8 : L^(1/8:ℝ)*L^(7/8:ℝ) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have h100D : 100*D*Real.log L ≤ L := by
    calc
      100*D*Real.log L ≤ 100*(K*L^(3/4:ℝ))*Real.log L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDbound (by norm_num))
          (by linarith)
      _ ≤ 100*(K*L^(3/4:ℝ))*(8*L^(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_left hTtop (by positivity)
      _ = 800*K*L^(7/8:ℝ) := by
        rw [← hP7]
        ring
      _ ≤ L := by
        calc
          _ ≤ L^(1/8:ℝ)*L^(7/8:ℝ) :=
            mul_le_mul_of_nonneg_right hTh (Real.rpow_nonneg hLp.le _)
          _ = L := hP8
  have hDsmall : 100*D ≤ L := by
    have hpos100 : 0 ≤ 100*D := by positivity
    nlinarith [mul_nonneg hpos100 (sub_nonneg.mpr hTge)]
  exact ⟨hD,hTge,hDsmall,h100D⟩
end Green64Analytic.LongPrime

end

/-! ## G2DenominatorLog -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_denominator_lower_log :
∀ (C L : ℝ), 0 ≤ C → 3 ≤ L →
  let Q : ℝ := 3*L^C
  let V : ℝ := 3*Real.exp (3*L)
  let D : ℝ := 10.5*Real.log Q +
    61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
  10.5*C*Real.log L ≤ D :=
by
  intro C L hC hL Q V D
  have hLp : 0 < L := by linarith
  have hQpower : 0 < L^C := Real.rpow_pos_of_pos hLp _
  have hQeq : Real.log Q = Real.log (3:ℝ)+C*Real.log L := by
    dsimp [Q]
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0)
      (ne_of_gt hQpower), Real.log_rpow hLp]
  have hLog3 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  let z : ℝ := Real.log V
  have hzEq : z = Real.log (3:ℝ)+3*L := by
    dsimp [z,V]
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0)
      (Real.exp_ne_zero _),Real.log_exp]
  have hz : 1 ≤ z := by linarith
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hP : 0 ≤ z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg hlogz _)
  change 10.5*C*Real.log L ≤
    10.5*Real.log Q + 61.5*z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ)
  nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 61.5) hP]
end Green64Analytic.LongPrime

end

/-! ## G2DenominatorLower -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_denominator_ge_one :
∀ (C L : ℝ), 0 ≤ C → 3 ≤ L →
  let Q : ℝ := 3*L^C
  let V : ℝ := 3*Real.exp (3*L)
  let D : ℝ := 10.5*Real.log Q +
    61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
  1 ≤ D :=
by
  intro C L hC hL Q V D
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hQge : (3:ℝ) ≤ Q := by
    dsimp [Q]
    have h := Real.one_le_rpow hLone hC
    nlinarith
  have h3log : (1:ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 ≤ (3:ℝ) :=
      (le_of_lt Real.exp_one_lt_d9).trans (by norm_num)
    have hh := Real.log_le_log (Real.exp_pos _) he
    simpa using hh
  have hQlog : 1 ≤ Real.log Q :=
    h3log.trans (Real.log_le_log (by norm_num) hQge)
  let z : ℝ := Real.log V
  have hz : 1 ≤ z := by
    have hzEq : z = Real.log (3:ℝ)+3*L := by
      dsimp [z,V]
      rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero _), Real.log_exp]
    linarith
  have hzLog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hP : 0 ≤ z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg hzLog _)
  change 1 ≤ 10.5*Real.log Q + 61.5*z^(2/3:ℝ)*(Real.log z)^(1/3:ℝ)
  nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 61.5) hP]
end Green64Analytic.LongPrime

end

/-! ## G2DeltaBudget -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_literal_delta_budget :
∀ (C : ℝ), 0 ≤ C →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧
    ∀ L : ℝ, L₀ ≤ L →
    let Q : ℝ := 3*L^C
    let V : ℝ := 3*Real.exp (3*L)
    let D : ℝ := 10.5*Real.log Q +
      61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
    let δ : ℝ := (100*D)⁻¹
    0 < δ ∧ δ ≤ 1/100 ∧ L⁻¹ ≤ δ ∧ Real.log L ≤ δ*L :=
by
  intro C hC
  obtain ⟨L₀,hL₀,hDecay⟩ := g2_parameter_decay C hC
  refine ⟨L₀,hL₀,?_⟩
  intro L hL Q V D δ
  have hLp : 0 < L := by linarith [hL₀.trans hL]
  have hFacts := hDecay L hL
  change 0 < D ∧ 1 ≤ Real.log L ∧
    100*D ≤ L ∧ 100*D*Real.log L ≤ L at hFacts
  obtain ⟨hD,hLogL,hDsmall,hDlog⟩ := hFacts
  have hDone : 1 ≤ D := g2_denominator_ge_one C L hC (hL₀.trans hL)
  have hDen : 0 < 100*D := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδBound : δ ≤ 1/100 := by
    have hh : (100*D)⁻¹ ≤ (100:ℝ)⁻¹ :=
      (inv_le_inv₀ hDen (by norm_num : (0:ℝ)<100)).2 (by nlinarith)
    simpa only [δ, one_div] using hh
  have hA : L⁻¹ ≤ δ := by
    change L⁻¹ ≤ (100*D)⁻¹
    exact (inv_le_inv₀ hLp hDen).2 hDsmall
  have hT : Real.log L ≤ δ*L := by
    have hdiv : Real.log L ≤ L/(100*D) :=
      (le_div_iff₀ hDen).2 (by nlinarith [hDlog])
    simpa only [δ, div_eq_mul_inv, mul_comm] using hdiv
  exact ⟨hδ,hδBound,hA,hT⟩
end Green64Analytic.LongPrime

end

/-! ## G2SmallDelta -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_delta_below_threshold :
∀ (C δ₀ : ℝ), 0 < C → 0 < δ₀ →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  let Q : ℝ := 3*L^C
  let V : ℝ := 3*Real.exp (3*L)
  let D : ℝ := 10.5*Real.log Q +
    61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
  (100*D)⁻¹ < δ₀ :=
by
  intro C δ₀ hC hδ₀
  let k : ℝ := 1050*C
  have hk : 0 < k := by dsimp [k]; positivity
  let M : ℝ := δ₀⁻¹ / k + 1
  have hloglim : Filter.Tendsto Real.log Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  obtain ⟨L₁,hL₁⟩ := Filter.eventually_atTop.1
    (hloglim.eventually (Filter.eventually_ge_atTop M))
  refine ⟨max 3 L₁,le_max_left _ _,?_⟩
  intro L hL Q V D
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hL
  have hlog : M ≤ Real.log L := hL₁ L ((le_max_right _ _).trans hL)
  have hLower := g2_denominator_lower_log C L hC.le hL3
  change 10.5*C*Real.log L ≤ D at hLower
  have hD1 := g2_denominator_ge_one C L hC.le hL3
  change 1 ≤ D at hD1
  have hDpos : 0 < 100*D := by linarith
  have hMul : k*Real.log L ≤ 100*D := by dsimp [k]; nlinarith
  have hMeq : k*M = δ₀⁻¹ + k := by
    dsimp [M]
    field_simp
  have hMain : δ₀⁻¹ < 100*D := by
    have hh := mul_le_mul_of_nonneg_left hlog hk.le
    linarith
  have hh := (inv_lt_inv₀ hDpos (inv_pos.mpr hδ₀)).2 hMain
  simpa only [inv_inv] using hh
end Green64Analytic.LongPrime

end

/-! ## G2SourceParameters -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem g2_all_source_parameters :
∀ (C C₅ δ₀ : ℝ), 0 < C → 0 ≤ C₅ → 0 < δ₀ →
  ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    let Q : ℝ := 3*L^C
    let V : ℝ := 3*Real.exp (3*L)
    let D : ℝ := 10.5*Real.log Q +
      61.5*(Real.log V)^(2/3:ℝ)*(Real.log (Real.log V))^(1/3:ℝ)
    let δ : ℝ := (100*D)⁻¹
    0 < δ ∧ δ < δ₀ ∧ δ ≤ 1/100 ∧ L⁻¹ ≤ δ ∧
      Real.log L ≤ δ*L ∧
      -50*Real.log L ≤ Real.log δ-Real.log 2 ∧
      100*δ*D = 1 ∧
      (∀ (q : ℕ), (q:ℝ) ≤ L^C → 3*(q:ℝ) ≤ Q) ∧
      (∀ (t y : ℝ), L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
        |y| ≤ L^C₅ →
        20+L^C₅ ≤ |t| ∧ 20 ≤ |y-t| ∧
        |y-t| ≤ 2*(Real.exp L)^2 ∧
        |t|+L^C₅+8*δ ≤ V) :=
by
  intro C C₅ δ₀ hC hC₅ hδ₀
  obtain ⟨L₁,hL₁,hBudget⟩ := g2_literal_delta_budget C hC.le
  obtain ⟨L₂,hL₂,hSmall⟩ := g2_delta_below_threshold C δ₀ hC hδ₀
  obtain ⟨L₃,hL₃,hMargins⟩ := g2_source_height_margins C₅ hC₅
  refine ⟨max L₁ (max L₂ L₃), hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL Q V D δ
  have hL₁' : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL₂' : L₂ ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL₃' : L₃ ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL3 : 3 ≤ L := hL₁.trans hL₁'
  have hLp : 0 < L := by linarith
  have hFacts := hBudget L hL₁'
  change 0 < δ ∧ δ ≤ 1/100 ∧ L⁻¹ ≤ δ ∧
    Real.log L ≤ δ*L at hFacts
  obtain ⟨hδ,hδmax,ha,hT⟩ := hFacts
  have hδsmall := hSmall L hL₂'
  change δ < δ₀ at hδsmall
  have hE : Real.exp 1 ≤ (3:ℝ) :=
    (le_of_lt Real.exp_one_lt_d9).trans (by norm_num)
  have hTge : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos _) (hE.trans hL3)
    simpa only [Real.log_exp] using h
  have hCenter : -50*Real.log L ≤ Real.log δ-Real.log 2 :=
    g2_center_log_budget L δ hLp hTge hδ ha
  have hDone := g2_denominator_ge_one C L hC.le hL3
  change 1 ≤ D at hDone
  have hDpos : 0 < D := by linarith
  have h100D : 100*D ≠ 0 := by positivity
  have hEq : 100*δ*D = 1 := by
    dsimp [δ]
    calc
      100*(100*D)⁻¹*D = (100*D)*(100*D)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ h100D
  refine ⟨hδ,hδsmall,hδmax,ha,hT,hCenter,hEq,?_,?_⟩
  · intro q hq
    dsimp [Q]
    nlinarith
  · intro t y htlo hthi hy
    obtain ⟨hh, hlo, hhi, hv⟩ :=
      hMargins L δ t y hL₃' hδ.le hδmax htlo hthi hy
    have hVeq : 3*(Real.exp L)^3 = V := by
      dsimp [V]
      rw [← Real.exp_nat_mul L 3]
      congr 1
    exact ⟨hh,hlo,hhi,hv.trans_eq hVeq⟩
end Green64Analytic.LongPrime

end

