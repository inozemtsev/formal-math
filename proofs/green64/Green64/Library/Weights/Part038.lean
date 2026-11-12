module

public import Green64.Library.Weights.Part037
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib
public import Green64.Library.Weights.Part016
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Weights / Part038

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## code.SourceMarkedPeeling -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Exact source marked weight for one distinguished small group, all other
    small groups, and big-group ordered lists carrying an arbitrary test b. -/
noncomputable def sourceMarkedWeight {ι β : Type}
    [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (I : Finset ι) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ) (q0 Vs : ℝ)
    (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (tsmall : ι → ℕ) (tbig : β → ℕ)
    (b : (∀ g : β, Fin (tbig g) → ℕ) → ℂ)
    (k n : ℕ) : ℂ :=
    (smallMarkedWeight S q0 Vs k n : ℂ) *
      (otherGroupWeight I Ts q0 Vsmall tsmall n *
        actualBigMarkDecoration Tb tbig q0 Vbig b n)

theorem sourceMarkedWeight_peel {ι β : Type}
    [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (I : Finset ι) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ) (q0 Vs : ℝ)
    (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (tsmall : ι → ℕ) (tbig : β → ℕ)
    (b : (∀ g : β, Fin (tbig g) → ℕ) → ℂ)
    (k n : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g ∈ I, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g ∈ I, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n) :
    sourceMarkedWeight S I Ts Tb q0 Vs Vsmall Vbig tsmall tbig b (k+1) n =
      ((1/Vs : ℝ):ℂ) *
        (∑ p ∈ smallPrimeSupport S n,
          sourceMarkedWeight S I Ts Tb q0 Vs Vsmall Vbig tsmall tbig b k (n/p)) := by
  have hE : ∀ p ∈ smallPrimeSupport S n,
        actualBigMarkDecoration Tb tbig q0 Vbig b (n/p) =
          actualBigMarkDecoration Tb tbig q0 Vbig b n := by
    intro p hp
    obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
    exact actualBigMarkDecoration_div Tb tbig q0 Vbig b n p
      (hS p hpS) hpn hTb (fun g => hDisjB g p hpS)
  simpa only [sourceMarkedWeight, oneGroupInFullWeight] using
    (oneGroupInFullWeight_peel S I Ts q0 Vs Vsmall tsmall
      (actualBigMarkDecoration Tb tbig q0 Vbig b) k n
      hS hTs hDisjS hsquare hE)
end Green64Analytic.CorrelationD

end

/-! ## code.LiteralMarkedSum -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Actual ordered lists in all *other* small groups. -/
noncomputable def otherSmallListFamily {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → Finset ℕ) (t : ι → ℕ) (n : ℕ) :
    Finset (∀ g : ι, Fin (t g) → ℕ) := by
  classical
  exact Fintype.piFinset (fun g => orderedBigMarks (T g) (t g) n)

theorem otherSmallListFamily_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → Finset ℕ) (t : ι → ℕ) (n : ℕ) :
    (otherSmallListFamily T t n).card =
      ∏ g : ι, (smallPrimeCount (T g) n).descFactorial (t g) := by
  classical
  simp [otherSmallListFamily, orderedBigMarks_card]

/-- Count the full actual ordered mark-list sum: the test b sees big
    marked lists only, so all small-group lists contribute factorial counts. -/
theorem literal_mark_sum_factor {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (ts : ι → ℕ) (tb : β → ℕ) (k n : ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) :
    (∑ a ∈ orderedBigMarks S k n,
      ∑ x ∈ otherSmallListFamily Ts ts n,
      ∑ y ∈ bigMarkLists Tb tb n, b y) =
    ((((smallPrimeCount S n).descFactorial k : ℕ) : ℂ) *
      ((∏ g : ι, (smallPrimeCount (Ts g) n).descFactorial (ts g) : ℕ) : ℂ)) *
      (∑ y ∈ bigMarkLists Tb tb n, b y) := by
  classical
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [orderedBigMarks_card, otherSmallListFamily_card]
  push_cast
  ring
end Green64Analytic.CorrelationD

end

/-! ## code.LiteralSourceWeight -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Direct reading of W_t^b: groupwise q₀/V prefactors, then the sum over
    actual ordered distinct marks in every small and big group. -/
noncomputable def literalSourceWeight {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ) : ℂ :=
    (((q0 ^ ((smallPrimeCount S n : ℤ) - (k:ℤ))) / Vs^k : ℝ) : ℂ) *
      bigMarkPrefactor Ts ts q0 Vsmall n *
      bigMarkPrefactor Tb tb q0 Vbig n *
      (∑ a ∈ orderedBigMarks S k n,
        ∑ x ∈ otherSmallListFamily Ts ts n,
        ∑ y ∈ bigMarkLists Tb tb n, b y)

theorem otherGroupWeight_as_literal_prefactor {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (T : ι → Finset ℕ) (t : ι → ℕ)
    (q0 : ℝ) (V : ι → ℝ) (n : ℕ) :
    otherGroupWeight (Finset.univ : Finset ι) T q0 V t n =
      bigMarkPrefactor T t q0 V n *
        ((∏ g : ι, (smallPrimeCount (T g) n).descFactorial (t g) : ℕ) : ℂ) := by
  classical
  unfold otherGroupWeight bigMarkPrefactor
  have hpoint (g : ι) :
      (smallMarkedWeight (T g) q0 (V g) (t g) n : ℂ) =
      ((q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) /
          (V g)^(t g) : ℝ) : ℂ) *
        ((smallPrimeCount (T g) n).descFactorial (t g) : ℂ) := by
    unfold smallMarkedWeight smallMarkKernel
    push_cast
    ring
  calc
    _ = ∏ g : ι,
      ((((q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ))) /
        (V g)^(t g) : ℝ) : ℂ) *
       ((smallPrimeCount (T g) n).descFactorial (t g) : ℂ)) := by
          apply Finset.prod_congr rfl
          intro g _
          exact hpoint g
    _ = (∏ g : ι,
        (((q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ))) /
          (V g)^(t g) : ℝ) : ℂ)) *
        (∏ g : ι, ((smallPrimeCount (T g) n).descFactorial (t g) : ℂ)) := by
          rw [Finset.prod_mul_distrib]
    _ = _ := by
      simp only [Nat.cast_prod]

theorem sourceMarkedWeight_eq_literal {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ) :
    sourceMarkedWeight S (Finset.univ : Finset ι) Ts Tb
      q0 Vs Vsmall Vbig ts tb b k n =
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k n := by
  unfold sourceMarkedWeight literalSourceWeight
  rw [otherGroupWeight_as_literal_prefactor,
    literal_mark_sum_factor]
  unfold actualBigMarkDecoration smallMarkedWeight smallMarkKernel
  push_cast
  ring
end Green64Analytic.CorrelationD

end

/-! ## code.SourceLiteralPeeling -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- The actual source W^b, defined with explicit ordered lists in every
    group, peels a designated small mark with no decoration hypothesis. -/
theorem literalSourceWeight_peel {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g : ι, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g : ι, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n) :
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1) n =
      ((1/Vs : ℝ):ℂ) *
        (∑ p ∈ smallPrimeSupport S n,
          literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k (n/p)) := by
  have hTsmall :
      ∀ g ∈ (Finset.univ : Finset ι), ∀ p ∈ Ts g, p.Prime := by
    intro g _ p hp
    exact hTs g p hp
  have hDsmall :
      ∀ g ∈ (Finset.univ : Finset ι), ∀ p ∈ S, p ∉ Ts g := by
    intro g _ p hp
    exact hDisjS g p hp
  calc
    _ = sourceMarkedWeight S (Finset.univ : Finset ι) Ts Tb
        q0 Vs Vsmall Vbig ts tb b (k+1) n :=
        (sourceMarkedWeight_eq_literal S Ts Tb
          q0 Vs Vsmall Vbig ts tb b (k+1) n).symm
    _ = ((1/Vs : ℝ):ℂ) *
          (∑ p ∈ smallPrimeSupport S n,
          sourceMarkedWeight S (Finset.univ : Finset ι) Ts Tb
            q0 Vs Vsmall Vbig ts tb b k (n/p)) :=
         sourceMarkedWeight_peel S Finset.univ Ts Tb
           q0 Vs Vsmall Vbig ts tb b k n
           hS hTsmall hDsmall hTb hDisjB hsquare
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      exact sourceMarkedWeight_eq_literal S Ts Tb
        q0 Vs Vsmall Vbig ts tb b k (n/p)
end Green64Analytic.CorrelationD

end

/-! ## SourceLiteralPeelSupport -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The literal source peeling difference is ZERO off the genuine
small-mark p²-exceptional support. No abstract support hypothesis,
no dropping q0 damping or big ordered marks. -/
theorem source_literal_peeling_difference_zero
    {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g : ι, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g : ι, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g)
    (hsquare : ∀ p ∈ S, ¬p^2 ∣ n) :
    sourcePeelingError S Vs
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k)
      n = 0 := by
  unfold sourcePeelingError
  rw [literalSourceWeight_peel S Ts Tb q0 Vs Vsmall Vbig ts tb
      b k n hS hTs hDisjS hTb hDisjB hsquare]
  exact sub_self _
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceRoughUnits -/

section

set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationD

/-- The source W-rough condition, expressed without using minFac 1.
    The case m=1 satisfies the premise vacuously. -/
def SourceRoughAbove (m : ℕ) (W : ℝ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → W < (ℓ : ℝ)

theorem rough_factor_coprime (m r : ℕ) (W : ℝ)
    (hr : 0 < r) (hrW : (r : ℝ) ≤ W)
    (hm : SourceRoughAbove m W) : Nat.Coprime m r := by
  by_contra h
  obtain ⟨ℓ, hprime, hdivm, hdivr⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp h
  have hle := Nat.le_of_dvd hr hdivr
  have hcast : (ℓ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
  exact (not_lt_of_ge (hcast.trans hrW)) (hm ℓ hprime hdivm)

theorem source_small_prime_unit (ps r : ℕ) (L a C : ℝ)
    (hps : ps.Prime) (hr : 0 < r) (hrcap : (r:ℝ) ≤ L^C)
    (hscale : L^C < Real.exp (L^a))
    (hgroup : Real.exp (L^a) ≤ (ps:ℝ)) :
    Nat.Coprime ps r := by
  have hlt : r < ps := by exact_mod_cast lt_of_le_of_lt hrcap (lt_of_lt_of_le hscale hgroup)
  exact source_prime_above_modulus_unit ps r hps hr hlt

theorem source_long_prime_unit (p r : ℕ) (L tau C : ℝ)
    (hp : p.Prime) (hr : 0 < r) (hrcap : (r:ℝ) ≤ L^C)
    (hscale : L^C < Real.exp (tau*L))
    (hprime : Real.exp (tau*L) ≤ (p:ℝ)) :
    Nat.Coprime p r := by
  have hlt : r < p := by
    exact_mod_cast lt_of_le_of_lt hrcap (lt_of_lt_of_le hscale hprime)
  exact source_prime_above_modulus_unit p r hp hr hlt

/-- Actual first three source factors and the gcd-reduced residual
    are units modulo the reduced rational-arc modulus q. -/
theorem source_four_factor_unit
    (m ps p rprime r : ℕ) (L a tau C : ℝ)
    (hr : 0 < r) (hrcap : (r:ℝ) ≤ L^C)
    (hrough : SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hpsPrime : ps.Prime)
    (hps : Real.exp (L^a) ≤ (ps:ℝ))
    (hsmall : L^C < Real.exp (L^a))
    (hpPrime : p.Prime)
    (hp : Real.exp (tau*L) ≤ (p:ℝ))
    (hlong : L^C < Real.exp (tau*L)) :
    Nat.Coprime (m * ps * p * (rprime / Nat.gcd rprime r))
      (r / Nat.gcd rprime r) := by
  have hm := rough_factor_coprime m r (Real.exp (Real.sqrt L))
    hr (hrcap.trans hW) hrough
  have hps' := source_small_prime_unit ps r L a C hpsPrime hr hrcap hsmall hps
  have hp' := source_long_prime_unit p r L tau C hpPrime hr hrcap hlong hp
  exact source_three_factor_units m ps p rprime r hr hm hps' hp'
end Green64Analytic.CorrelationD

end

/-! ## code.SourceScaleAsymptotics -/

section

open Filter Real
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationD

/-- A fixed logarithmic-power modulus is eventually below
    every genuine stretched-exponential source prime cutoff. -/
theorem eventually_rpow_lt_exp_rpow_for_selected_correlations (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, L^C < Real.exp (L^a) := by
  have hlimit : Tendsto (fun L : ℝ =>
      Real.exp (L^a) / (L^a)^(C/a)) atTop atTop :=
    (tendsto_exp_div_rpow_atTop (C/a)).comp (tendsto_rpow_atTop ha)
  have hratio : ∀ᶠ L : ℝ in atTop,
      (1:ℝ) < Real.exp (L^a) / (L^a)^(C/a) :=
    hlimit.eventually (eventually_gt_atTop (1:ℝ))
  filter_upwards [hratio, eventually_ge_atTop (1:ℝ)] with L hrat hL
  have hp : 0 < L := by linarith
  have heq : (L^a)^(C/a) = L^C := by
    rw [← Real.rpow_mul (le_of_lt hp)]
    congr 1
    field_simp
  rw [heq] at hrat
  have hden : 0 < L^C := Real.rpow_pos_of_pos hp C
  simpa only [one_mul] using (lt_div_iff₀ hden).mp hrat

theorem eventually_rpow_lt_exp_linear_for_selected_correlations (τ C : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, L^C < Real.exp (τ*L) := by
  have hlimit : Tendsto (fun L : ℝ => Real.exp (τ*L)/L^C)
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop C τ hτ
  have hratio : ∀ᶠ L : ℝ in atTop,
      (1:ℝ) < Real.exp (τ*L)/L^C :=
    hlimit.eventually (eventually_gt_atTop (1:ℝ))
  filter_upwards [hratio, eventually_ge_atTop (1:ℝ)] with L hrat hL
  have hp : 0 < L := by linarith
  have hden : 0 < L^C := Real.rpow_pos_of_pos hp C
  simpa only [one_mul] using (lt_div_iff₀ hden).mp hrat

theorem eventually_source_scales_for_selected_correlations (a τ C : ℝ)
    (ha : 0 < a) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop,
      L^C < Real.exp (Real.sqrt L) ∧
      L^C < Real.exp (L^a) ∧
      L^C < Real.exp (τ*L) := by
  have hW := eventually_rpow_lt_exp_rpow_for_selected_correlations ((1:ℝ)/2) C (by norm_num)
  have hS := eventually_rpow_lt_exp_rpow_for_selected_correlations a C ha
  have hP := eventually_rpow_lt_exp_linear_for_selected_correlations τ C hτ
  filter_upwards [hW, hS, hP] with L hw hs hp
  exact ⟨by simpa only [Real.sqrt_eq_rpow] using hw, hs, hp⟩
end Green64Analytic.CorrelationD

end

/-! ## code.SourceEventualUnits -/

section

set_option maxHeartbeats 8000000
open Filter
namespace Green64Analytic.CorrelationD

/-- Source support implies all four factors are rational-arc units
    uniformly in m, ps, p, rprime, r after a fixed threshold in L.
    This discharges all three former scale-comparison premises. -/
theorem source_four_factor_units_eventually
    (a τ C : ℝ) (ha : 0 < a) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m ps p rprime r : ℕ),
        0 < r →
        (r:ℝ) ≤ L^C →
        SourceRoughAbove m (Real.exp (Real.sqrt L)) →
        ps.Prime → Real.exp (L^a) ≤ (ps:ℝ) →
        p.Prime → Real.exp (τ*L) ≤ (p:ℝ) →
        Nat.Coprime (m * ps * p * (rprime / Nat.gcd rprime r))
          (r / Nat.gcd rprime r) := by
  filter_upwards [eventually_source_scales_for_selected_correlations a τ C ha hτ] with
    L ⟨hW, hS, hP⟩ m ps p rprime r hr hrcap hm hpsPrime hps hpPrime hp
  exact source_four_factor_unit m ps p rprime r L a τ C
    hr hrcap hm (le_of_lt hW) hpsPrime hps hS hpPrime hp hP
end Green64Analytic.CorrelationD

end

/-! ## code.UnweightedDivisorMoments -/

section

open scoped BigOperators
namespace Green64Analytic.Correlation

def ExpectedUnweightedDivisorMoment : Prop :=
∀ (N k : ℕ), (∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^k) ≤
 (N:ℝ)*(1+Real.log N)^(2^k)

theorem unweightedDivisorMoment : ExpectedUnweightedDivisorMoment :=
by
  have moment : ∀ (N k : ℕ), (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k / n) ≤ (1+Real.log N)^(2^k) := by
    have moment : ∀ (N k : ℕ), (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k / n) ≤ (∑ n ∈ Finset.Icc 1 N, (1 : ℝ)/n)^(2^k) := by
      have point : ∀ (n k : ℕ), (n.divisors.card : ℝ)^(k+1) ≤ ∑ d ∈ n.divisors, (d.divisors.card : ℝ)^k * ((n/d).divisors.card : ℝ)^k := by
        have submul : ∀ (a b : ℕ), (a*b).divisors.card ≤ a.divisors.card * b.divisors.card := by
          intro a b
          classical
          by_cases ha : a = 0
          · simp [ha]
          by_cases hb : b = 0
          · simp [hb]
          have hsub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1*p.2) := by
            intro d hd
            rcases Nat.dvd_mul.mp (Nat.mem_divisors.mp hd).1 with ⟨u,v,hu,hv,he⟩
            exact Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr
              ⟨Nat.mem_divisors.mpr ⟨hu,ha⟩,Nat.mem_divisors.mpr ⟨hv,hb⟩⟩,he⟩
          exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans_eq (Finset.card_product _ _))
        
        intro n k
        calc
          _ = ∑ d ∈ n.divisors, (n.divisors.card : ℝ)^k := by
            simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]
            ring
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro d hd
            have h := submul d (n/d)
            rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1] at h
            have hc : (n.divisors.card : ℝ) ≤ (d.divisors.card : ℝ)*((n/d).divisors.card : ℝ) := by exact_mod_cast h
            simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n.divisors.card) hc k
      
      have conv : ∀ (N : ℕ) (f g : ℕ → ℝ), (∀ n, 0 ≤ f n) → (∀ n, 0 ≤ g n) → (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d * g (n/d)) ≤ (∑ n ∈ Finset.Icc 1 N, f n) * (∑ n ∈ Finset.Icc 1 N, g n) := by
        intro N f g hf hg
        classical
        let S := (Finset.Icc 1 N).sigma (fun n => n.divisors)
        let F : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2,p.1/p.2)
        have hp (p : Σ _ : ℕ, ℕ) (h : p ∈ S) :
            1 ≤ p.1 ∧ p.1 ≤ N ∧ p.2 ∣ p.1 := by
          rcases Finset.mem_sigma.mp h with ⟨h1,h2⟩
          exact ⟨(Finset.mem_Icc.mp h1).1,(Finset.mem_Icc.mp h1).2,(Nat.mem_divisors.mp h2).1⟩
        have he (p : Σ _ : ℕ, ℕ) (h : p ∈ S) : p.2 * (p.1/p.2) = p.1 :=
          Nat.mul_div_cancel' (hp p h).2.2
        have hi : Set.InjOn F (↑S : Set (Σ _ : ℕ, ℕ)) := by
          intro p hp' q hq' heq
          have h1 : p.2 = q.2 := congrArg Prod.fst heq
          have h2 : p.1/p.2 = q.1/q.2 := congrArg Prod.snd heq
          have h0 : p.1 = q.1 := by rw [←he p hp',←he q hq',h2,h1]
          cases p; cases q
          simp_all
        have hs : S.image F ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
          intro p h
          rcases Finset.mem_image.mp h with ⟨q,hq,rfl⟩
          have h := hp q hq
          have hqpos : 0 < q.1 := by omega
          have hdpos : 0 < q.2 := Nat.pos_of_dvd_of_pos h.2.2 hqpos
          have hdivpos : 0 < q.1/q.2 := Nat.div_pos (Nat.le_of_dvd hqpos h.2.2) hdpos
          exact Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hdpos,(Nat.le_of_dvd hqpos h.2.2).trans h.2.1⟩,
             Finset.mem_Icc.mpr ⟨hdivpos,(Nat.div_le_self _ _).trans h.2.1⟩⟩
        calc
          _ = ∑ p ∈ S, f (F p).1 * g (F p).2 := by
            dsimp [S,F]
            rw [Finset.sum_sigma]
          _ = ∑ p ∈ S.image F, f p.1*g p.2 := by rw [Finset.sum_image hi]
          _ ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, f p.1*g p.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => mul_nonneg (hf _) (hg _))
          _ = _ := by rw [Finset.sum_product,Finset.sum_mul_sum]
      
      intro N k
      induction k with
      | zero => simp
      | succ k ih =>
        have hn (n : ℕ) : 0 ≤ (n.divisors.card : ℝ)^k / n := by positivity
        have hH : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n := Finset.sum_nonneg (fun n _ => by positivity)
        calc
          _ ≤ ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
              (d.divisors.card : ℝ)^k * ((n/d).divisors.card : ℝ)^k) / n := by
            exact Finset.sum_le_sum (fun n _ => div_le_div_of_nonneg_right (point n k) (Nat.cast_nonneg n))
          _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
              ((d.divisors.card : ℝ)^k / d) * (((n/d).divisors.card : ℝ)^k / (n/d : ℕ)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro d hd
            rw [div_mul_div_comm]
            congr 1
            exact_mod_cast (Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1).symm
          _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k/n) *
              (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k/n) := conv N _ _ hn hn
          _ ≤ (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n)^(2^k) *
              (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n)^(2^k) := 
            mul_le_mul ih ih (Finset.sum_nonneg (fun n _ => hn n)) (pow_nonneg hH _)
          _ = _ := by rw [←pow_two,←pow_mul,pow_succ]
    
    intro N k
    have hH : (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [one_div]
    exact (moment N k).trans (pow_le_pow_left₀
      (Finset.sum_nonneg (fun n _ => by positivity)) (by rw [hH]; exact harmonic_le_one_add_log N) _)
  
  intro N k
  calc
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^k) ≤
      ∑ n ∈ Finset.Icc 1 N, (N:ℝ)*((n.divisors.card:ℝ)^k/n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      calc
        (n.divisors.card:ℝ)^k = (n:ℝ)*((n.divisors.card:ℝ)^k/n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hnN (by positivity)
    _ = (N:ℝ)*(∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^k/n) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (moment N k) (Nat.cast_nonneg N)

end Green64Analytic.Correlation

end

/-! ## code.SquareDivisibilityMoment -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators

namespace Green64Analytic.CorrelationD

def squareDivisibleSupport (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => p^2 ∣ n)

theorem squareSupport_image (N p : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 (N/p^2)).image (fun m => p^2*m) =
      squareDivisibleSupport N p := by
  classical
  have ha : 0 < p^2 := pow_pos hp 2
  ext n
  constructor
  · intro hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hml, hmu⟩ := Finset.mem_Icc.mp hm
    have hbound : m*p^2 ≤ N :=
      (Nat.le_div_iff_mul_le ha).mp hmu
    have hpos : 1 ≤ p^2*m := by
      have hh : 0 < p^2*m := mul_pos ha (by omega)
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpos, by simpa [mul_comm] using hbound⟩, dvd_mul_right (p^2) m⟩
  · intro hn
    obtain ⟨hnrange, hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnrange
    have hquot : 0 < n/(p^2) :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) ha
    have hbound : n/(p^2) ≤ N/(p^2) :=
      Nat.div_le_div_right hnN
    have he : p^2*(n/p^2) = n := Nat.mul_div_cancel' hdiv
    refine Finset.mem_image.mpr ⟨n/(p^2), ?_, he⟩
    exact Finset.mem_Icc.mpr ⟨hquot, hbound⟩

theorem squareSupport_sum (N p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ n ∈ squareDivisibleSupport N p, f (n/p^2)) =
      ∑ m ∈ Finset.Icc 1 (N/p^2), f m := by
  rw [← squareSupport_image N p hp]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro m hm
    have ha : 0 < p^2 := pow_pos hp 2
    rw [Nat.mul_div_cancel_left m ha]
  · intro m hm k hk he
    have ha : 0 < p^2 := pow_pos hp 2
    exact (mul_left_cancel₀ (Nat.ne_of_gt ha)) he

/-- Fixed divisor moment on the *exact* square-divisibility exceptional set. -/
theorem squareDivisorMoment (N p k : ℕ) (hp : 0 < p) :
    (∑ n ∈ squareDivisibleSupport N p,
        (((n/p^2).divisors.card : ℝ)^k)) ≤
    ((N / p^2 : ℕ) : ℝ) * (1+Real.log ((N / p^2 : ℕ) : ℝ))^(2^k) := by
  rw [squareSupport_sum N p hp
      (fun m => ((m.divisors.card : ℝ)^k))]
  exact Green64Analytic.Correlation.unweightedDivisorMoment (N/p^2) k

end Green64Analytic.CorrelationD

end

/-! ## code.SquarePrimeMass -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Source square-exception reciprocal mass. No prime number theorem is used:
    even the full integer interval [P,2P] has mass at most 2/P. -/
theorem dyadic_reciprocal_square_mass
    (P : ℕ) (S : Finset ℕ)
    (hP : 1 ≤ P) (hS : S ⊆ Finset.Icc P (2*P)) :
    (∑ p ∈ S, (1 : ℝ)/(p:ℝ)^2) ≤ 2/(P:ℝ) := by
  have hP0 : (0:ℝ) < P := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hP)
  have hcard : S.card ≤ 2*P := by
    have hc := Finset.card_le_card hS
    have hh : (Finset.Icc P (2*P)).card = P+1 := by simp [Nat.card_Icc]; omega
    rw [hh] at hc
    omega
  have hbound (p : ℕ) (hp : p ∈ S) :
      (1:ℝ)/(p:ℝ)^2 ≤ 1/(P:ℝ)^2 := by
    have hl := (Finset.mem_Icc.mp (hS hp)).1
    have hpr : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hl
    have hs : (P:ℝ)^2 ≤ (p:ℝ)^2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity : 0 < (P:ℝ)^2) hs
  calc
    _ ≤ ∑ p ∈ S, (1:ℝ)/(P:ℝ)^2 :=
        Finset.sum_le_sum (fun p hp => hbound p hp)
    _ = (S.card:ℝ) / (P:ℝ)^2 := by simp [div_eq_mul_inv]
    _ ≤ ((2*P:ℕ):ℝ) / (P:ℝ)^2 := by
      apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      exact_mod_cast hcard
    _ = 2/(P:ℝ) := by
      push_cast
      field_simp

/-- With the source's lower prime-dyad scale this is exponentially small
    in the fixed power L^a. -/
theorem source_small_square_mass (L a : ℝ) (P : ℕ) (S : Finset ℕ)
    (hP : 1 ≤ P) (hS : S ⊆ Finset.Icc P (2*P))
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ)) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)^2) ≤ 4*Real.exp (-(L^a)) := by
  have hp : 0 < (P:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hP)
  have he : 0 < Real.exp (L^a) := Real.exp_pos _
  have hscale : 2/(P:ℝ) ≤ 4/Real.exp (L^a) :=
    (div_le_div_iff₀ hp he).2 (by linarith [hLow])
  calc
    _ ≤ 2/(P:ℝ) := dyadic_reciprocal_square_mass P S hP hS
    _ ≤ 4/Real.exp (L^a) := hscale
    _ = _ := by rw [Real.exp_neg]; ring
end Green64Analytic.CorrelationD

end

/-! ## code.SourceSquareEnvelope -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Endpoint constructed from the literal source core evaluated at n_*
    and an independently specified marked weight W(n). -/
noncomputable def sourceEndpoint (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) (n : ℕ) : ℂ :=
  sourceCore (nStar n) primeSlot α c q χ σ₀ σ₁ * W n

/-- Divisor monotonicity: the sole needed property of the source n_*
    on p²-divisible integers is n_* | (n/p²). -/
theorem divisors_card_le_square_quotient
    (nStar n p : ℕ) (hp : 0 < p)
    (hn : 0 < n) (hp2 : p^2 ∣ n)
    (hstar : nStar ∣ n/p^2) :
    (nStar.divisors.card : ℝ) ≤ ((n/p^2).divisors.card : ℝ) := by
  have hqpos : 0 < n/p^2 := by
    have hpp : 0 < p^2 := pow_pos hp _
    have hfact := Nat.mul_div_cancel' hp2
    have hge : p^2 ≤ n := Nat.le_of_dvd hn hp2
    exact Nat.div_pos hge hpp
  exact_mod_cast Finset.card_le_card
    (Nat.divisors_subset_of_dvd (Nat.ne_of_gt hqpos) hstar)

/-- The source core envelope is *derived from the literal triple sum*;
    only the marked-weight cap and n_* divisor relation remain to instantiate. -/
theorem sourceEndpoint_square_pointwise
    (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (q n p : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hW : ‖W n‖ ≤ B)
    (hp : 0 < p) (hn : 0 < n) (hp2 : p^2 ∣ n)
    (hstar : nStar n ∣ n/p^2) :
    ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2 ≤
      (A*C*B)^2 * (((n/p^2).divisors.card : ℝ)^4) := by
  have hcard := divisors_card_le_square_quotient
    (nStar n) n p hp hn hp2 hstar
  have hpow : ((nStar n).divisors.card : ℝ)^2 ≤
      (((n/p^2).divisors.card : ℝ)^2) := by
    gcongr
  have hcore := sourceCore_divisor_bound
    (nStar n) q primeSlot α c χ σ₀ σ₁ A C hA hC hα hc
  have hfirst :
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖ ≤
      A*C*B*(((n/p^2).divisors.card : ℝ)^2) := by
    unfold sourceEndpoint
    rw [norm_mul]
    calc
      _ ≤ (A*C*((nStar n).divisors.card : ℝ)^2)*‖W n‖ :=
         mul_le_mul_of_nonneg_right hcore (norm_nonneg _)
      _ ≤ (A*C*((nStar n).divisors.card : ℝ)^2)*B :=
         mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ (A*C*(((n/p^2).divisors.card : ℝ)^2))*B := by
         exact mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hC)) hB
      _ = _ := by ring
  calc
    _ ≤ (A*C*B*(((n/p^2).divisors.card : ℝ)^2))^2 := by
      gcongr
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceSquareAtPrime -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- The exact p²-divisible source-endpoint L² bound at a fixed prime,
    with no assumed square-error L² premise. -/
theorem sourceSquareAtPrime
    (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q p : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hp : 0 < p)
    (hStar : ∀ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       nStar n ∣ n/p^2)
    (hWcap : ∀ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       ‖W n‖ ≤ B) :
    (∑ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N p,
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
    (A*C*B)^2 * ((N/p^2 : ℕ) : ℝ) *
      (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 := by
  let S := Green64Analytic.CorrelationD.squareDivisibleSupport N p
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2 ≤
      (A*C*B)^2 * (((n/p^2).divisors.card : ℝ)^4) := by
    have hmem := Finset.mem_filter.mp hn
    have hpos : 0 < n := (Finset.mem_Icc.mp hmem.1).1
    exact sourceEndpoint_square_pointwise nStar W primeSlot α c
      q n p χ σ₀ σ₁ A C B hA hC hB hα hc
      (hWcap n hn) hp hpos hmem.2 (hStar n hn)
  calc
    _ ≤ ∑ n ∈ S, (A*C*B)^2 * (((n/p^2).divisors.card : ℝ)^4) := by
      exact Finset.sum_le_sum (fun n hn => hterm n hn)
    _ = (A*C*B)^2 * (∑ n ∈ S,
          (((n/p^2).divisors.card : ℝ)^4)) := by rw [Finset.mul_sum]
    _ ≤ (A*C*B)^2 * (((N/p^2 : ℕ) : ℝ) *
          (1+Real.log ((N/p^2 : ℕ) : ℝ))^(2^4)) :=
      mul_le_mul_of_nonneg_left
        (Green64Analytic.CorrelationD.squareDivisorMoment N p 4 hp)
        (sq_nonneg _)
    _ = _ := by norm_num; ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.SquareScaleBounds -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

theorem square_quotient_log_mono (N p : ℕ)
    (hN : 1 ≤ N) :
    0 ≤ 1+Real.log ((N/p^2 : ℕ) : ℝ) ∧
    1+Real.log ((N/p^2 : ℕ) : ℝ) ≤
       1+Real.log (N : ℝ) := by
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNreal
  by_cases hz : N/p^2 = 0
  · simp [hz, hNlog]
  · have hqpos : (0:ℝ) < ((N/p^2 : ℕ):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    have hqle : ((N/p^2 : ℕ):ℝ) ≤ (N:ℝ) := by
      exact_mod_cast Nat.div_le_self N (p^2)
    have hlog : Real.log ((N/p^2 : ℕ) : ℝ) ≤
      Real.log (N:ℝ) := Real.log_le_log hqpos hqle
    have hlog0 : 0 ≤ Real.log ((N/p^2 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)
    constructor <;> linarith

theorem square_quotient_floor_div (N p : ℕ) (hp : 0 < p) :
    ((N/p^2 : ℕ) : ℝ) ≤ (N:ℝ)/(p:ℝ)^2 := by
  have hh := Nat.div_mul_le_self N (p^2)
  have hc : (((N/p^2 : ℕ) : ℝ) * (p:ℝ)^2) ≤ (N:ℝ) := by
    exact_mod_cast hh
  exact (le_div_iff₀ (by positivity : (0:ℝ) < (p:ℝ)^2)).mpr hc

/-- Uniform scale form of the prime-specific divisor bound. -/
theorem square_quotient_moment_scale (N p : ℕ)
    (hN : 1 ≤ N) (hp : 0 < p) :
    ((N/p^2 : ℕ) : ℝ) *
        (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 ≤
      (N:ℝ)*(1+Real.log (N:ℝ))^16/(p:ℝ)^2 := by
  obtain ⟨hlog0, hlog⟩ := square_quotient_log_mono N p hN
  have hq := square_quotient_floor_div N p hp
  have hpow : (1+Real.log ((N/p^2 : ℕ):ℝ))^16 ≤
      (1+Real.log (N:ℝ))^16 := by
    gcongr
  calc
    _ ≤ ((N:ℝ)/(p:ℝ)^2) *
        (1+Real.log (N:ℝ))^16 := by
      exact mul_le_mul hq hpow (pow_nonneg hlog0 _) (by positivity)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceSquareDoubleMass -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Uniform source error mass, summed over *all* squared small primes.
    This is the double-counting upper bound: no diagonal or disjointness
    of the exceptional square sets is assumed. -/
theorem sourceSquareDoubleMass
    (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q P : ℕ) (S : Finset ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B L a : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hS : S ⊆ Finset.Icc P (2*P))
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ))
    (hStar : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       nStar n ∣ n/p^2)
    (hWcap : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       ‖W n‖ ≤ B) :
    (∑ p ∈ S, ∑ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
      4*(A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16*
        Real.exp (-(L^a)) := by
  let K : ℝ := (A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpPos (p : ℕ) (hpS : p ∈ S) : 0 < p := by
    have hmem := Finset.mem_Icc.mp (hS hpS)
    omega
  have hscale (p : ℕ) (hpS : p ∈ S) :
      (A*C*B)^2 * ((N/p^2 : ℕ) : ℝ) *
        (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 ≤
      K / (p:ℝ)^2 := by
    have hq := square_quotient_moment_scale N p hN (hpPos p hpS)
    have hh := mul_le_mul_of_nonneg_left hq (sq_nonneg (A*C*B))
    dsimp [K]
    calc
      _ = (A*C*B)^2 *
          (((N/p^2 : ℕ) : ℝ) *
          (1+Real.log ((N/p^2 : ℕ) : ℝ))^16) := by ring
      _ ≤ (A*C*B)^2 *
          ((N:ℝ)*(1+Real.log (N:ℝ))^16/(p:ℝ)^2) := hh
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ S, (A*C*B)^2 * ((N/p^2 : ℕ) : ℝ) *
        (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 := by
      apply Finset.sum_le_sum
      intro p hpS
      exact sourceSquareAtPrime nStar W primeSlot α c N q p χ
        σ₀ σ₁ A C B hA hC hB hα hc (hpPos p hpS)
        (hStar p hpS) (hWcap p hpS)
    _ ≤ ∑ p ∈ S, K/(p:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hpS
      exact hscale p hpS
    _ = K * ∑ p ∈ S, (1:ℝ)/(p:ℝ)^2 := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
    _ ≤ K * (4*Real.exp (-(L^a))) :=
      mul_le_mul_of_nonneg_left
        (Green64Analytic.CorrelationD.source_small_square_mass
          L a P S hP hS hLow) hK
    _ = _ := by dsimp [K]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.UnionSquareSupport -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

def sourceSquareExceptionalSupport (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => ∃ p ∈ S, p^2 ∣ n)

theorem sourceSquareExceptionalSupport_eq_union
    (N : ℕ) (S : Finset ℕ) :
    sourceSquareExceptionalSupport N S =
      S.biUnion (fun p =>
        Green64Analytic.CorrelationD.squareDivisibleSupport N p) := by
  classical
  ext n
  simp only [sourceSquareExceptionalSupport,
    Green64Analytic.CorrelationD.squareDivisibleSupport,
    Finset.mem_filter, Finset.mem_biUnion]
  tauto

/-- Elementary nonnegative union bound with overlapping finite supports. -/
theorem finite_sum_union_le {ι : Type} [DecidableEq ι] (s t : Finset ι)
    (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s ∪ t, f x) ≤ (∑ x ∈ s, f x) + (∑ x ∈ t, f x) := by
  classical
  have hpart : s ∪ t = (s \ t) ∪ t := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hpart, Finset.sum_union (Finset.sdiff_disjoint)]
  exact add_le_add_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun x _ _ => hf x)) _

theorem finite_sum_biUnion_le {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (S : Finset ι)
    (T : ι → Finset κ) (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ S.biUnion T, f x) ≤
      ∑ p ∈ S, ∑ x ∈ T p, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (finite_sum_union_le (T a) (s.biUnion T) f hf).trans
        (add_le_add_right ih _)
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceSquareUnionMass -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- The real physical error uses the UNION of p²-exceptional positions,
    not the sum with multiplicity. This inequality allows overlaps. -/
theorem sourceSquareUnionLeDouble
    (N : ℕ) (S : Finset ℕ) (E : ℕ → ℂ) :
    (∑ n ∈ sourceSquareExceptionalSupport N S, ‖E n‖^2) ≤
      ∑ p ∈ S, ∑ n ∈
        Green64Analytic.CorrelationD.squareDivisibleSupport N p,
        ‖E n‖^2 := by
  rw [sourceSquareExceptionalSupport_eq_union]
  exact finite_sum_biUnion_le S
    (Green64Analytic.CorrelationD.squareDivisibleSupport N)
    (fun n => ‖E n‖^2) (fun _ => sq_nonneg _)

/-- Quantitative source square-error L² for the literal invariant
    three-factor core and marked endpoint W, reduced to exactly two
    source-side arithmetic facts: n_*|n/p² and the marked cap. -/
theorem sourceSquareUnionMass
    (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q P : ℕ) (S : Finset ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B L a : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hS : S ⊆ Finset.Icc P (2*P))
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ))
    (hStar : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       nStar n ∣ n/p^2)
    (hWcap : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       ‖W n‖ ≤ B) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
      4*(A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16*
        Real.exp (-(L^a)) := by
  calc
    _ ≤ ∑ p ∈ S, ∑ n ∈
          Green64Analytic.CorrelationD.squareDivisibleSupport N p,
          ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2 :=
        sourceSquareUnionLeDouble N S
          (sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁)
    _ ≤ _ := sourceSquareDoubleMass nStar W primeSlot α c
      N q P S χ σ₀ σ₁ A C B L a hA hC hB hα hc
      hN hP hS hLow hStar hWcap
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSquareUnionReciprocal -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Reuse the proved single-prime square moment and union bound.
The exact reciprocal-square sum replaces the old dyadic group restriction;
no square-peeling identity or individual prime estimate is reproved. -/
theorem source_square_union_reciprocal_mass434
    (nStar : ℕ → ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q : ℕ) (S : Finset ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hpPos : ∀ p ∈ S, 0 < p)
    (hStar : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       nStar n ∣ n/p^2)
    (hWcap : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
       ‖W n‖ ≤ B) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
      ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
      ((A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16)*
        (∑ p ∈ S, (1:ℝ)/(p:ℝ)^2) := by
  let K : ℝ := (A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hscale (p : ℕ) (hpS : p ∈ S) :
      (A*C*B)^2 * ((N/p^2 : ℕ) : ℝ) *
        (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 ≤
      K / (p:ℝ)^2 := by
    have hq := square_quotient_moment_scale N p hN (hpPos p hpS)
    have hh := mul_le_mul_of_nonneg_left hq (sq_nonneg (A*C*B))
    dsimp [K]
    calc
      _ = (A*C*B)^2 *
          (((N/p^2 : ℕ) : ℝ) *
          (1+Real.log ((N/p^2 : ℕ) : ℝ))^16) := by ring
      _ ≤ (A*C*B)^2 *
          ((N:ℝ)*(1+Real.log (N:ℝ))^16/(p:ℝ)^2) := hh
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ S, ∑ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N p,
        ‖sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁ n‖^2 :=
      sourceSquareUnionLeDouble N S (sourceEndpoint nStar W primeSlot α c q χ σ₀ σ₁)
    _ ≤ ∑ p ∈ S, (A*C*B)^2 * ((N/p^2 : ℕ) : ℝ) *
        (1+Real.log ((N/p^2 : ℕ) : ℝ))^16 := by
      apply Finset.sum_le_sum
      intro p hpS
      exact sourceSquareAtPrime nStar W primeSlot α c N q p χ
        σ₀ σ₁ A C B hA hC hB hα hc (hpPos p hpS)
        (hStar p hpS) (hWcap p hpS)
    _ ≤ ∑ p ∈ S, K/(p:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hpS
      exact hscale p hpS
    _ = K * ∑ p ∈ S, (1:ℝ)/(p:ℝ)^2 := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

/-! ## code.LiteralSourceOutsidePart -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Literal n_* = product of the complete prime powers outside all
    marked groups; this uses distinct support n.primeFactors and keeps
    the multiplicities n.factorization p. -/
noncomputable def sourceOutsidePart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∉ P, p^(n.factorization p)

noncomputable def sourceInsidePart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∈ P, p^(n.factorization p)

theorem sourceParts_mul (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    sourceOutsidePart P n * sourceInsidePart P n = n := by
  classical
  unfold sourceOutsidePart sourceInsidePart
  rw [Finset.prod_filter_not_mul_prod_filter]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem sourceInsidePart_square_dvd (P : Finset ℕ) (n p : ℕ)
    (hn : n ≠ 0) (hp : p.Prime) (hpP : p ∈ P)
    (hp2 : p^2 ∣ n) :
    p^2 ∣ sourceInsidePart P n := by
  classical
  have hpdiv : p ∣ n := (dvd_pow_self p (by norm_num : (2:ℕ) ≠ 0)).trans hp2
  have hpMem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hn⟩
  have hexp : 2 ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn).mp hp2
  unfold sourceInsidePart
  exact (Nat.pow_dvd_pow p hexp).trans
    (Finset.dvd_prod_of_mem (fun v => v^(n.factorization v))
      (Finset.mem_filter.mpr ⟨hpMem, hpP⟩))


/-- The source's true n_* is automatically a divisor of n/p² on
    the square exceptional set, because p is a removed group prime. -/
theorem sourceOutsidePart_dvd_square_quotient
    (P : Finset ℕ) (n p : ℕ)
    (hn : n ≠ 0) (hp : p.Prime) (hpP : p ∈ P)
    (hp2 : p^2 ∣ n) :
    sourceOutsidePart P n ∣ n/p^2 := by
  have hins := sourceInsidePart_square_dvd P n p hn hp hpP hp2
  obtain ⟨z, hz⟩ := hins
  have hdecomp := sourceParts_mul P n hn
  have heq : n = p^2 * (sourceOutsidePart P n * z) := by
    calc
      _ = sourceOutsidePart P n * sourceInsidePart P n := hdecomp.symm
      _ = sourceOutsidePart P n * (p^2*z) := by rw [hz]
      _ = _ := by ring
  have hquot : n/p^2 = sourceOutsidePart P n * z := by
    calc
      _ = (p^2 * (sourceOutsidePart P n * z))/p^2 :=
        congrArg (fun u : ℕ => u/p^2) heq
      _ = _ := Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)
  exact ⟨z, hquot⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeelOutsideSquares -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The exact source W^b peeling residual vanishes on every
non-exceptional n between 1 and N: not just on a formal abstract
good set. This uses the exact p²-union support. -/
theorem source_literal_peeling_zero_off_exception
    {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (N : ℕ) (S : Finset ℕ) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g : ι, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g : ι, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g)
    (hn : n ∈ Finset.Icc 1 N)
    (hgood : n ∉ sourceSquareExceptionalSupport N S) :
    sourcePeelingError S Vs
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k)
      n = 0 := by
  have hnosq : ∀ p ∈ S, ¬ p^2 ∣ n := by
    intro p hp hdiv
    exact hgood (Finset.mem_filter.mpr
      ⟨hn, ⟨p,hp,hdiv⟩⟩)
  exact source_literal_peeling_difference_zero
    S Ts Tb q0 Vs Vsmall Vbig ts tb b k n
    hS hTs hDisjS hTb hDisjB hnosq

/-- Hence the entire literal three-factor physical peeling *difference*
vanishes outside the exceptional support, including its character
and complex oscillatory factors. -/
theorem source_physical_peeling_zero_off_exception
    {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k n : ℕ)
    (allGroupPrimes primeSlot : Finset ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g : ι, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g : ι, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g)
    (hn : n ∈ Finset.Icc 1 N)
    (hgood : n ∉ sourceSquareExceptionalSupport N S) :
    sourceEndpoint (sourceOutsidePart allGroupPrimes)
      (sourcePeelingError S Vs
        (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
        (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k))
      primeSlot α c q χ σ₀ σ₁ n = 0 := by
  have hz := source_literal_peeling_zero_off_exception
    N S Ts Tb q0 Vs Vsmall Vbig ts tb b k n
    hS hTs hDisjS hTb hDisjB hn hgood
  unfold sourceEndpoint
  rw [hz]
  simp
end Green64Analytic.CorrelationSquare

end

/-! ## code.LiteralCoreSquareUnion -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- The physical square-error union estimate with the exact source
    outside-group n_*; no source n_*-divisibility premise remains. -/
theorem literalCoreSquareUnionMass
    (allGroupPrimes S : Finset ℕ) (W : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q P : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B L a : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hS : S ⊆ Finset.Icc P (2*P))
    (hGroups : S ⊆ allGroupPrimes)
    (hPrime : ∀ p ∈ S, p.Prime)
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ))
    (hWcap : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ‖W n‖ ≤ B) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
      ‖sourceEndpoint (sourceOutsidePart allGroupPrimes) W
          primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
      4*(A*C*B)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16*
        Real.exp (-(L^a)) := by
  have hstar : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
      sourceOutsidePart allGroupPrimes n ∣ n/p^2 := by
    intro p hp n hn
    have hmem := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hmem.1).1
    exact sourceOutsidePart_dvd_square_quotient allGroupPrimes n p
       (Nat.ne_of_gt hnpos) (hPrime p hp) (hGroups hp) hmem.2
  have hW : ∀ p ∈ S, ∀ n ∈
      Green64Analytic.CorrelationD.squareDivisibleSupport N p,
      ‖W n‖ ≤ B := by
    intro p hp n hn
    obtain ⟨hnIcc,hpn⟩ := Finset.mem_filter.mp hn
    exact hWcap n (Finset.mem_filter.mpr
       ⟨hnIcc, ⟨p,hp,hpn⟩⟩)
  exact sourceSquareUnionMass (sourceOutsidePart allGroupPrimes)
    W primeSlot α c N q P S χ σ₀ σ₁ A C B L a
    hA hC hB hα hc hN hP hS hLow hstar hW
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupPeelingMass -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Entire original small group, not an artificially dyadic subgroup.
Only the final reciprocal summation is generalized; the proved physical
square support, original outside-part arithmetic and marked cap are reused. -/
theorem source_peeling_original_group_square_union434
    (allGroupPrimes S : Finset ℕ) (W_hi W_lo : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B V vmin L a D Vplus : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N)
    (hGroups : S ⊆ allGroupPrimes)
    (hPrime : ∀ p ∈ S, p.Prime)
    (hmin : ∀ p ∈ S, Real.exp (L^a) ≤ (p:ℝ))
    (hMass : (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Vplus)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hv : 0 < vmin) (hV : vmin ≤ V)
    (hlogN : Real.log (N:ℝ) ≤ D*L)
    (hhi : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ‖W_hi n‖ ≤ B)
    (hlo : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ∀ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ ≤ B) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖sourceEndpoint (sourceOutsidePart allGroupPrimes)
         (sourcePeelingError S V W_hi W_lo)
         primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
       Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
         (N:ℝ)*(1+Real.log (N:ℝ))^16*
         Real.exp (-(L^a)) := by
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1:ℝ)<2)
  have hK : 0 ≤ (1+D/(vmin*Real.log 2)) := by positivity
  have hBcap : 0 ≤ B*L*(1+D/(vmin*Real.log 2)) := by
    positivity
  have hpeel : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ‖sourcePeelingError S V W_hi W_lo n‖ ≤
         B*L*(1+D/(vmin*Real.log 2)) := by
    intro n hn
    have hIcc : n ∈ Finset.Icc 1 N :=
       (Finset.mem_filter.mp hn).1
    obtain ⟨hnpos,hnle⟩ := Finset.mem_Icc.mp hIcc
    exact peeling_error_log_power S n N V vmin B L D W_hi W_lo
      hPrime hnpos hnle hv hV hL hD hlogN
      hB (hhi n hn) (hlo n hn)
  let E := sourcePeelingError S V W_hi W_lo
  have hstar : ∀ p ∈ S, ∀ n ∈ squareDivisibleSupport N p,
      sourceOutsidePart allGroupPrimes n ∣ n/p^2 := by
    intro p hp n hn
    obtain ⟨hnIcc,hpn⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
    exact sourceOutsidePart_dvd_square_quotient allGroupPrimes n p
      hnpos.ne' (hPrime p hp) (hGroups hp) hpn
  have hW : ∀ p ∈ S, ∀ n ∈ squareDivisibleSupport N p,
      ‖E n‖ ≤ B*L*(1+D/(vmin*Real.log 2)) := by
    intro p hp n hn
    obtain ⟨hnIcc,hpn⟩ := Finset.mem_filter.mp hn
    exact hpeel n (Finset.mem_filter.mpr ⟨hnIcc,p,hp,hpn⟩)
  have hNorm := source_square_union_reciprocal_mass434
    (sourceOutsidePart allGroupPrimes) E primeSlot α c N q S χ
    σ₀ σ₁ A C (B*L*(1+D/(vmin*Real.log 2)))
    hA hC hBcap hα hc hN (fun p hp => (hPrime p hp).pos) hstar hW
  have hSq := source_original_group_square_mass434 S L a Vplus hmin hMass
  have hFactor : 0 ≤ (A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
      (N:ℝ)*(1+Real.log (N:ℝ))^16 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hSq hFactor
  apply hNorm.trans
  convert hScaled using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.PeelingErrorSquareUnion -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- This also bounds the difference between the original marked term
    and the sum of peeled terms on the exact square-exception union. -/
theorem sourcePeelingDifferenceSquareUnion
    (allGroupPrimes S : Finset ℕ) (W_hi W_lo : ℕ → ℂ)
    (primeSlot : Finset ℕ) (α c : ℕ → ℂ)
    (N q P : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B V vmin L a D : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hS : S ⊆ Finset.Icc P (2*P))
    (hGroups : S ⊆ allGroupPrimes)
    (hPrime : ∀ p ∈ S, p.Prime)
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ))
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hv : 0 < vmin) (hV : vmin ≤ V)
    (hlogN : Real.log (N:ℝ) ≤ D*L)
    (hhi : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ‖W_hi n‖ ≤ B)
    (hlo : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ∀ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ ≤ B) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖sourceEndpoint (sourceOutsidePart allGroupPrimes)
         (sourcePeelingError S V W_hi W_lo)
         primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
       4*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
         (N:ℝ)*(1+Real.log (N:ℝ))^16*
         Real.exp (-(L^a)) := by
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1:ℝ)<2)
  have hK : 0 ≤ (1+D/(vmin*Real.log 2)) := by positivity
  have hBcap : 0 ≤ B*L*(1+D/(vmin*Real.log 2)) := by
    positivity
  have hpeel : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ‖sourcePeelingError S V W_hi W_lo n‖ ≤
         B*L*(1+D/(vmin*Real.log 2)) := by
    intro n hn
    have hIcc : n ∈ Finset.Icc 1 N :=
       (Finset.mem_filter.mp hn).1
    obtain ⟨hnpos,hnle⟩ := Finset.mem_Icc.mp hIcc
    exact peeling_error_log_power S n N V vmin B L D W_hi W_lo
      hPrime hnpos hnle hv hV hL hD hlogN
      hB (hhi n hn) (hlo n hn)
  exact literalCoreSquareUnionMass allGroupPrimes S
    (sourcePeelingError S V W_hi W_lo)
    primeSlot α c N q P χ σ₀ σ₁ A C
    (B*L*(1+D/(vmin*Real.log 2))) L a
    hA hC hBcap hα hc hN hP hS hGroups hPrime hLow hpeel
end Green64Analytic.CorrelationSquare

end

/-! ## code.UniformMarkedScalar -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Polynomial times geometric damping is bounded uniformly over the
    number u of distinct prime divisors, for each fixed mark count k. -/
theorem polynomial_geometric_bounded (k : ℕ) (q0 : ℝ)
    (hq : 0 ≤ q0) (hq1 : q0 < 1) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u : ℕ, (u:ℝ)^k*q0^u ≤ M := by
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one k hq hq1
  have hb := Metric.isBounded_range_of_tendsto
     (fun u : ℕ => (u:ℝ)^k*q0^u) ht
  obtain ⟨M, hM⟩ := hb.bddAbove
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro u
  exact (hM ⟨u, rfl⟩).trans (le_max_right _ _)

/-- One source group has an absolute uniform marked-weight bound,
    *independent of the number u of prime divisors*. -/
theorem single_group_weight_uniform (k : ℕ) (q0 V : ℝ)
    (hq : 0 < q0) (hq1 : q0 < 1) (hV : 0 < V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℕ,
      |q0 ^ ((u:ℤ)-(k:ℤ)) *
          (u.descFactorial k : ℝ) / V^k| ≤ M := by
  obtain ⟨M0, hM0, hM⟩ :=
    polynomial_geometric_bounded k q0 (le_of_lt hq) hq1
  have hD : 0 < q0^k*V^k := by positivity
  refine ⟨M0/(q0^k*V^k), div_nonneg hM0 (le_of_lt hD), ?_⟩
  intro u
  have hf : ((u.descFactorial k : ℕ) : ℝ) ≤ (u:ℝ)^k := by
    exact_mod_cast Nat.descFactorial_le_pow u k
  have hnum : q0^u * (u.descFactorial k : ℝ) ≤ M0 := by
    calc
      _ ≤ q0^u * (u:ℝ)^k :=
         mul_le_mul_of_nonneg_left hf (pow_nonneg (le_of_lt hq) _)
      _ = (u:ℝ)^k*q0^u := by ring
      _ ≤ M0 := hM u
  have hnonneg : 0 ≤ q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / V^k := by positivity

  rw [abs_of_nonneg hnonneg]
  rw [zpow_sub₀ (ne_of_gt hq), zpow_natCast, zpow_natCast]
  have heq : (q0^u / q0^k) * (u.descFactorial k : ℝ) / V^k =
      (q0^u * (u.descFactorial k : ℝ))/(q0^k*V^k) := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hD)
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceGroupMarkCap -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

theorem sourceBigMarkPrefactor_norm {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ) (q0 : ℝ)
    (V : β → ℝ) (n : ℕ)
    (hq0 : 0 < q0) (hV : ∀ g, 0 < V g) :
    ‖bigMarkPrefactor T t q0 V n‖ =
    ∏ g : β, q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) /
      (V g)^(t g) := by
  classical
  unfold bigMarkPrefactor
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro g _
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply abs_of_nonneg
  exact div_nonneg (le_of_lt (zpow_pos hq0 _))
    (le_of_lt (pow_pos (hV g) _))

/-- An arbitrary test of the *actual ordered mark lists* is bounded
    pointwise by the literal product of groupwise scalar marked weights. -/
theorem sourceBigMarkDecoration_pointwise {β : Type}
    [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (q0 : ℝ) (V : β → ℝ)
    (b : (∀ g : β, Fin (t g) → ℕ) → ℂ)
    (n : ℕ) (hq0 : 0 < q0) (hV : ∀ g, 0 < V g)
    (hb : ∀ lists, ‖b lists‖ ≤ 1) :
    ‖actualBigMarkDecoration T t q0 V b n‖ ≤
      ∏ g : β,
        (q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) *
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ) /
           (V g)^(t g)) := by
  classical
  have hsum : ‖∑ lists ∈ bigMarkLists T t n, b lists‖ ≤
      ((bigMarkLists T t n).card : ℝ) := by
    calc
      _ ≤ ∑ lists ∈ bigMarkLists T t n, ‖b lists‖ :=
         norm_sum_le _ _
      _ ≤ ∑ lists ∈ bigMarkLists T t n, (1:ℝ) :=
         Finset.sum_le_sum (fun lists _ => hb lists)
      _ = _ := by simp
  unfold actualBigMarkDecoration
  rw [norm_mul]
  calc
    _ ≤ ‖bigMarkPrefactor T t q0 V n‖ *
        ((bigMarkLists T t n).card : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = (∏ g : β,
          q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) /
            (V g)^(t g)) *
        (∏ g : β,
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ)) := by
        rw [sourceBigMarkPrefactor_norm T t q0 V n hq0 hV,
          bigMarkLists_card]
        push_cast
        rfl
    _ = _ := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro g _
        ring

/-- Full source list weight with any bounded test b has a finite
    uniform cap for fixed finite group data, without an analytic input. -/
theorem sourceBigMarkDecoration_uniform {β : Type}
    [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (q0 : ℝ) (V : β → ℝ)
    (b : (∀ g : β, Fin (t g) → ℕ) → ℂ)
    (hq0 : 0 < q0) (hq1 : q0 < 1)
    (hV : ∀ g, 0 < V g)
    (hb : ∀ lists, ‖b lists‖ ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, ‖actualBigMarkDecoration T t q0 V b n‖ ≤ B := by
  classical
  have hc (g : β) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ u : ℕ, |q0 ^ ((u:ℤ)-(t g:ℤ)) *
          (u.descFactorial (t g) : ℝ) / (V g)^(t g)| ≤ M :=
    single_group_weight_uniform (t g) q0 (V g) hq0 hq1 (hV g)
  let M : β → ℝ := fun g => (hc g).choose
  have hm (g : β) : 0 ≤ M g ∧
      ∀ u : ℕ, |q0 ^ ((u:ℤ)-(t g:ℤ)) *
          (u.descFactorial (t g) : ℝ) / (V g)^(t g)| ≤ M g :=
    (hc g).choose_spec
  refine ⟨∏ g : β, M g, Finset.prod_nonneg
    (fun g _ => (hm g).1), ?_⟩
  intro n

  have hpos (g : β) : 0 ≤
      q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) *
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ) /
          (V g)^(t g) := by
    apply div_nonneg
    · exact mul_nonneg (le_of_lt (zpow_pos hq0 _)) (Nat.cast_nonneg _)
    · exact le_of_lt (pow_pos (hV g) _)
  calc
    _ ≤ ∏ g : β, (q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) *
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ) /
          (V g)^(t g)) :=
        sourceBigMarkDecoration_pointwise T t q0 V b n hq0 hV hb
    _ ≤ ∏ g : β, M g := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact hpos g
      · intro g _
        have hg := (hm g).2 (smallPrimeCount (T g) n)
        simpa only [abs_of_nonneg (hpos g)] using hg
end Green64Analytic.CorrelationSquare

end

/-! ## code.UniformGroupCap -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Uniform in *all* group mark counts up to tmax and all reciprocal
    normalizers V ≥ vmin; the constant depends only on fixed q0,vmin,tmax. -/
theorem uniform_group_mark_bound
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (k u : ℕ) (V : ℝ),
        k ≤ tmax → vmin ≤ V →
        |q0 ^ ((u:ℤ)-(k:ℤ)) *
          (u.descFactorial k : ℝ) / V^k| ≤ K := by
  classical
  have hfix (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ u : ℕ, |q0 ^ ((u:ℤ)-(k:ℤ)) *
        (u.descFactorial k : ℝ) / vmin^k| ≤ M :=
    single_group_weight_uniform k q0 vmin hq0 hq1 hv
  let M : ℕ → ℝ := fun k => (hfix k).choose
  have hM (k : ℕ) : 0 ≤ M k ∧
      ∀ u : ℕ, |q0 ^ ((u:ℤ)-(k:ℤ)) *
        (u.descFactorial k : ℝ) / vmin^k| ≤ M k :=
    (hfix k).choose_spec
  let K : ℝ := 1 + ∑ k ∈ Finset.Icc 0 tmax, M k
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 0 tmax, M k :=
    Finset.sum_nonneg (fun k _ => (hM k).1)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro k u V hk hV
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have hpow : vmin^k ≤ V^k := pow_le_pow_left₀ (le_of_lt hv) hV _
  have hnum : 0 ≤ q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) := by
    exact mul_nonneg (le_of_lt (zpow_pos hq0 _)) (Nat.cast_nonneg _)
  have hdiv : q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / V^k ≤
      q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / vmin^k :=
        div_le_div_of_nonneg_left hnum (pow_pos hv _) hpow
  have hposV : 0 ≤ q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / V^k :=
        div_nonneg hnum (le_of_lt (pow_pos hVpos _))
  have hposv : 0 ≤ q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / vmin^k :=
        div_nonneg hnum (le_of_lt (pow_pos hv _))
  rw [abs_of_nonneg hposV]
  calc
    _ ≤ q0 ^ ((u:ℤ)-(k:ℤ)) *
      (u.descFactorial k : ℝ) / vmin^k := hdiv
    _ ≤ M k := by
      simpa only [abs_of_nonneg hposv] using (hM k).2 u
    _ ≤ ∑ j ∈ Finset.Icc 0 tmax, M j := by
      apply Finset.single_le_sum
      · intro j hj
        exact (hM j).1
      · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,hk⟩
    _ ≤ K := by dsimp [K]; linarith
end Green64Analytic.CorrelationSquare

end

/-! ## code.UniformFullMarkedWeight -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The source W_t^b on a varying family of disjoint prime groups has
    a cap K^(#groups), where K depends ONLY on fixed q0,vmin,tmax. -/
theorem uniform_full_marked_weight
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {β : Type} [Fintype β] [DecidableEq β]
        (T : β → Finset ℕ) (t : β → ℕ) (V : β → ℝ)
        (b : (∀ g : β, Fin (t g) → ℕ) → ℂ),
        (∀ g, t g ≤ tmax) → (∀ g, vmin ≤ V g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ n : ℕ,
          ‖actualBigMarkDecoration T t q0 V b n‖ ≤
            K^(Fintype.card β) := by
  obtain ⟨K,hK,hKbound⟩ :=
    uniform_group_mark_bound q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro β _ _ T t V b ht hV hb n
  have hVpos (g : β) : 0 < V g := lt_of_lt_of_le hv (hV g)
  have hnonneg (g : β) :
      0 ≤ q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) *
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ) /
            (V g)^(t g) := by
    apply div_nonneg
    · exact mul_nonneg (le_of_lt (zpow_pos hq0 _)) (Nat.cast_nonneg _)
    · exact le_of_lt (pow_pos (hVpos g) _)
  classical
  calc
    _ ≤ ∏ g : β,
       (q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) *
          ((smallPrimeCount (T g) n).descFactorial (t g) : ℝ) /
            (V g)^(t g)) :=
      sourceBigMarkDecoration_pointwise T t q0 V b n hq0 hVpos hb
    _ ≤ ∏ _g : β, K := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact hnonneg g
      · intro g _
        have h := hKbound (t g) (smallPrimeCount (T g) n) (V g)
          (ht g) (hV g)
        simpa only [abs_of_nonneg (hnonneg g)] using h
    _ = K^(Fintype.card β) := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralWeightUniform -/

section

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open scoped BigOperators

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The *entire literal* source W_t^b, with a distinguished small
group, every other small group, and the genuine test of ordered BIG
marks, has a uniform K^(#small + #big + 1) bound.

Crucially K depends only on fixed q₀,v_-,tmax, and not on group
types, group count, mark locations, n or bounded test b. -/
theorem source_literal_weight_uniform_all_groups
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ)
        (k n : ℕ),
        k ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k n‖ ≤
           K^(Fintype.card ι + Fintype.card β + 1) := by
  obtain ⟨Ksmall, hKs, hBoundSmall⟩ :=
    uniform_group_mark_bound q0 vmin tmax hq0 hq1 hv
  obtain ⟨Kbig, hKb, hBoundBig⟩ :=
    uniform_full_marked_weight q0 vmin tmax hq0 hq1 hv
  let K : ℝ := max Ksmall Kbig
  have hK : 1 ≤ K := hKs.trans (le_max_left _ _)
  have hKS : Ksmall ≤ K := le_max_left _ _
  have hKB : Kbig ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k n
    hk hVs hts htb hVsmall hVbig hb
  have hS (J : Finset ℕ) (u : ℕ) (v : ℝ)
      (hu : u ≤ tmax) (hv2 : vmin ≤ v) (n2 : ℕ) :
      ‖((smallMarkedWeight J q0 v u n2 : ℝ) : ℂ)‖ ≤ K := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hh := hBoundSmall u (smallPrimeCount J n2) v hu hv2
    have hh' : |smallMarkedWeight J q0 v u n2| ≤ Ksmall := by
      simpa only [smallMarkedWeight, smallMarkKernel] using hh
    exact hh'.trans hKS

  have hOther : ‖otherGroupWeight (Finset.univ : Finset ι)
      Ts q0 Vsmall ts n‖ ≤ K^(Fintype.card ι) := by
    unfold otherGroupWeight
    rw [norm_prod]
    calc
      (∏ g ∈ (Finset.univ : Finset ι),
          ‖((smallMarkedWeight (Ts g) q0 (Vsmall g) (ts g) n : ℝ) : ℂ)‖) ≤
        ∏ _g ∈ (Finset.univ : Finset ι), K := by
           apply Finset.prod_le_prod₀
           · intro g hg
             exact norm_nonneg _
           · intro g hg
             exact hS (Ts g) (ts g) (Vsmall g)
                (hts g) (hVsmall g) n
      _ = K^(Fintype.card ι) := by simp
  have hBig : ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖ ≤
      K^(Fintype.card β) := by
    calc
      _ ≤ Kbig^(Fintype.card β) :=
        hBoundBig Tb tb Vbig b htb hVbig hb n
      _ ≤ K^(Fintype.card β) :=
        pow_le_pow_left₀ (by linarith) hKB _
  have hSelected :
      ‖((smallMarkedWeight S q0 Vs k n : ℝ) : ℂ)‖ ≤ K :=
    hS S k Vs hk hVs n
  have hnorm :
    ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k n‖ =
      ‖((smallMarkedWeight S q0 Vs k n : ℝ) : ℂ)‖ *
      (‖otherGroupWeight (Finset.univ : Finset ι)
         Ts q0 Vsmall ts n‖ *
       ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖) := by
    rw [← sourceMarkedWeight_eq_literal]
    simp only [sourceMarkedWeight, norm_mul]

  have hh :
      ‖((smallMarkedWeight S q0 Vs k n : ℝ) : ℂ)‖ *
      (‖otherGroupWeight (Finset.univ : Finset ι)
         Ts q0 Vsmall ts n‖ *
       ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖) ≤
      K*(K^(Fintype.card ι)*K^(Fintype.card β)) := by
    have hOpos : 0 ≤ ‖otherGroupWeight (Finset.univ : Finset ι)
         Ts q0 Vsmall ts n‖ := norm_nonneg _
    have hBpos : 0 ≤ ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖ :=
      norm_nonneg _
    calc
      _ ≤ K*(‖otherGroupWeight (Finset.univ : Finset ι)
          Ts q0 Vsmall ts n‖ *
         ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖) :=
           mul_le_mul_of_nonneg_right hSelected
             (mul_nonneg hOpos hBpos)
      _ ≤ K*(K^(Fintype.card ι)*
            ‖actualBigMarkDecoration Tb tb q0 Vbig b n‖) := by
           apply mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_right hOther hBpos)
             (by linarith)
      _ ≤ K*(K^(Fintype.card ι)*K^(Fintype.card β)) := by
           apply mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_left hBig (by positivity))
             (by linarith)
  calc
    _ = _ := hnorm
    _ ≤ K*(K^(Fintype.card ι)*K^(Fintype.card β)) := hh
    _ = K^(Fintype.card ι+Fintype.card β+1) := by
      rw [pow_add,pow_add]
      simp only [pow_one]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralGroupLogBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- The uniform literal source weight K^(all groups + distinguished
small group) has FIXED log-power size when both other-small and
BIG group counts are ≤ C0 logL. No K may depend on L. -/
theorem source_literal_group_card_log_budget_for_selected_correlations
    (K L C0 : ℝ) (hK : 1 ≤ K)
    (hL : 1 ≤ L) (hC0 : 0 ≤ C0)
    (nSmall nBig : ℕ)
    (hSmall : (nSmall:ℝ) ≤ C0*Real.log L)
    (hBig : (nBig:ℝ) ≤ C0*Real.log L) :
    K^(nSmall+nBig+1) ≤ K*L^(2*C0*Real.log K) := by
  have hKpos : 0 < K := by linarith
  have hLpos : 0 < L := by linarith
  have hCount : ((nSmall+nBig:ℕ):ℝ) ≤ (2*C0)*Real.log L := by
    push_cast
    linarith
  have hPower :
      K^(nSmall+nBig) ≤ K^((2*C0)*Real.log L) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hK hCount)
  have hSwap : K^((2*C0)*Real.log L) =
      L^(2*C0*Real.log K) := by
    rw [Real.rpow_def_of_pos hKpos,Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  calc
    K^(nSmall+nBig+1) = K*K^(nSmall+nBig) := by
      rw [pow_succ]
      ring
    _ ≤ K*K^((2*C0)*Real.log L) :=
      mul_le_mul_of_nonneg_left hPower (by linarith)
    _ = K*L^(2*C0*Real.log K) := by rw [hSwap]
end Green64Analytic.CorrelationSquare

end

/-! ## code.GroupLogPower -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- One uniform per-group constant costs only a fixed power of L when
    the total number of prime groups is O(log L). -/
theorem group_card_pow_le_log_power
    (K L C0 : ℝ) (s : ℕ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hC0 : 0 ≤ C0)
    (hsize : (s:ℝ) ≤ C0*Real.log L) :
    K^s ≤ L^(C0*Real.log K) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hK
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hKlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hmul : (s:ℝ)*Real.log K ≤
      (C0*Real.log L)*Real.log K :=
    mul_le_mul_of_nonneg_right hsize hKlog
  calc
    K^s = K^((s:ℕ):ℝ) := (Real.rpow_natCast K s).symm
    _ = Real.exp (Real.log K * (s:ℝ)) :=
      Real.rpow_def_of_pos hKpos _
    _ ≤ Real.exp (Real.log L * (C0*Real.log K)) := by
      apply (Real.exp_le_exp).2
      calc
        _ = (s:ℝ)*Real.log K := by ring
        _ ≤ (C0*Real.log L)*Real.log K := hmul
        _ = _ := by ring
    _ = L^(C0*Real.log K) :=
      (Real.rpow_def_of_pos hLpos _).symm
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceMarkedLogPower -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The original source sh:weight-bound, now kernel-derived for arbitrary
    bounded ordered-list tests and *changing* groups with |groups|≤C0 log L. -/
theorem source_marked_weight_log_power
    (q0 vmin C0 : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (L : ℝ), 1 ≤ L →
        ∀ {β : Type} [Fintype β] [DecidableEq β]
          (T : β → Finset ℕ) (t : β → ℕ) (V : β → ℝ)
          (b : (∀ g : β, Fin (t g) → ℕ) → ℂ),
            ((Fintype.card β : ℕ) : ℝ) ≤ C0*Real.log L →
            (∀ g, t g ≤ tmax) →
            (∀ g, vmin ≤ V g) →
            (∀ lists, ‖b lists‖ ≤ 1) →
            ∀ n : ℕ,
              ‖actualBigMarkDecoration T t q0 V b n‖ ≤ L^Cw := by
  obtain ⟨K,hK,hW⟩ :=
    uniform_full_marked_weight q0 vmin tmax hq0 hq1 hv
  have hCw : 0 ≤ C0*Real.log K :=
    mul_nonneg hC0 (Real.log_nonneg hK)
  refine ⟨C0*Real.log K,hCw,?_⟩
  intro L hL β _ _ T t V b hcount ht hV hb n
  calc
    _ ≤ K^(Fintype.card β) := hW T t V b ht hV hb n
    _ ≤ L^(C0*Real.log K) :=
      group_card_pow_le_log_power K L C0
        (Fintype.card β) hK hL hC0 hcount
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourcePhysicalSquareError -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Fully derived source square-exception L², with n_* and W^b both
    literal. The source group-size and coefficient hypotheses remain exact. -/
theorem source_physical_square_error
    (q0 vmin C0 : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (L : ℝ), 1 ≤ L →
        ∀ {β : Type} [Fintype β] [DecidableEq β]
          (T : β → Finset ℕ) (t : β → ℕ) (V : β → ℝ)
          (b : (∀ g : β, Fin (t g) → ℕ) → ℂ),
          ((Fintype.card β : ℕ) : ℝ) ≤ C0*Real.log L →
          (∀ g, t g ≤ tmax) → (∀ g, vmin ≤ V g) →
          (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (N P q : ℕ) (S primeSlot : Finset ℕ)
          (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C a : ℝ),
          0 ≤ A → 0 ≤ C →
          (∀ m, ‖α m‖ ≤ A) → (∀ r, ‖c r‖ ≤ C) →
          1 ≤ N → 1 ≤ P →
          S ⊆ Finset.Icc P (2*P) →
          S ⊆ (Finset.univ : Finset β).biUnion T →
          (∀ p ∈ S, p.Prime) →
          Real.exp (L^a)/2 ≤ (P:ℝ) →
          (∑ n ∈ sourceSquareExceptionalSupport N S,
             ‖sourceEndpoint
               (sourceOutsidePart ((Finset.univ : Finset β).biUnion T))
               (actualBigMarkDecoration T t q0 V b)
               primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
          4*(A*C*L^Cw)^2*(N:ℝ)*
            (1+Real.log (N:ℝ))^16*Real.exp (-(L^a)) := by
  obtain ⟨Cw,hCw,hcap⟩ :=
    source_marked_weight_log_power q0 vmin C0 tmax
      hq0 hq1 hv hC0
  refine ⟨Cw,hCw,?_⟩
  intro L hL β _ _ T t V b hcount ht hV hb N P q S primeSlot
    α c χ σ₀ σ₁ A C a hA hC hα hc hN hP hS hGroup hPrime hLow
  have hB : 0 ≤ L^Cw := by positivity
  exact literalCoreSquareUnionMass
    ((Finset.univ : Finset β).biUnion T) S
    (actualBigMarkDecoration T t q0 V b)
    primeSlot α c N q P χ σ₀ σ₁ A C (L^Cw) L a
    hA hC hB hα hc hN hP hS hGroup hPrime hLow
    (fun n _ => hcap L hL T t V b hcount ht hV hb n)
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceScaleBudget -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Source hypotheses turn the exact finite error into Y times a log
    power with an explicit constant, without asymptotic shortcuts. -/
theorem source_square_scale_budget (L Y N A C Cw E D a : ℝ)
    (hL : 1 ≤ L) (hY : 0 ≤ Y) (hN : 1 ≤ N) (hNY : N ≤ Y)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hAb : A ≤ L^E) (hCb : C ≤ L^E)
    (hlog : Real.log N ≤ D*L) :
    4*(A*C*L^Cw)^2*N*(1+Real.log N)^16*
       Real.exp (-(L^a)) ≤
    4*(1+D)^16*Y*L^(4*E+2*Cw+16)*
       Real.exp (-(L^a)) := by
  have hLpos : 0 < L := by linarith
  have hDpos : 0 ≤ 1+D := by linarith
  have hlog0 : 0 ≤ 1+Real.log N :=
    by linarith [Real.log_nonneg hN]
  have hlogLarge : 1+Real.log N ≤ (1+D)*L := by nlinarith [hlog]
  have hp : 0 ≤ L^E := by positivity
  calc
    _ ≤ 4*((L^E*L^E*L^Cw)^2)*Y*(((1+D)*L)^16)*
         Real.exp (-(L^a)) := by
           gcongr
    _ = _ := by
      rw [mul_pow]
      have hmul : L^E*L^E*L^Cw = L^(2*E+Cw) := by
        calc
          _ = L^(E+E)*L^Cw := by
            rw [Real.rpow_add hLpos E E]
          _ = L^((E+E)+Cw) :=
            (Real.rpow_add hLpos (E+E) Cw).symm
          _ = L^(2*E+Cw) := by congr 1; ring
      have hpow : (L^E*L^E*L^Cw)^2 * L^16 =
          L^(4*E+2*Cw+16) := by
        calc
          _ = (L^(2*E+Cw))^2 * L^16 := by rw [hmul]
          _ = L^((2*E+Cw)*2) * L^(16:ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLpos)]
            norm_num
          _ = L^((2*E+Cw)*2+16) :=
            (Real.rpow_add hLpos _ _).symm
          _ = L^(4*E+2*Cw+16) := by congr 1; ring
      calc
        _ = 4*(1+D)^16*Y*
          ((L^E*L^E*L^Cw)^2*L^16)*Real.exp (-(L^a)) := by ring
        _ = _ := by rw [hpow]
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourcePhysicalSquareScaled -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Source small-square-error with its final physical Y*L^C format.
    All numerical source parameters are fixed before the group/frequency
    choices, and no long-prime or classical character theorem is assumed. -/
theorem source_physical_square_error_scaled
    (q0 vmin C0 E D : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (L : ℝ), 1 ≤ L →
        ∀ {β : Type} [Fintype β] [DecidableEq β]
          (T : β → Finset ℕ) (t : β → ℕ) (V : β → ℝ)
          (b : (∀ g : β, Fin (t g) → ℕ) → ℂ),
          ((Fintype.card β : ℕ) : ℝ) ≤ C0*Real.log L →
          (∀ g, t g ≤ tmax) → (∀ g, vmin ≤ V g) →
          (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (N P q : ℕ) (S primeSlot : Finset ℕ)
          (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C a Y : ℝ),
          0 ≤ A → 0 ≤ C →
          (∀ m, ‖α m‖ ≤ A) → (∀ r, ‖c r‖ ≤ C) →
          1 ≤ N → 1 ≤ P →
          S ⊆ Finset.Icc P (2*P) →
          S ⊆ (Finset.univ : Finset β).biUnion T →
          (∀ p ∈ S, p.Prime) →
          Real.exp (L^a)/2 ≤ (P:ℝ) →
          (N : ℝ) ≤ Y →
          A ≤ L^E → C ≤ L^E →
          Real.log (N:ℝ) ≤ D*L →
          (∑ n ∈ sourceSquareExceptionalSupport N S,
             ‖sourceEndpoint
               (sourceOutsidePart ((Finset.univ : Finset β).biUnion T))
               (actualBigMarkDecoration T t q0 V b)
               primeSlot α c q χ σ₀ σ₁ n‖^2) ≤
          4*(1+D)^16*Y*L^(4*E+2*Cw+16)*
            Real.exp (-(L^a)) := by
  obtain ⟨Cw,hCw,hphys⟩ :=
    source_physical_square_error q0 vmin C0 tmax hq0 hq1 hv hC0
  refine ⟨Cw,hCw,?_⟩
  intro L hL β _ _ T t V b hcount ht hV hb N P q S primeSlot
    α c χ σ₀ σ₁ A C a Y hA hC hα hc hN hP hS hGroup hPrime
    hLow hNY hAb hCb hlog
  have hY : 0 ≤ Y := by
    have hNreal : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  calc
    _ ≤ 4*(A*C*L^Cw)^2*(N:ℝ)*
      (1+Real.log (N:ℝ))^16*Real.exp (-(L^a)) :=
        hphys L hL T t V b hcount ht hV hb N P q S primeSlot
          α c χ σ₀ σ₁ A C a hA hC hα hc hN hP hS hGroup
          hPrime hLow
    _ ≤ _ := source_square_scale_budget L Y (N:ℝ)
        A C Cw E D a hL hY
        (by exact_mod_cast hN) hNY hA hC hE hD hAb hCb hlog
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralPeelingScale -/

section

namespace Green64Analytic.CorrelationSquare

/-- Literal source peeling error's extra mark-count factor
B·L·(1+D/(v_- log2)) is a fixed L-power, provided the other-small
and big group counts are O(log L). No group-dependent constant
is slipped into the O-notation. -/
theorem source_literal_peeling_logpower_budget
    (K L C0 D vmin : ℝ)
    (nSmall nBig : ℕ)
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hC0 : 0 ≤ C0) (hD : 0 ≤ D) (hv : 0 < vmin)
    (hSmall : (nSmall:ℝ) ≤ C0*Real.log L)
    (hBig : (nBig:ℝ) ≤ C0*Real.log L)
    (hLarge : K*(1+D/(vmin*Real.log 2)) ≤ L) :
    K^(nSmall+nBig+1)*L*(1+D/(vmin*Real.log 2)) ≤
      L^(2*C0*Real.log K+2) := by
  have hLp : 0 < L := by linarith
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1:ℝ)<2)
  let e : ℝ := 2*C0*Real.log K
  let M : ℝ := 1+D/(vmin*Real.log 2)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hEpos : 0 ≤ L^e := (Real.rpow_pos_of_pos hLp e).le
  have hCards := source_literal_group_card_log_budget_for_selected_correlations
    K L C0 hK hL hC0 nSmall nBig hSmall hBig
  have hBound :
      K^(nSmall+nBig+1)*L*M ≤ (K*L^e)*L*M := by
    have hCards' : K^(nSmall+nBig+1) ≤ K*L^e := by
      simpa only [e] using hCards
    have hStep : K^(nSmall+nBig+1)*L ≤ (K*L^e)*L :=
      mul_le_mul_of_nonneg_right hCards' (by linarith)
    exact mul_le_mul_of_nonneg_right hStep hM
  have hTarget : L*(L^e*L) = L^(e+2) := by
    rw [Real.rpow_add hLp]
    norm_num
    ring
  calc
    K^(nSmall+nBig+1)*L*M ≤ (K*L^e)*L*M := hBound
    _ = (K*M)*(L^e*L) := by ring
    _ ≤ L*(L^e*L) := mul_le_mul_of_nonneg_right
      (by simpa only [M] using hLarge) (by positivity)
    _ = L^(e+2) := hTarget
    _ = L^(2*C0*Real.log K+2) := rfl
end Green64Analytic.CorrelationSquare

end

