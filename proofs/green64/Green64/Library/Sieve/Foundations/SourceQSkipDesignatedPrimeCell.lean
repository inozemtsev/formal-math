module

public import Green64.Library.Weights.Part097
public import Mathlib

@[expose] public section

/-!
# Sieve / Foundations / SourceQSkipDesignatedPrimeCell

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceQSkipDesignatedPrimeCell -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The literal original designated Q slot with its inclusive endpoints
is exactly the prime integers in its original real closed log interval.
In particular, the source comparison primeSlot is not a proxy sample. -/
theorem source_actual_designated_Q_prime_interval434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (p : ℕ) :
    p ∈ sourceOriginalQActualBands r d L b ↔
      p.Prime ∧ (p:ℝ) ∈
        Set.Icc (Real.exp (sourceOriginalQActualExponent r b.val * L))
          (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent r b.val * L)) := by
  constructor
  · intro hp
    obtain ⟨hI,hPrime⟩ := Finset.mem_filter.mp hp
    have hEnds := Finset.mem_Icc.mp hI
    refine ⟨hPrime, ?_⟩
    exact Set.mem_Icc.mpr
      ⟨(Nat.ceil_le).1 hEnds.1,
        (by
          have hcast : (p:ℝ) ≤
              (⌊Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent r b.val * L)⌋₊:ℝ) := by
            exact_mod_cast hEnds.2
          exact hcast.trans (Nat.floor_le (Real.exp_nonneg _)))⟩
  · intro hp
    obtain ⟨hprime, hrange⟩ := hp
    have hEnds := Set.mem_Icc.mp hrange
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,hprime⟩
    · exact (Nat.ceil_le).2 hEnds.1
    · exact Nat.le_floor hEnds.2

/-- The original Q-prime real interval is order-connected, as required
for SourceComparisonData434.hI. -/
theorem source_actual_designated_Q_interval_connected434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) :
    Set.OrdConnected
      (Set.Icc (Real.exp (sourceOriginalQActualExponent r b.val * L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent r b.val * L))) := by
  exact Set.ordConnected_Icc
/-- The original source tau and eta are the two actual Q_j endpoints.
At x=exp L they coincide literally with the SourceComparisonData434
prime-slot bounding interval; neither exponent is reselected. -/
theorem source_actual_Q_Icc_eq_exp_power_band434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) :
    Set.Icc (Real.exp (sourceOriginalQActualExponent r b.val * L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent r b.val * L)) =
      Set.Icc ((Real.exp L)^(sourceOriginalQActualExponent r b.val))
        ((Real.exp L)^((6/5:ℝ)*sourceOriginalQActualExponent r b.val)) := by
  simp only [Real.rpow_def_of_pos (Real.exp_pos L),
    Real.log_exp]
  congr 1 <;> ring
end Green64Analytic.SourceBlockSieve

end

end

