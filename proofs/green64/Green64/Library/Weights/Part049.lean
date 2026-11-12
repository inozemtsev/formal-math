module

public import Green64.Library.Weights.Part048
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Green64.Library.Analysis.Estimates.Part011
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part047
public import Green64.Library.Weights.Part046
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Green64.Library.Weights.Part017
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Weights.Part042
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part016

@[expose] public section

/-!
# Weights / Part049

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalChebyshev64PowerMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 350000

/-- The actual real log 64 is between 0 and 6. -/
theorem source_original_log64_bounds434 :
    0 < Real.log (64:ℝ) ∧ Real.log (64:ℝ) ≤ 6 := by
  have hh : Real.log (64:ℝ) = 3*Real.log (4:ℝ) := by
    convert (Real.log_pow (4:ℝ) 3) using 1 <;> norm_num
  constructor
  · exact Real.log_pos (by norm_num)
  · rw [hh]
    linarith [source_original_log_four_le_two434]

/-- Original true band arithmetic endpoint for u=64^K. -/
theorem source_original_TRUE_geometric64_power_cut434
    (K i : ℕ) :
    sourceOriginalChebyshevGeometricCut434 (64^K) i =
      64^(K+i) := by
  simp [sourceOriginalChebyshevGeometricCut434,pow_add]

/-- Every block u_i=64^(K+i) with K>=2 is indeed >=512. -/
theorem source_original_TRUE_geometric64_power_large434
    (K i : ℕ) (hK : 2 ≤ K) :
    512 ≤ sourceOriginalChebyshevGeometricCut434 (64^K) i := by
  rw [source_original_TRUE_geometric64_power_cut434]
  have hpow : 64^2 ≤ 64^(K+i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hpow
  omega

/-- For a real Fourier/prime block u_i=64^(K+i),
the exact explicit reciprocal-log lower bound is at least
1/(96*(K+i+1)). This is a REAL arithmetic estimate, not a
heuristic asymptotic approximation. -/
theorem source_original_TRUE_geometric64_log_reciprocal434
    (K i : ℕ) (hK : 2 ≤ K) :
    (1:ℝ)/(96*((K+i+1:ℕ):ℝ)) ≤
      (1:ℝ)/(16*Real.log
        (sourceOriginalChebyshevGeometricCut434 (64^K) i:ℝ)) := by
  have hlog64 := source_original_log64_bounds434
  have hki : (0:ℝ) < ((K+i:ℕ):ℝ) := by exact_mod_cast (show 0 < K+i by omega)
  have hlog :
      Real.log
        (sourceOriginalChebyshevGeometricCut434 (64^K) i:ℝ) =
      ((K+i:ℕ):ℝ)*Real.log (64:ℝ) := by
    rw [source_original_TRUE_geometric64_power_cut434]
    simp only [Nat.cast_pow, Nat.cast_ofNat,Real.log_pow]
  have hdenpos : 0 < 16*Real.log
      (sourceOriginalChebyshevGeometricCut434 (64^K) i:ℝ) := by
    rw [hlog]
    positivity
  have hden : 16*Real.log
      (sourceOriginalChebyshevGeometricCut434 (64^K) i:ℝ) ≤
      96*((K+i+1:ℕ):ℝ) := by
    rw [hlog]
    have hmul := mul_le_mul_of_nonneg_left hlog64.2 hki.le
    have hcast : (((K+i+1:ℕ):ℝ)) = ((K+i:ℕ):ℝ)+1 := by norm_num
    rw [hcast]
    nlinarith
  exact one_div_le_one_div_of_le hdenpos hden
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64Harmonic -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 280000

/-- TRUE finite harmonic sum from the Kth to (K+N)th term.
All indexing offsets are explicit; no asymptotic approximation. -/
theorem source_original_harmonic_range_exact434 (K N : ℕ) :
    (∑ i ∈ Finset.range N, (1:ℝ)/((K+i+1:ℕ):ℝ)) =
      (harmonic (K+N):ℝ)-(harmonic K:ℝ) := by
  have h : harmonic (K+N) =
      harmonic K +
        ∑ i ∈ Finset.range N,
          (((K+i+1:ℕ):ℚ)⁻¹) := by
    simpa only [harmonic,Nat.add_assoc] using
      (Finset.sum_range_add
        (fun j : ℕ => (((j+1:ℕ):ℚ)⁻¹)) K N)
  have hr := congrArg (fun r : ℚ => (r:ℝ)) h
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_inv,
    Rat.cast_natCast] at hr
  simp only [one_div]
  linarith

/-- Logarithmic lower bound on the genuine truncated reciprocal
sum. This is a rigorously checked harmonic-integer theorem,
not a heuristic integral replacement. -/
theorem source_original_harmonic_range_log_lower434
    (K N : ℕ) :
    Real.log ((K+N+1:ℕ):ℝ) - 1 -
      Real.log (K:ℝ) ≤
    ∑ i ∈ Finset.range N, (1:ℝ)/((K+i+1:ℕ):ℝ) := by
  rw [source_original_harmonic_range_exact434]
  have hlo := log_add_one_le_harmonic (K+N)
  have hhi := harmonic_le_one_add_log K
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64LogMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 320000

/-- Unconditional Mertens-TYPE logarithmic lower bound on the
TRUE reciprocal mass of primes in (64^K,64^(K+N)].
All constants are explicit but very weak, derived from
Mathlib Chebyshev plus the rigorous harmonic-number estimates.
The frequency-band source primes are not modified or enlarged. -/
theorem source_original_TRUE_geometric_prime_mass_log_lower434
    (K N : ℕ) (hK : 2 ≤ K) :
    (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 ≤
    sourceOriginalPrimeBandHarmonicMass434 (64^K)
      (64^(K+N)) := by
  have hbase : 512 ≤ 64^K := by
    simpa only [sourceOriginalChebyshevGeometricCut434,
      pow_zero,mul_one] using
      (source_original_TRUE_geometric64_power_large434 K 0 hK)
  have hgeom := source_original_TRUE_prime_harmonic_geometric_sum434
    (64^K) N hbase
  have hcut := source_original_TRUE_geometric64_power_cut434 K N
  rw [hcut] at hgeom
  have hcomparison :
      (∑ i ∈ Finset.range N,
        (1:ℝ)/(96*((K+i+1:ℕ):ℝ))) ≤
      (∑ i ∈ Finset.range N,
        (1:ℝ)/(16*Real.log
          (sourceOriginalChebyshevGeometricCut434 (64^K) i:ℝ))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact source_original_TRUE_geometric64_log_reciprocal434 K i hK
  have hlog := source_original_harmonic_range_log_lower434 K N
  have hscaled :
      (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 ≤
        ∑ i ∈ Finset.range N,
          (1:ℝ)/(96*((K+i+1:ℕ):ℝ)) := by
    have hh := div_le_div_of_nonneg_right hlog (by norm_num : (0:ℝ) ≤ 96)
    calc
      _ ≤ (∑ i ∈ Finset.range N,
          (1:ℝ)/((K+i+1:ℕ):ℝ))/96 := hh
      _ = ∑ i ∈ Finset.range N,
          (1:ℝ)/(96*((K+i+1:ℕ):ℝ)) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  exact hscaled.trans (hcomparison.trans hgeom)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64TrueFullBigGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 180000

/-- Source03 BIG groups constructed as FULL consecutive prime
intervals from the now UNCONDITIONALLY PROVED Chebyshev
power-64 prime harmonic lower bound. The numerical budget is
explicit; no hypothetical prime-distribution estimate or
pre-existing family of groups appears. -/
theorem source_original_TRUE_chebyshev64_full_BIG_groups434
    (K N n : ℕ) (hK : 2 ≤ K)
    (target δ : ℝ) (htarget : 0 < target)
    (hδ : (1:ℝ)/(((64^K:ℕ)+1:ℕ):ℝ) ≤ δ)
    (hBudget : (n:ℝ)*(target+δ) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-Real.log (K:ℝ)-1)/96) :
    ∃ (left right : Fin n → ℕ),
      (∀ i, 64^K ≤ left i ∧
        left i < right i ∧ right i ≤ 64^(K+N)) ∧
      (∀ i, target ≤ sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) ∧
        sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) < target+δ) ∧
      (∀ i j, i≠j →
        Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) := by
  have hle : (64^K:ℕ) ≤ 64^(K+N) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmass : (n:ℝ)*(target+δ) ≤
      sourceOriginalPrimeBandHarmonicMass434 (64^K) (64^(K+N)) := by
    have hCheb :=
      source_original_TRUE_geometric_prime_mass_log_lower434 K N hK
    have heq :
        (Real.log ((K+N+1:ℕ):ℝ)-Real.log (K:ℝ)-1)/96 =
        (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 := by ring
    rw [heq] at hBudget
    exact hBudget.trans hCheb
  exact source_original_TRUE_full_prime_interval_groups434
    n (64^K) (64^(K+N)) hle
    target δ htarget hδ hmass
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64FullBIGExpGeometry -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 160000

/-- The EXACT original source03 BIG geometry with all primes in
each integer interval, and every selected prime lying inside
[exp(L^c), exp(L^d)]. Uses only explicit NUMERICAL band and
harmonic-budget inequalities plus the unconditional Mathlib
Chebyshev lower bound already proved above.
No hypothetical BIG group family or incomplete prime interval. -/
theorem source_original_TRUE_chebyshev64_source03_FULL_BIG_exp_geometry434
    (K N n : ℕ) (hK : 2 ≤ K)
    (L c d target δ : ℝ) (htarget : 0 < target)
    (hStart : Real.exp (L^c) ≤ ((64^K:ℕ):ℝ))
    (hEnd : ((64^(K+N):ℕ):ℝ) ≤ Real.exp (L^d))
    (hδ : (1:ℝ)/(((64^K:ℕ)+1:ℕ):ℝ) ≤ δ)
    (hBudget : (n:ℝ)*(target+δ) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-Real.log (K:ℝ)-1)/96) :
    ∃ (left right : Fin n → ℕ),
      (∀ i, left i < right i) ∧
      (∀ i p,
        p ∈ sourceOriginalActualPrimeBand434 (left i) (right i) →
        p.Prime ∧ Real.exp (L^c) ≤ (p:ℝ) ∧
          (p:ℝ) ≤ Real.exp (L^d)) ∧
      (∀ i, target ≤ sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) ∧
        sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) < target+δ) ∧
      (∀ i j, i≠j →
        Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) := by
  obtain ⟨left,right,hrange,hmass,hdisj⟩ :=
    source_original_TRUE_chebyshev64_full_BIG_groups434
      K N n hK target δ htarget hδ hBudget
  refine ⟨left,right,(fun i => (hrange i).2.1),?_,hmass,hdisj⟩
  intro i p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hbounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hlow : Real.exp (L^c) ≤ (p:ℝ) := by
    have ha : ((64^K:ℕ):ℝ) ≤ (left i:ℝ) := by
      exact_mod_cast (hrange i).1
    have hb : (left i:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast hbounds.1.le
    exact (hStart.trans ha).trans hb
  have hhigh : (p:ℝ) ≤ Real.exp (L^d) := by
    have ha : (p:ℝ) ≤ (right i:ℝ) := by
      exact_mod_cast hbounds.2
    have hb : (right i:ℝ) ≤ ((64^(K+N):ℕ):ℝ) := by
      exact_mod_cast (hrange i).2.2
    exact (ha.trans hb).trans hEnd
  exact ⟨hprime,hlow,hhigh⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64TrueSmallGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 260000

/-- True SMALL family from FULLY PROVED prime distribution:
only an EXPLICIT ELEMENTARY inequality on integer K,N,n remains
to check. There is no prime-harmonic sum premise, no group-existence
premise, and no assumption of a Mertens theorem. -/
theorem source_original_TRUE_chebyshev64_log_SMALL_groups434
    (K N n : ℕ) (hK : 2 ≤ K)
    (vmin : ℝ) (hvmin : 0 < vmin)
    (hBudget :
      ((n+1:ℕ):ℝ) *
          (vmin+1/(((64^K:ℕ)+1):ℝ)) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96) :
    ∃ (P : Option (Fin n) → Finset ℕ)
      (V : Option (Fin n) → ℝ),
      (∀ g, (P g).Nonempty) ∧
      (∀ g p, p ∈ P g →
          p.Prime ∧ 64^K < p ∧ p ≤ 64^(K+N)) ∧
      (∀ g, V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ)) ∧
      (∀ g, vmin ≤ V g ∧
        V g < vmin+1/(((64^K:ℕ)+1):ℝ)) ∧
      (∀ g h, g≠h → Disjoint (P g) (P h)) := by
  let u := 64^K
  let v := 64^(K+N)
  have hmass : ((n+1:ℕ):ℝ)*(vmin+1/((u+1:ℕ):ℝ)) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v := by
    simpa only [u,v,Nat.cast_add,Nat.cast_one] using
      (hBudget.trans
        (source_original_TRUE_geometric_prime_mass_log_lower434 K N hK))
  obtain ⟨blocks,hsub,hbound,hdisj⟩ :=
    source_original_ACTUAL_small_band_prime_groups434
      u v (n+1) (Nat.zero_lt_succ u) vmin hvmin hmass
  let index := sourceOriginalChebyshevSmallIndex434 n
  let P : Option (Fin n) → Finset ℕ := fun g => blocks (index g)
  let V : Option (Fin n) → ℝ := fun g =>
    ∑ p ∈ P g, (1:ℝ)/(p:ℝ)
  refine ⟨P,V,?_,?_,?_,?_,?_⟩
  · intro g
    exact (hbound (index g)).1
  · intro g p hp
    rcases Finset.mem_filter.mp (hsub (index g) hp) with ⟨hband,hprime⟩
    have hbounds := Finset.mem_Ioc.mp hband
    exact ⟨hprime,hbounds.1,hbounds.2⟩
  · intro g
    rfl
  · intro g
    simpa only [P,V,u,Nat.cast_add,Nat.cast_one] using
      (hbound (index g)).2
  · intro g h hneq
    apply hdisj (index g) (index h)
    intro he
    exact hneq ((source_original_chebyshev_small_index_injective434 n) he)

/-- Original SMALL source03 exponential prime support, genuine
harmonic normalization and pairwise separation, conditional only
on explicit NUMERICAL inequalities relating K,N and L. -/
theorem source_original_TRUE_chebyshev64_source03_exp_groups434
    (K N n : ℕ) (hK : 2 ≤ K)
    (L a b : ℝ) (vmin : ℝ) (hvmin : 0 < vmin)
    (hRangeStart : Real.exp (L^a) ≤ ((64^K:ℕ):ℝ))
    (hRangeEnd : ((64^(K+N):ℕ):ℝ) ≤ Real.exp (L^b))
    (hBudget :
      ((n+1:ℕ):ℝ) *
          (vmin+1/(((64^K:ℕ)+1):ℝ)) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96) :
    ∃ (P : Option (Fin n) → Finset ℕ)
      (V : Option (Fin n) → ℝ),
      (∀ g, (P g).Nonempty) ∧
      (∀ g p, p ∈ P g →
          p.Prime ∧ Real.exp (L^a) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (L^b)) ∧
      (∀ g, V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ)) ∧
      (∀ g, vmin ≤ V g ∧
        V g < vmin+1/(((64^K:ℕ)+1):ℝ)) ∧
      (∀ g h, g≠h → Disjoint (P g) (P h)) := by
  obtain ⟨P,V,hne,hband,hmass,hbound,hdisj⟩ :=
    source_original_TRUE_chebyshev64_log_SMALL_groups434
      K N n hK vmin hvmin hBudget
  refine ⟨P,V,hne,?_,hmass,hbound,hdisj⟩
  intro g p hp
  obtain ⟨hprime,hlo,hhi⟩ := hband g p hp
  have hloR : Real.exp (L^a) ≤ (p:ℝ) := by
    have hcast : ((64^K:ℕ):ℝ) < (p:ℝ) := by
      exact_mod_cast hlo
    exact hRangeStart.trans hcast.le
  have hhiR : (p:ℝ) ≤ Real.exp (L^b) := by
    have hcast : (p:ℝ) ≤ ((64^(K+N):ℕ):ℝ) := by
      exact_mod_cast hhi
    exact hcast.trans hRangeEnd
  exact ⟨hprime,hloR,hhiR⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64JointSource03Geometry -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 220000

/-- The original strictly separated source03 SMALL and BIG
exponential prime bands cannot share any real prime label.
This proof uses the ACTUAL power exponents b<c and L>1. -/
theorem source_original_source03_exponential_bands_separated434
    (L b c : ℝ) (hL : 1 < L) (hbc : b < c) :
    Real.exp (L^b) < Real.exp (L^c) :=
  Real.exp_lt_exp.mpr
    (Real.rpow_lt_rpow_of_exponent_lt hL hbc)

/-- Under ONLY explicit elementary integer-power64 window
and harmonic-budget inequalities, constructs the TRUE
original source03 S + Ts + Tb prime-group geometry:
  * S and each Ts is a nonempty set of actual SMALL primes
    with exact harmonic mass,
  * each Tb is ALL primes of a full BIG integer interval,
  * EVERY SMALL-SMALL, BIG-BIG and SMALL-BIG pair is disjoint,
  * the selected primes lie in the ORIGINAL distinct bands
    [exp(L^a),exp(L^b)] and [exp(L^c),exp(L^d)].
No pre-existing group family is assumed. The explicit numerical
budgets and boundary placement for fixed moving L are STILL to
be discharged; signed physical transference is NOT proved. -/
theorem source_original_TRUE_source03_full_joint_prime_geometry434
    (KS NS nS KB NB nB : ℕ) (hKS : 2 ≤ KS) (hKB : 2 ≤ KB)
    (L a b c d vS vB : ℝ)
    (hL : 1 < L) (hbc : b < c)
    (hvS : 0 < vS) (hvB : 0 < vB)
    (hSmallStart : Real.exp (L^a) ≤ ((64^KS:ℕ):ℝ))
    (hSmallEnd : ((64^(KS+NS):ℕ):ℝ) ≤ Real.exp (L^b))
    (hBigStart : Real.exp (L^c) ≤ ((64^KB:ℕ):ℝ))
    (hBigEnd : ((64^(KB+NB):ℕ):ℝ) ≤ Real.exp (L^d))
    (hSmallBudget :
      (((nS+1:ℕ):ℝ)) *
        (vS+1/(((64^KS:ℕ):ℝ)+1)) ≤
      (Real.log ((KS+NS+1:ℕ):ℝ)-1-Real.log (KS:ℝ))/96)
    (hBigBudget :
      (nB:ℝ) * (vB+1/(((64^KB:ℕ)+1:ℕ):ℝ)) ≤
      (Real.log ((KB+NB+1:ℕ):ℝ)-Real.log (KB:ℝ)-1)/96) :
    ∃ (P : Option (Fin nS) → Finset ℕ)
      (V : Option (Fin nS) → ℝ)
      (left right : Fin nB → ℕ),
      (∀ g, (P g).Nonempty ∧
        V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ) ∧
        vS ≤ V g ∧ V g < vS+1/(((64^KS:ℕ):ℝ)+1)) ∧
      (∀ g p, p∈P g →
        p.Prime ∧ Real.exp (L^a) ≤ (p:ℝ) ∧
          (p:ℝ) ≤ Real.exp (L^b)) ∧
      (∀ i, left i < right i ∧
        vB ≤ sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) ∧
        sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) <
          vB+1/(((64^KB:ℕ)+1:ℕ):ℝ)) ∧
      (∀ i p,
        p ∈ sourceOriginalActualPrimeBand434 (left i) (right i) →
        p.Prime ∧ Real.exp (L^c) ≤ (p:ℝ) ∧
          (p:ℝ) ≤ Real.exp (L^d)) ∧
      (∀ g h, g≠h → Disjoint (P g) (P h)) ∧
      (∀ i j, i≠j → Disjoint
        (sourceOriginalActualPrimeBand434 (left i) (right i))
        (sourceOriginalActualPrimeBand434 (left j) (right j))) ∧
      (∀ g i, Disjoint (P g)
        (sourceOriginalActualPrimeBand434 (left i) (right i))) := by
  classical
  have hgap :=
    source_original_source03_exponential_bands_separated434 L b c hL hbc
  obtain ⟨P,V,hSne,hSband,hSV,hSmass,hSdisj⟩ :=
    source_original_TRUE_chebyshev64_source03_exp_groups434
      KS NS nS hKS L a b vS hvS
      hSmallStart hSmallEnd hSmallBudget
  obtain ⟨left,right,hBrange,hBband,hBmass,hBdisj⟩ :=
    source_original_TRUE_chebyshev64_source03_FULL_BIG_exp_geometry434
      KB NB nB hKB L c d vB
      (1/(((64^KB:ℕ)+1:ℕ):ℝ)) hvB hBigStart hBigEnd
      le_rfl hBigBudget
  refine ⟨P,V,left,right,?_,hSband,?_,hBband,hSdisj,hBdisj,?_⟩
  · intro g
    exact ⟨hSne g,hSV g,(hSmass g).1,(hSmass g).2⟩
  · intro i
    exact ⟨hBrange i,(hBmass i).1,(hBmass i).2⟩
  · intro g i
    apply Finset.disjoint_left.mpr
    intro p hSP hBP
    have hpS := (hSband g p hSP).2.2
    have hpB := (hBband i p hBP).2.1
    exact (not_le_of_gt hgap) (hpB.trans hpS)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevPower64RoundedBands -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- True power-64 integer prime endpoints agree EXACTLY with
their real exponential logarithmic values. -/
theorem source_original_true_power64_real_exp434 (K : ℕ) :
    (((64^K:ℕ):ℝ)) = Real.exp ((K:ℝ)*Real.log 64) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<64)]
  norm_cast

/-- Mathlib compatible elementary lower and upper bounds for
the natural power-64 lattice spacing. -/
theorem source_original_true_log64_between_one_six434 :
    (1:ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ 6 := by
  have hh : Real.log (64:ℝ) = 6*Real.log (2:ℝ) := by
    conv_lhs => rw [show (64:ℝ) = 2^6 by norm_num]
    rw [Real.log_pow]
    ring
  rw [hh]
  have lo := (source_original_log_two_bounds434).1
  have hi := (source_original_log_two_bounds434).2
  constructor <;> nlinarith

/-- Given an explicit real band of log-prime scales r and s
with s >= 24r and r>=2, construct ACTUAL INTEGER cutoffs
K, K+N by rounding: K=ceil(r), K+N=floor(s/6).
These power64 endpoints really lie INSIDE [exp r,exp s].
Their logarithmic ratio is bounded below by exact
real logarithms of s/6 and 2r. No prime groups assumed. -/
theorem source_original_true_rounded_power64_band434
    (r s : ℝ) (hr : 2 ≤ r) (hs : 24*r ≤ s) :
    ∃ (K N : ℕ), 2 ≤ K ∧
      Real.exp r ≤ (((64^K:ℕ):ℝ)) ∧
      (((64^(K+N):ℕ):ℝ)) ≤ Real.exp s ∧
      Real.log (s/6)-Real.log (2*r) ≤
        Real.log ((K+N+1:ℕ):ℝ) - Real.log (K:ℝ) := by
  let K := Nat.ceil r
  let E := Nat.floor (s/6)
  have hrpos : (0:ℝ) ≤ r := by linarith
  have hspos : (0:ℝ) < s := by nlinarith
  have hKlower : r ≤ (K:ℝ) := Nat.le_ceil r
  have hK : 2 ≤ K := by
    exact_mod_cast (hr.trans hKlower)
  have hKupper : (K:ℝ) < r+1 := Nat.ceil_lt_add_one hrpos
  have hEupper : (E:ℝ) ≤ s/6 := Nat.floor_le (by positivity)
  have hElower : s/6 < (E:ℝ)+1 := Nat.lt_floor_add_one _
  have hKE : K ≤ E := by
    apply (Nat.ceil_le).2
    have hround : r ≤ (E:ℝ) := by
      have hratio : 4*r ≤ s/6 := by linarith
      linarith
    exact hround
  let N := E-K
  have hKN : K+N=E := by dsimp [N]; omega
  have hlog64 := source_original_true_log64_between_one_six434
  have hKpos : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg _
  have hEpos : (0:ℝ) ≤ (E:ℝ) := Nat.cast_nonneg _
  have hStartExp : r ≤ (K:ℝ)*Real.log 64 := by
    have hh : (K:ℝ) ≤ (K:ℝ)*Real.log 64 :=
      by simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hlog64.1 hKpos)
    exact hKlower.trans hh
  have hEndExp : (E:ℝ)*Real.log 64 ≤ s := by
    have hh : (E:ℝ)*Real.log 64 ≤ (E:ℝ)*6 :=
      mul_le_mul_of_nonneg_left hlog64.2 hEpos
    linarith
  have hK1 : (K:ℝ) ≤ 2*r := by linarith
  have hE1 : s/6 ≤ ((E+1:ℕ):ℝ) := by
    have h := hElower
    norm_num at h ⊢
    linarith
  have hKlog : Real.log (K:ℝ) ≤ Real.log (2*r) :=
    Real.log_le_log (by
      exact_mod_cast (show 0<K by omega))
      hK1
  have hElog : Real.log (s/6) ≤ Real.log ((E+1:ℕ):ℝ) :=
    Real.log_le_log (by positivity) hE1
  refine ⟨K,N,hK,?_,?_,?_⟩
  · rw [source_original_true_power64_real_exp434]
    exact (Real.exp_le_exp).2 hStartExp
  · rw [hKN,source_original_true_power64_real_exp434]
    exact (Real.exp_le_exp).2 hEndExp
  · rw [hKN]
    linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedExpScale -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 390000

/-- Exact scale identity: the power-64 rounded prime-band
log-ratio is a fixed positive exponent gap times log L,
minus only the CONSTANT real log 12. -/
theorem source_original_rounded_scale_log_identity434
    (L a b : ℝ) (hL : 0 < L) :
    Real.log ((L^b)/6) - Real.log (2*(L^a)) =
      (b-a)*Real.log L - Real.log 12 := by
  have hLa : 0 < L^a := Real.rpow_pos_of_pos hL _
  have hLb : 0 < L^b := Real.rpow_pos_of_pos hL _
  rw [Real.log_div (ne_of_gt hLb) (by norm_num : (6:ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hLa)]
  rw [Real.log_rpow hL b, Real.log_rpow hL a]
  have hh : Real.log (12:ℝ) = Real.log (2:ℝ)+Real.log (6:ℝ) := by
    rw [show (12:ℝ) = 2*6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hh]
  ring

/-- For fixed positive exponents 0<a<b and real L tending
to infinity, the two inputs r=L^a and s=L^b of the
true source prime power-64 rounding constructor eventually
satisfy 2<=r and 24r<=s. This uses actual Mathlib
power-atTop asymptotics, NOT unproved prime asymptotics. -/
theorem source_original_eventually_rounded_scale_feasible434
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ 2 ≤ L^a ∧ 24*(L^a) ≤ L^b := by
  have hgap : 0 < b-a := sub_pos.mpr hab
  have hr : ∀ᶠ L : ℝ in atTop, 2 ≤ L^a :=
    (tendsto_atTop.1 (tendsto_rpow_atTop ha)) 2
  have hratio : ∀ᶠ L : ℝ in atTop, 24 ≤ L^(b-a) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop hgap)) 24
  filter_upwards [eventually_gt_atTop (1:ℝ),hr,hratio]
    with L hL hr hratio
  have hLpos : 0 < L := by linarith
  have hLa : 0 < L^a := Real.rpow_pos_of_pos hLpos _
  rw [Real.rpow_sub hLpos b a] at hratio
  have hs : 24*(L^a) ≤ L^b :=
    (le_div_iff₀ hLa).mp hratio
  exact ⟨hL,hr,hs⟩

/-- Numerically rounded genuine SMALL or BIG prime band
at EVERY sufficiently large L: both endpoints are actual
integer powers of 64, are INSIDE [exp(L^a),exp(L^b)],
and have logarithmic exponent ratio at least
(b-a)*log L-log12. -/
theorem source_original_eventually_power64_inside_exponential_band434
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop,
      ∃ K N : ℕ, 2 ≤ K ∧
        Real.exp (L^a) ≤ (((64^K:ℕ):ℝ)) ∧
        (((64^(K+N):ℕ):ℝ)) ≤ Real.exp (L^b) ∧
        (b-a)*Real.log L-Real.log 12 ≤
          Real.log ((K+N+1:ℕ):ℝ) - Real.log (K:ℝ) := by
  filter_upwards [source_original_eventually_rounded_scale_feasible434 a b ha hab]
    with L ⟨hL,hr,hs⟩
  obtain ⟨K,N,hK,hstart,hend,hlog⟩ :=
    source_original_true_rounded_power64_band434
      (L^a) (L^b) hr hs
  refine ⟨K,N,hK,hstart,hend,?_⟩
  rw [←source_original_rounded_scale_log_identity434 L a b (by linarith)]
  exact hlog
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedExpBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 420000

/-- Uniform arithmetic REAL power-64 band endpoint and
quantitative Chebyshev mass budget, for any finite number of
FULL or SMALL prime groups m bounded by kappa*log L.
This is an eventual statement about explicit numerical bounds,
not a prime-distribution hypothesis and not a signed saving. -/
theorem source_original_eventually_TRUE_exp_band_budget434
    (a b vmin κ : ℝ)
    (ha : 0 < a) (hab : a < b)
    (hv : 0 < vmin)
    (hκ : 192*κ*(vmin+1) ≤ b-a) :
    ∀ᶠ L : ℝ in atTop,
      ∀ m : ℕ, (m:ℝ) ≤ κ*Real.log L →
        ∃ (K N : ℕ), 2 ≤ K ∧
          Real.exp (L^a) ≤ (((64^K:ℕ):ℝ)) ∧
          (((64^(K+N):ℕ):ℝ)) ≤ Real.exp (L^b) ∧
          (m:ℝ)*(vmin+1/(((64^K:ℕ):ℝ)+1)) ≤
           (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 := by
  have hgap : 0 < b-a := sub_pos.mpr hab
  have hLog :
      ∀ᶠ L : ℝ in atTop,
        2*(Real.log 12+1)/(b-a) ≤ Real.log L :=
    (tendsto_atTop.1 Real.tendsto_log_atTop) _
  filter_upwards
    [source_original_eventually_power64_inside_exponential_band434 a b ha hab,
      hLog]
    with L ⟨K,N,hK,hstart,hend,hlog⟩ hLlog m hm
  have hgapLog :
      2*(Real.log 12+1) ≤ (b-a)*Real.log L := by
    have hh := (div_le_iff₀ hgap).mp hLlog
    nlinarith
  have hlogPos : 0 ≤ Real.log L := by
    have hlog12 : 0 ≤ Real.log (12:ℝ) :=
      (Real.log_pos (by norm_num : (1:ℝ)<12)).le
    have hnum : 0 ≤ 2*(Real.log (12:ℝ)+1)/(b-a) :=
      div_nonneg (by positivity) hgap.le
    linarith
  let δ : ℝ := 1/((((64^K:ℕ):ℝ))+1)
  have hδ : δ ≤ 1 := by
    dsimp [δ]
    have hd : (0:ℝ) < (((64^K:ℕ):ℝ))+1 := by positivity
    apply (div_le_iff₀ hd).2
    nlinarith [show (0:ℝ) ≤ (((64^K:ℕ):ℝ)) from Nat.cast_nonneg _]
  have hvδ : vmin+δ ≤ vmin+1 := by linarith
  have hV : 0 ≤ vmin+1 := by linarith
  have hBudgetUpper :
      (m:ℝ)*(vmin+δ) ≤
      κ*(vmin+1)*Real.log L := by
    calc
      _ ≤ (m:ℝ)*(vmin+1) :=
        mul_le_mul_of_nonneg_left hvδ
          (Nat.cast_nonneg _)
      _ ≤ (κ*Real.log L)*(vmin+1) :=
        mul_le_mul_of_nonneg_right hm hV
      _ = _ := by ring
  have hcoef : 96*κ*(vmin+1) ≤ (b-a)/2 := by
    linarith
  have hcoefMul := mul_le_mul_of_nonneg_right hcoef hlogPos
  have hBudget :
      (m:ℝ)*(vmin+δ) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 := by
    have hnumeric :
        κ*(vmin+1)*Real.log L ≤
          ((b-a)*Real.log L-Real.log 12-1)/96 := by
      have hh :
          96*κ*(vmin+1)*Real.log L ≤
          ((b-a)/2)*Real.log L := by
        nlinarith [hcoefMul]
      have hh2 :
          ((b-a)/2)*Real.log L ≤
          (b-a)*Real.log L-Real.log 12-1 := by
        linarith
      linarith
    have hgapBudget :
        ((b-a)*Real.log L-Real.log 12-1)/96 ≤
          (Real.log ((K+N+1:ℕ):ℝ)-1-Real.log (K:ℝ))/96 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    exact hBudgetUpper.trans (hnumeric.trans hgapBudget)
  exact ⟨K,N,hK,hstart,hend,hBudget⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedHarmonicTolerance -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 280000

/-- With a true moving SMALL/BIG source prime band starting at
exp(L^a), the exact excess harmonic mass of the true
prime-group greedy/full-interval constructors, 1/(64^K+1),
is EVENTUALLY SMALLER than ANY fixed positive tolerance epsilon.
The same lemma applies to S, Ts, and FULL Tb groups.
No prime asymptotics: only the integer band starting cutoff. -/
theorem source_original_eventually_power64_harmonic_excess_le434
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      ∀ K : ℕ,
        Real.exp (L^a) ≤ (((64^K:ℕ):ℝ)) →
          (1:ℝ)/((((64^K:ℕ):ℝ))+1) ≤ ε := by
  have hev : ∀ᶠ L : ℝ in atTop,
      Real.log (1/ε) ≤ L^a :=
    (tendsto_atTop.1 (tendsto_rpow_atTop ha)) _
  filter_upwards [hev] with L hL K hK
  have hB : (1:ℝ)/ε ≤ (((64^K:ℕ):ℝ)) := by
    calc
      _ = Real.exp (Real.log (1/ε)) := by
        rw [Real.exp_log (by positivity)]
      _ ≤ Real.exp (L^a) := (Real.exp_le_exp).2 hL
      _ ≤ _ := hK
  have hdpos : (0:ℝ) < (((64^K:ℕ):ℝ))+1 := by positivity
  apply (div_le_iff₀ hdpos).2
  have hh : (1:ℝ) ≤ (((64^K:ℕ):ℝ))*ε :=
    (div_le_iff₀ hε).mp hB
  have hn : (0:ℝ) ≤ ε := hε.le
  nlinarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedExactBigBounds -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 360000

/-- For every sufficiently large original L and true exponent
band exp(L^c)..exp(L^d), construct n BIG groups as ALL
primes in their consecutive disjoint intervals, with ACTUAL
harmonic mass in the full original window [v_-,v_+).
The overshoot can be smaller than ANY prescribed gap,
rather than merely 1. No assumed BIG prime group family. -/
theorem source_original_eventually_TRUE_FULL_BIG_groups_original_mass_window434
    (c d vmin vmax κ : ℝ)
    (hc : 0 < c) (hcd : c < d)
    (hvmin : 0 < vmin) (hvspan : vmin < vmax)
    (hκ : 192*κ*(vmin+1) ≤ d-c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ n : ℕ, (n:ℝ) ≤ κ*Real.log L →
        ∃ (left right : Fin n → ℕ),
          (∀ i, left i < right i) ∧
          (∀ i p,
            p ∈ sourceOriginalActualPrimeBand434 (left i) (right i) →
              p.Prime ∧ Real.exp (L^c) ≤ (p:ℝ) ∧
                (p:ℝ) ≤ Real.exp (L^d)) ∧
          (∀ i, vmin ≤ sourceOriginalPrimeBandHarmonicMass434
              (left i) (right i) ∧
            sourceOriginalPrimeBandHarmonicMass434
              (left i) (right i) < vmax) ∧
          (∀ i j, i≠j →
            Disjoint
              (sourceOriginalActualPrimeBand434 (left i) (right i))
              (sourceOriginalActualPrimeBand434 (left j) (right j))) := by
  have hgap : 0 < vmax-vmin := sub_pos.mpr hvspan
  filter_upwards
    [source_original_eventually_TRUE_exp_band_budget434
        c d vmin κ hc hcd hvmin hκ,
      source_original_eventually_power64_harmonic_excess_le434
        c (vmax-vmin) hc hgap]
    with L hBudget htol n hn
  obtain ⟨K,N,hK,hstart,hend,hm⟩ := hBudget n hn
  let δ : ℝ := (1:ℝ)/(((64^K:ℕ):ℝ)+1)
  have hδ : δ ≤ vmax-vmin := htol K hstart
  have hm' : (n:ℝ)*(vmin+δ) ≤
      (Real.log ((K+N+1:ℕ):ℝ)-Real.log (K:ℝ)-1)/96 := by
    dsimp [δ]
    convert hm using 1
    ring
  obtain ⟨left,right,hrange,hband,hVm,hdisj⟩ :=
    source_original_TRUE_chebyshev64_source03_FULL_BIG_exp_geometry434
      K N n hK L c d vmin δ hvmin hstart hend
      (by simpa only [δ,Nat.cast_add,Nat.cast_one] using
        (le_refl δ)) hm'
  refine ⟨left,right,hrange,hband,?_,hdisj⟩
  intro i
  have hh : vmin+δ ≤ vmax := by linarith
  exact ⟨(hVm i).1,lt_of_lt_of_le (hVm i).2 hh⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedExactSmallBounds -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 350000

/-- The ORIGINAL strict harmonic window v_- < v_+ is respected,
with NO artificial need to have v_+ >= v_-+1.
At every sufficiently large L construct all n+1 distinguished
S+Ts true prime groups within exp(L^a)..exp(L^b),
provided n+1<=kappa log L at a sufficiently small FIXED kappa.
The extra mass 1/(64^K+1) is proved <v_+-v_- eventually. -/
theorem source_original_eventually_TRUE_SMALL_groups_original_mass_window434
    (a b vmin vmax κ : ℝ)
    (ha : 0 < a) (hab : a < b)
    (hvmin : 0 < vmin) (hvspan : vmin < vmax)
    (hκ : 192*κ*(vmin+1) ≤ b-a) :
    ∀ᶠ L : ℝ in atTop,
      ∀ n : ℕ, ((n+1:ℕ):ℝ) ≤ κ*Real.log L →
        ∃ (P : Option (Fin n) → Finset ℕ)
          (V : Option (Fin n) → ℝ),
        (∀ g, (P g).Nonempty) ∧
        (∀ g p, p ∈ P g →
          p.Prime ∧ Real.exp (L^a) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (L^b)) ∧
        (∀ g, V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ)) ∧
        (∀ g, vmin ≤ V g ∧ V g < vmax) ∧
        (∀ g h, g≠h → Disjoint (P g) (P h)) := by
  have hgap : 0 < vmax-vmin := sub_pos.mpr hvspan
  filter_upwards
    [source_original_eventually_TRUE_exp_band_budget434
        a b vmin κ ha hab hvmin hκ,
      source_original_eventually_power64_harmonic_excess_le434
        a (vmax-vmin) ha hgap]
    with L hBudget htol n hn
  obtain ⟨K,N,hK,hstart,hend,hm⟩ := hBudget (n+1) hn
  have hδ : (1:ℝ)/(((64^K:ℕ):ℝ)+1) ≤ vmax-vmin :=
    htol K hstart
  obtain ⟨P,V,hne,hP,hVe,hVm,hdisj⟩ :=
    source_original_TRUE_chebyshev64_source03_exp_groups434
      K N n hK L a b vmin hvmin hstart hend hm
  refine ⟨P,V,hne,hP,hVe,?_,hdisj⟩
  intro g
  have hbound := hVm g
  refine ⟨hbound.1,?_⟩
  have hh : vmin+ (1:ℝ)/(((64^K:ℕ):ℝ)+1) ≤ vmax := by
    linarith
  exact lt_of_lt_of_le hbound.2 hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedExactJointGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 520000

/-- Genuine ORIGINAL source03 group geometry for ALL sufficiently
large real L and EVERY allowed moving count of SMALL S+Ts and
BIG FULL prime intervals up to explicit fixed multiples of log L.
Unlike earlier bridges there are NO numerical prime-band endpoint
or prime-harmonic mass hypotheses, and each EXACT original bound
v_- <= V_g <= v_+ holds for ANY gap 0<v_-<v_+.
The only fixed rate restriction is
192*κS*(vSmin+1)<=b-a and 192*κB*(vBmin+1)<=d-c.
This does NOT prove signed path-pair correlation saving. -/
theorem source_original_eventually_TRUE_source03_full_prime_geometry434
    (a b c d vSmin vSmax vBmin vBmax κS κB : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hvSmin : 0 < vSmin) (hvSspan : vSmin < vSmax)
    (hvBmin : 0 < vBmin) (hvBspan : vBmin < vBmax)
    (hκS : 192*κS*(vSmin+1) ≤ b-a)
    (hκB : 192*κB*(vBmin+1) ≤ d-c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ nS nB : ℕ,
        ((nS+1:ℕ):ℝ) ≤ κS*Real.log L →
        (nB:ℝ) ≤ κB*Real.log L →
      ∃ (P : Option (Fin nS) → Finset ℕ)
        (V : Option (Fin nS) → ℝ)
        (left right : Fin nB → ℕ),
        (∀ g, (P g).Nonempty ∧
          V g = ∑ p ∈ P g,(1:ℝ)/(p:ℝ) ∧
          vSmin ≤ V g ∧ V g < vSmax) ∧
        (∀ g p, p ∈ P g →
          p.Prime ∧ Real.exp (L^a) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (L^b)) ∧
        (∀ i, left i < right i ∧
          vBmin ≤ sourceOriginalPrimeBandHarmonicMass434
            (left i) (right i) ∧
          sourceOriginalPrimeBandHarmonicMass434
            (left i) (right i) < vBmax) ∧
        (∀ i p,
          p ∈ sourceOriginalActualPrimeBand434 (left i) (right i) →
            p.Prime ∧ Real.exp (L^c) ≤ (p:ℝ) ∧
              (p:ℝ) ≤ Real.exp (L^d)) ∧
        (∀ g h, g≠h → Disjoint (P g) (P h)) ∧
        (∀ i j, i≠j → Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) ∧
        (∀ g i, Disjoint (P g)
          (sourceOriginalActualPrimeBand434 (left i) (right i))) := by
  have hc : 0 < c := lt_trans ha (lt_trans hab hbc)
  filter_upwards
    [eventually_gt_atTop (1:ℝ),
      source_original_eventually_TRUE_SMALL_groups_original_mass_window434
        a b vSmin vSmax κS ha hab hvSmin hvSspan hκS,
      source_original_eventually_TRUE_FULL_BIG_groups_original_mass_window434
        c d vBmin vBmax κB hc hcd hvBmin hvBspan hκB]
    with L hL hsmall hbig nS nB hnS hnB
  obtain ⟨P,V,hSne,hSband,hSV,hSmass,hSdisj⟩ :=
    hsmall nS hnS
  obtain ⟨left,right,hBrange,hBband,hBmass,hBdisj⟩ :=
    hbig nB hnB
  have hgap :=
    source_original_source03_exponential_bands_separated434
      L b c hL hbc
  refine ⟨P,V,left,right,?_,hSband,?_,hBband,hSdisj,hBdisj,?_⟩
  · intro g
    exact ⟨hSne g,hSV g,(hSmass g).1,(hSmass g).2⟩
  · intro i
    exact ⟨hBrange i,(hBmass i).1,(hBmass i).2⟩
  · intro g i
    apply Finset.disjoint_left.mpr
    intro p hpS hpB
    have hpLower := (hBband i p hpB).2.1
    have hpUpper := (hSband g p hpS).2.2
    exact (not_le_of_gt hgap) (hpLower.trans hpUpper)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedGroupCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 360000

/-- A genuinely MOVING integer count T of BOTH prime-group types
exists at every sufficiently large L. It is bounded BELOW by a
fixed positive multiple of log L, while both SMALL count T+1
and BIG count T fit the quantitative source03 Chebyshev budgets. -/
theorem source_original_eventually_TRUE_source03_log_group_count434
    (κS κB : ℝ) (hS : 0 < κS) (hB : 0 < κB) :
    ∀ᶠ L : ℝ in atTop,
      ∃ T : ℕ,
        ((min κS κB)/4)*Real.log L ≤ (T:ℝ) ∧
        ((T+1:ℕ):ℝ) ≤ κS*Real.log L ∧
        (T:ℝ) ≤ κB*Real.log L := by
  let q : ℝ := min κS κB / 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hev : ∀ᶠ L : ℝ in atTop,
      2/q ≤ Real.log L :=
    (tendsto_atTop.1 Real.tendsto_log_atTop) _
  filter_upwards [hev] with L hL
  let T := Nat.floor (q*Real.log L)
  have hql : 2 ≤ q*Real.log L := by
    have hh := (div_le_iff₀ hq).mp hL
    nlinarith
  have hlogL : 0 ≤ Real.log L := by
    have hh : 0 < 2/q := by positivity
    linarith
  have hflo : (T:ℝ) ≤ q*Real.log L :=
    Nat.floor_le (by linarith)
  have hfhi : q*Real.log L < (T:ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hqS : 2*q ≤ κS := by
    dsimp [q]
    have hh := min_le_left κS κB
    linarith
  have hqB : q ≤ κB := by
    dsimp [q]
    have hh := min_le_right κS κB
    have hp : 0 ≤ min κS κB := le_min hS.le hB.le
    linarith
  have hCapS : ((T+1:ℕ):ℝ) ≤ κS*Real.log L := by
    have hm := mul_le_mul_of_nonneg_right hqS hlogL
    push_cast
    nlinarith
  have hCapB : (T:ℝ) ≤ κB*Real.log L := by
    have hm := mul_le_mul_of_nonneg_right hqB hlogL
    linarith
  have hLower : (min κS κB/4)*Real.log L ≤ (T:ℝ) := by
    have hh : q*Real.log L/2 ≤ (T:ℝ) := by
      linarith
    dsimp [q] at hh
    nlinarith
  exact ⟨T,hLower,hCapS,hCapB⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedArbitraryGroupConstants -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 430000

/-- Arithmetic selection of group counts for ANY fixed source03
constants 0<c0<C0. In particular actual SMALL group count n+1
and BIG group count n BOTH lie between c0*T and C0*T, for a
truly moving integer T=Omega(log L). The counts also fit any
given positive small Chebyshev construction rates kappaS,kappaB.
The numeric rates may depend on c0,C0 and exponent-gap widths,
as required by the original manuscript's fixed group constants. -/
theorem source_original_eventually_TRUE_original_group_cardinalities434
    (c0 C0 κS κB : ℝ)
    (hc0 : 0 < c0) (hgap : c0 < C0)
    (hκS : 0 < κS) (hκB : 0 < κB) :
    ∀ᶠ L : ℝ in atTop,
      ∃ (T n : ℕ), 0 < T ∧
        (min κS κB/(8*(c0+1)))*Real.log L ≤ (T:ℝ) ∧
        c0*(T:ℝ) ≤ (n:ℝ) ∧
        ((n+1:ℕ):ℝ) ≤ C0*(T:ℝ) ∧
        ((n+1:ℕ):ℝ) ≤ κS*Real.log L ∧
        (n:ℝ) ≤ κB*Real.log L := by
  let κ : ℝ := min κS κB
  let q : ℝ := κ/(4*(c0+1))
  have hκ : 0 < κ := lt_min hκS hκB
  have hcpos : 0 < c0+1 := by linarith
  have hΔ : 0 < C0-c0 := sub_pos.mpr hgap
  have hq : 0 < q := by dsimp [q]; positivity
  have hFactor : (c0+1)*q = κ/4 := by
    dsimp [q]
    field_simp
  let cutoff : ℝ := 4+2/(C0-c0)
  have hevent :
      ∀ᶠ L : ℝ in atTop, cutoff/q ≤ Real.log L :=
    (tendsto_atTop.1 Real.tendsto_log_atTop) _
  filter_upwards [hevent] with L hL
  have hQ : cutoff ≤ q*Real.log L := by
    have hh := (div_le_iff₀ hq).mp hL
    nlinarith
  have hL0 : 0 ≤ Real.log L := by
    have hcut : 0 < cutoff := by
      dsimp [cutoff]
      positivity
    have hh : 0 < q*Real.log L := lt_of_lt_of_le hcut hQ
    have hq0 : 0 < q := hq
    nlinarith
  let T : ℕ := Nat.floor (q*Real.log L)
  let n : ℕ := Nat.ceil (c0*(T:ℝ))
  have hTup : (T:ℝ) ≤ q*Real.log L :=
    Nat.floor_le (by nlinarith [hQ])
  have hTlo : q*Real.log L < (T:ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hTpositive : 0 < T := by
    have hh : (2:ℝ) ≤ q*Real.log L := by
      have hδnn : 0 ≤ 2/(C0-c0) := by positivity
      dsimp [cutoff] at hQ
      linarith
    have ht : (1:ℝ) < (T:ℝ) := by linarith
    have hNat : 1 < T := by exact_mod_cast ht
    omega
  have hNl : c0*(T:ℝ) ≤ (n:ℝ) := Nat.le_ceil _
  have hNu : (n:ℝ) < c0*(T:ℝ)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hTgap : (2:ℝ)/(C0-c0) ≤ (T:ℝ) := by
    dsimp [cutoff] at hQ
    linarith
  have hCgap : 2 ≤ (C0-c0)*(T:ℝ) := by
    have hh := (div_le_iff₀ hΔ).mp hTgap
    nlinarith
  have hCardC : ((n+1:ℕ):ℝ) ≤ C0*(T:ℝ) := by
    push_cast
    nlinarith
  have hNL : ((n+1:ℕ):ℝ) ≤ (c0+1)*(q*Real.log L) := by
    have hQ2 : 2 ≤ q*Real.log L := by
      dsimp [cutoff] at hQ
      have hh : 0 ≤ 2/(C0-c0) := by positivity
      linarith
    have hMul := mul_le_mul_of_nonneg_left hTup hc0.le
    push_cast
    nlinarith
  have hScaled : (c0+1)*(q*Real.log L) = (κ/4)*Real.log L := by
    calc
      _ = ((c0+1)*q)*Real.log L := by ring
      _ = _ := by rw [hFactor]
  have hκS : κ ≤ κS := min_le_left _ _
  have hκB : κ ≤ κB := min_le_right _ _
  have hCapS : ((n+1:ℕ):ℝ) ≤ κS*Real.log L := by
    calc
      _ ≤ (c0+1)*(q*Real.log L) := hNL
      _ = (κ/4)*Real.log L := hScaled
      _ ≤ κ*Real.log L := by nlinarith [mul_nonneg hκ.le hL0]
      _ ≤ κS*Real.log L :=
        mul_le_mul_of_nonneg_right hκS hL0
  have hCapB : (n:ℝ) ≤ κB*Real.log L := by
    have hle : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by
      exact_mod_cast (Nat.le_succ n)
    have hcommon : (n:ℝ) ≤ κ*Real.log L := by
      calc
        _ ≤ (c0+1)*(q*Real.log L) := hle.trans hNL
        _ = (κ/4)*Real.log L := hScaled
        _ ≤ κ*Real.log L := by nlinarith [mul_nonneg hκ.le hL0]
    exact hcommon.trans (mul_le_mul_of_nonneg_right hκB hL0)
  have hTlower : (κ/(8*(c0+1)))*Real.log L ≤ (T:ℝ) := by
    have hh : q*Real.log L/2 ≤ (T:ℝ) := by
      have hqL2 : 2 ≤ q*Real.log L := by
        have hδnn : 0 ≤ 2/(C0-c0) := by positivity
        dsimp [cutoff] at hQ
        linarith
      linarith
    have hEq : κ/(8*(c0+1))*Real.log L =
          (q*Real.log L)/2 := by
      dsimp [q]
      field_simp [ne_of_gt hcpos]
      ring
    rw [hEq]
    exact hh
  exact ⟨T,n,hTpositive,hTlower,hNl,hCardC,hCapS,hCapB⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevRoundedSource03Cardinality -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 370000

/-- Original source03 group geometry for arbitrary FIXED
0<c0<C0: at every large L choose T=Omega(log L), numbers
of true SMALL groups n+1 and full-interval BIG groups n
satisfying simultaneously c0*T <= n <= n+1 <= C0*T.
All distinct group primes really lie in the exact exp(L^a),
exp(L^b) and exp(L^c),exp(L^d) bands, and each group obeys
the original REAL harmonic mass window v_-<=V_g<v_+.
This is a verified construction, not an assumed group record.
It still does NOT prove the signed source03 correlation. -/
theorem source_original_eventually_TRUE_source03_arbitrary_c0_C0_geometry434
    (a b c d vSmin vSmax vBmin vBmax c0 C0 κS κB : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hvSmin : 0 < vSmin) (hvSspan : vSmin < vSmax)
    (hvBmin : 0 < vBmin) (hvBspan : vBmin < vBmax)
    (hc0 : 0 < c0) (hC0 : c0 < C0)
    (hκSpos : 0 < κS) (hκBpos : 0 < κB)
    (hκS : 192*κS*(vSmin+1) ≤ b-a)
    (hκB : 192*κB*(vBmin+1) ≤ d-c) :
    ∀ᶠ L : ℝ in atTop,
      ∃ (T n : ℕ),
        0 < T ∧
        ((min κS κB)/(8*(c0+1)))*Real.log L ≤ (T:ℝ) ∧
        c0*(T:ℝ) ≤ (n:ℝ) ∧
        ((n+1:ℕ):ℝ) ≤ C0*(T:ℝ) ∧
      ∃ (P : Option (Fin n) → Finset ℕ)
        (V : Option (Fin n) → ℝ)
        (left right : Fin n → ℕ),
        (∀ g, (P g).Nonempty ∧
          V g = ∑ p ∈ P g,(1:ℝ)/(p:ℝ) ∧
          vSmin ≤ V g ∧ V g < vSmax) ∧
        (∀ g p, p ∈ P g →
          p.Prime ∧ Real.exp (L^a) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (L^b)) ∧
        (∀ i, left i < right i ∧
          vBmin ≤ sourceOriginalPrimeBandHarmonicMass434
            (left i) (right i) ∧
          sourceOriginalPrimeBandHarmonicMass434
            (left i) (right i) < vBmax) ∧
        (∀ i p,
          p ∈ sourceOriginalActualPrimeBand434 (left i) (right i) →
            p.Prime ∧ Real.exp (L^c) ≤ (p:ℝ) ∧
              (p:ℝ) ≤ Real.exp (L^d)) ∧
        (∀ g h, g≠h → Disjoint (P g) (P h)) ∧
        (∀ i j, i≠j → Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) ∧
        (∀ g i, Disjoint (P g)
          (sourceOriginalActualPrimeBand434 (left i) (right i))) := by
  filter_upwards
    [source_original_eventually_TRUE_source03_full_prime_geometry434
        a b c d vSmin vSmax vBmin vBmax κS κB
        ha hab hbc hcd hvSmin hvSspan hvBmin hvBspan
        hκS hκB,
     source_original_eventually_TRUE_original_group_cardinalities434
       c0 C0 κS κB hc0 hC0 hκSpos hκBpos]
    with L hGeom hCount
  obtain ⟨T,n,hT,hTlow,hNlow,hNhigh,hScap,hBcap⟩ := hCount
  obtain ⟨P,V,left,right,hS,hSband,hB,hBband,hSS,hBB,hSB⟩ :=
    hGeom n n hScap hBcap
  exact ⟨T,n,hT,hTlow,hNlow,hNhigh,P,V,left,right,
    hS,hSband,hB,hBband,hSS,hBB,hSB⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimitivePairSWReady -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The true source03 quotient of two DISTINCT primitive
Dirichlet characters is not necessarily itself primitive;
Siegel-Walfisz applies to its canonical primitive character.
This theorem discharges nonprincipality (not assumed) and
preserves the exact conductor bound Q². -/
theorem source_original_primitive_pair_SW_primitive_data434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧
    η.primitiveCharacter ≠ 1 ∧
    η.conductor ≤ Q^2 := by
  dsimp
  let η := sourceOriginalPrimitivePairQuotient434 Q c d
  have hη : η ≠ 1 :=
    source_original_distinct_primitive_pair_quotient_nonprincipal434
      Q c d hc hd hne
  have hprim : η.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive η
  have hnonprim : η.primitiveCharacter ≠ 1 := by
    intro h
    have heq := η.changeLevel_primitiveCharacter
    rw [h] at heq
    have hηone : η = 1 := by
      simpa using heq.symm
    exact hη hηone
  have hlevel : 0 < sourceOriginalPrimitiveCommonLevel434 Q c d := by
    unfold sourceOriginalPrimitiveCommonLevel434
    exact Nat.lcm_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  have hcond : η.conductor ≤ Q^2 := by
    calc
      η.conductor ≤ sourceOriginalPrimitiveCommonLevel434 Q c d :=
        Nat.le_of_dvd hlevel η.conductor_dvd_level
      _ ≤ Q^2 :=
        source_original_primitive_common_level_le_square434 Q c d
  exact ⟨hprim,hnonprim,hcond⟩

/-- On EACH genuine original BIG prime p>Q², the primitive
character η* has EXACTLY the same numerical prime values
as the true source pair character \barχ(p)ψ(p).
This is the missing safe bridge to the kernel-checked
unconditional Siegel-Walfisz theorem from the D direction. -/
theorem source_original_primitive_pair_SW_eval_big_prime434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (p : ℕ) (hp : p.Prime) (hpBig : Q^2 < p) :
    (sourceOriginalPrimitivePairQuotient434 Q c d).primitiveCharacter
       (p : ZMod (sourceOriginalPrimitivePairQuotient434 Q c d).conductor) =
    star (c.2 (p:ZMod (c.1.val+1))) *
      d.2 (p:ZMod (d.1.val+1)) := by
  let η := sourceOriginalPrimitivePairQuotient434 Q c d
  have hcop := source_original_primitive_pair_big_prime_coprime434
     Q c d p hp hpBig
  have hprimEval :
      η.primitiveCharacter (p : ZMod η.conductor) =
      η (p : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d)) := by
    simpa only [Int.cast_natCast] using
      (η.primitiveCharacter_apply_of_isCoprime hcop)
  have hpair := source_original_primitive_pair_prime_eval434
     Q c d p hp hpBig
  exact hprimEval.trans hpair.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitivePairSWInterval -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- EXACT missing SW bridge for the ORIGINAL source03
offdiagonal character pair over an actual finite BIG prime
interval (a,b]. Even if the quotient at common level lcm
is IMPIMITIVE, on all source BIG primes p>Q² it equals the
canonical PRIMITIVE character at its honest conductor.
NO extra prime endpoint or numerical character weight lost. -/
theorem source_original_primitive_pair_SW_interval_equal434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (a b : ℕ)
    (hBIG : ∀ p ∈ Finset.Ioc a b, p.Prime → Q^2 < p) :
    (∑ p ∈ Finset.Ioc a b,
      if p.Prime then
        star (c.2 (p : ZMod (c.1.val+1))) *
          d.2 (p : ZMod (d.1.val+1)) else 0) =
    (∑ p ∈ Finset.Ioc a b,
      if p.Prime then
        (sourceOriginalPrimitivePairQuotient434 Q c d).primitiveCharacter
          (p : ZMod
            (sourceOriginalPrimitivePairQuotient434 Q c d).conductor)
      else 0) := by
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [if_pos hprime]
    exact (source_original_primitive_pair_SW_eval_big_prime434
      Q c d p hprime (hBIG p hp hprime)).symm
  · simp only [if_neg hprime]

/-- Precise source03 SW arithmetic handoff:
for distinct ORIGINAL primitive characters χ,ψ, the input
to an unconditional Siegel-Walfisz theorem is the REAL
primitive character (χ^{-1}ψ)^* of conductor at most Q²,
and the ORIGINAL prime interval sum is literally identical.
Unlike merely knowing quotient≠1 at lcm(qχ,qψ), this
certifies the PRIMITIVE/nonprincipal input needed by D. -/
theorem source_original_primitive_pair_SW_ready_interval434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (a b : ℕ)
    (hBIG : ∀ p ∈ Finset.Ioc a b, p.Prime → Q^2 < p) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧
    η.primitiveCharacter ≠ 1 ∧
    η.conductor ≤ Q^2 ∧
    (∑ p ∈ Finset.Ioc a b,
      if p.Prime then
        star (c.2 (p : ZMod (c.1.val+1))) *
           d.2 (p : ZMod (d.1.val+1)) else 0) =
    (∑ p ∈ Finset.Ioc a b,
      if p.Prime then
         η.primitiveCharacter (p : ZMod η.conductor)
      else 0) := by
  dsimp
  obtain ⟨hprim, hnon, hcond⟩ :=
    source_original_primitive_pair_SW_primitive_data434
      Q c d hc hd hne
  exact ⟨hprim, hnon, hcond,
    source_original_primitive_pair_SW_interval_equal434
      Q c d a b hBIG⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveSWConductorScale -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Unconditional conductor-to-logarithmic-scale estimate for the
GENUINE primitive quotient of distinct original source03 characters.
The physical prime band begins at exp(L); Q is allowed to be any
polylogarithmic level L^Cq. No fake primitivity of the quotient. -/
theorem source_original_primitive_pair_SW_conductor_log_scale434
    (Q Cq u : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hu : Real.exp L ≤ ((u+1:ℕ):ℝ))
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧
    η.primitiveCharacter ≠ 1 ∧
    (η.conductor:ℝ) ≤
      Real.log ((u+1:ℕ):ℝ) ^ (2*Cq+1) := by
  dsimp
  obtain ⟨hprim,hnon,hcond⟩ :=
    source_original_primitive_pair_SW_primitive_data434
      Q c d hc hd hne
  let y : ℝ := ((u+1:ℕ):ℝ)
  have hlog : L ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos L) hu
    simpa only [Real.log_exp] using h
  let η := sourceOriginalPrimitivePairQuotient434 Q c d
  have hcondReal : (η.conductor:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast hcond
  have hQsq : (Q:ℝ)^2 ≤ (L^Cq)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
  have hLpow : (L^Cq)^2 = L^(2*Cq) := by
    rw [←pow_mul]
    congr 1
    omega
  have hpow : L^(2*Cq) ≤ Real.log y ^ (2*Cq) :=
    pow_le_pow_left₀ (by linarith) hlog (2*Cq)
  have hlogOne : 1 ≤ Real.log y := hL.trans hlog
  have hlast : Real.log y ^ (2*Cq) ≤
      Real.log y ^ (2*Cq+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) hlogOne
  refine ⟨hprim,hnon,?_⟩
  change (η.conductor:ℝ) ≤ Real.log y ^ (2*Cq+1)
  exact hcondReal.trans (hQsq.trans (le_of_eq_of_le hLpow (hpow.trans hlast)))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveSWFractionalScale -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Actual source03 BIG prime scale exp(L^gamma), with
0 < gamma < 1 permitted. This is the essential fractional
log-scale version: Q <= L^Cq, conductor <= Q^2 and
2*Cq <= gamma*C imply conductor <= (log(u+1))^C.
Unlike exp(L), this matches the ORIGINAL BIG group ranges. -/
theorem source_original_primitive_pair_SW_fractional_log_scale434
    (Q Cq u : ℕ) (L gamma C : ℝ)
    (hL : 1 ≤ L) (hgamma : 0 < gamma)
    (hC : 0 < C) (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hu : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧
    η.primitiveCharacter ≠ 1 ∧
    (η.conductor:ℝ) ≤ (Real.log ((u+1:ℕ):ℝ))^C := by
  dsimp
  obtain ⟨hprim,hnon,hcond⟩ :=
    source_original_primitive_pair_SW_primitive_data434 Q c d hc hd hne
  let η := sourceOriginalPrimitivePairQuotient434 Q c d
  let y : ℝ := ((u+1:ℕ):ℝ)
  have hlog : L^gamma ≤ Real.log y := by
    have ht := Real.log_le_log (Real.exp_pos _) hu
    simpa only [Real.log_exp] using ht
  have hcast : (η.conductor:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast hcond
  have hQsq : (Q:ℝ)^2 ≤ (L^Cq)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
  have hpowEq : (L^Cq)^2 = L^(2*(Cq:ℝ)) := by
    calc
      _ = L^(Cq*2) := by rw [pow_mul]
      _ = L^((Cq*2:ℕ):ℝ) := by rw [Real.rpow_natCast]
      _ = L^(2*(Cq:ℝ)) := by
        congr 1
        push_cast
        ring
  have hpowOrder : L^(2*(Cq:ℝ)) ≤ L^(gamma*C) :=
    Real.rpow_le_rpow_of_exponent_le hL hExponent
  have hLpos : 0 ≤ L := by linarith
  have hlogPower : (L^gamma)^C ≤ (Real.log y)^C :=
    Real.rpow_le_rpow (Real.rpow_nonneg hLpos _) hlog hC.le
  refine ⟨hprim,hnon,?_⟩
  change (η.conductor:ℝ) ≤ (Real.log y)^C
  calc
    _ ≤ (Q:ℝ)^2 := hcast
    _ ≤ (L^Cq)^2 := hQsq
    _ = L^(2*(Cq:ℝ)) := hpowEq
    _ ≤ L^(gamma*C) := hpowOrder
    _ = (L^gamma)^C := Real.rpow_mul hLpos gamma C
    _ ≤ (Real.log y)^C := hlogPower
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveSWMovingBox -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The EXACT original source03 moving prime interval fits a
single Siegel–Walfisz dyadic box whenever its source BIG group
is dyadic. The original character pair, moving cutoffs, and
primitive inducing character are preserved literally. -/
theorem source_original_primitive_SW_moving_dyadic_box434
    (Q Cq u v a k lo hi : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp L ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u) (hdyad : v ≤ 2*(u+1))
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧ η.primitiveCharacter ≠ 1 ∧
    (η.conductor:ℝ) ≤ Real.log ((u+1:ℕ):ℝ)^(2*Cq+1) ∧
    ((u+1:ℕ):ℝ) ≤ ((max a (max u lo):ℕ):ℝ)+1 ∧
    ((min k (min v hi):ℕ):ℝ) ≤ 2*((u+1:ℕ):ℝ) ∧
    (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then star (c.2 (p:ZMod (c.1.val+1))) *
         d.2 (p:ZMod (d.1.val+1)) else 0) =
    (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then η.primitiveCharacter (p:ZMod η.conductor)
       else 0) := by
  dsimp
  obtain ⟨hprim,hnon,hcond⟩ :=
    source_original_primitive_pair_SW_conductor_log_scale434
      Q Cq u L hL hQ huLarge c d hc hd hne
  have hleft : ((u+1:ℕ):ℝ) ≤
      ((max a (max u lo):ℕ):ℝ)+1 := by
    have h : u ≤ max a (max u lo) := by omega
    exact_mod_cast (Nat.add_le_add_right h 1)
  have hright : ((min k (min v hi):ℕ):ℝ) ≤
      2*((u+1:ℕ):ℝ) := by
    have h : min k (min v hi) ≤ 2*(u+1) := by omega
    exact_mod_cast h
  have hBIG : ∀ p ∈ Finset.Ioc (max a (max u lo))
      (min k (min v hi)), p.Prime → Q^2 < p := by
    intro p hp _
    have hpl := (Finset.mem_Ioc.mp hp).1
    omega
  refine ⟨hprim,hnon,hcond,hleft,hright,?_⟩
  exact source_original_primitive_pair_SW_interval_equal434
    Q c d (max a (max u lo)) (min k (min v hi)) hBIG
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDyadicExactPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact finite telescoping over ordered half-open natural intervals.
It applies with the physical character sum as the summand, so no
smoothing, replacement prime law or endpoint loss is introduced. -/
theorem source_original_Ioc_sum_partition434
    (s : ℕ → ℕ) (hs : Monotone s) (F : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ p ∈ Finset.Ioc (s i) (s (i+1)), F p) =
      ∑ p ∈ Finset.Ioc (s 0) (s n), F p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hd : Disjoint (Finset.Ioc (s 0) (s n))
          (Finset.Ioc (s n) (s (n+1))) :=
        Finset.Ioc_disjoint_Ioc_of_le (le_refl (s n))
      rw [← Finset.sum_union hd,
        Finset.Ioc_union_Ioc_eq_Ioc
          (hs (Nat.zero_le n)) (hs (Nat.le_succ n))]

/-- Dyadic pieces clipped at the exact original BIG-band endpoint. -/
def sourceSWClippedDyad434 (u v i : ℕ) : ℕ :=
  min v (u*2^i)
theorem sourceSWClippedDyad_mono434 (u v : ℕ) :
    Monotone (sourceSWClippedDyad434 u v) := by
  intro i j hij
  dsimp [sourceSWClippedDyad434]
  have hp : (2:ℕ)^i ≤ 2^j := by gcongr
  exact min_le_min_left v (Nat.mul_le_mul_left u hp)

/-- Exact partition of the actual long BIG prime-band interval.
All pieces are clipped; their union contains precisely (u,v]. -/
theorem source_original_exact_clipped_dyadic_partition434
    (u v n : ℕ) (huv : u ≤ v) (hv : v ≤ u*2^n)
    (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc u v, F p) =
    ∑ i ∈ Finset.range n,
      ∑ p ∈ Finset.Ioc (sourceSWClippedDyad434 u v i)
        (sourceSWClippedDyad434 u v (i+1)), F p := by
  have hsum := source_original_Ioc_sum_partition434
    (sourceSWClippedDyad434 u v)
      (sourceSWClippedDyad_mono434 u v) F n
  have h0 : sourceSWClippedDyad434 u v 0 = u := by
    simp [sourceSWClippedDyad434, min_eq_right huv]
  have hn : sourceSWClippedDyad434 u v n = v := by
    exact min_eq_left hv
  simpa only [h0,hn] using hsum.symm
/-- Every clipped dyadic piece has the precise SW box width,
including inactive empty pieces after the original upper endpoint. -/
theorem source_original_clipped_dyadic_SW_width434
    (u v i : ℕ) :
    sourceSWClippedDyad434 u v (i+1) ≤
       2*(sourceSWClippedDyad434 u v i+1) := by
  dsimp [sourceSWClippedDyad434]
  rw [pow_succ]
  have ht : u*(2^i*2) = 2*(u*2^i) := by ring
  rw [ht]
  by_cases h : v ≤ u*2^i
  · rw [min_eq_left h]
    have hh : v ≤ 2*(u*2^i) := by omega
    rw [min_eq_left hh]
    omega
  · have hh : u*2^i ≤ v := by omega
    rw [min_eq_right hh]
    have hm : min v (2*(u*2^i)) ≤ 2*(u*2^i) := min_le_right _ _
    omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMovingDyadicExactSum -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- EXACT decomposition of the C38/C39 moving prime-character
interval into clipped dyadic subintervals. The original prefix
k, band (u,v], and moving GLOBAL log-cell cutoffs lo,hi remain
untouched; no artificial enlargement of a prime sum is made. -/
theorem source_original_exact_moving_dyadic_character_sum434
    (u v n a k lo hi : ℕ) (huv : u ≤ v) (hv : v ≤ u*2^n)
    (χ : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then χ p else 0) =
    ∑ i ∈ Finset.range n,
      ∑ p ∈ Finset.Ioc
        (max a (max (sourceSWClippedDyad434 u v i) lo))
        (min k (min (sourceSWClippedDyad434 u v (i+1)) hi)),
        if p.Prime then χ p else 0 := by
  classical
  let G : ℕ → ℂ := fun p => if p.Prime then χ p else 0
  let F : ℕ → ℂ := fun p =>
    if a < p ∧ lo < p ∧ p ≤ k ∧ p ≤ hi then G p else 0
  have hmask (x y : ℕ) :
      (∑ p ∈ Finset.Ioc x y, F p) =
      ∑ p ∈ Finset.Ioc (max a (max x lo)) (min k (min y hi)), G p := by
    dsimp [F]
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc,
      max_lt_iff, le_min_iff]
    tauto
  have hsum := source_original_exact_clipped_dyadic_partition434
    u v n huv hv F
  have hr :
      (∑ i ∈ Finset.range n,
        ∑ p ∈ Finset.Ioc
          (sourceSWClippedDyad434 u v i)
          (sourceSWClippedDyad434 u v (i+1)), F p) =
      ∑ i ∈ Finset.range n,
        ∑ p ∈ Finset.Ioc
          (max a (max (sourceSWClippedDyad434 u v i) lo))
          (min k (min (sourceSWClippedDyad434 u v (i+1)) hi)),
          G p := by
    apply Finset.sum_congr rfl
    intro i _
    exact hmask _ _
  change (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)), G p) = _
  exact (hmask u v).symm.trans (hsum.trans hr)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDyadicHarmonicPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact decomposition of the ORIGINAL prime-band harmonic summand
into clipped dyadic pieces. True source prime support, arbitrary
moving physical GLOBAL cell predicate, and weights are unchanged.
No absolute values or enlarged summation range are introduced. -/
theorem source_original_dyadic_harmonic_partition434
    (u v n : ℕ) (huv : u ≤ v) (hcover : v ≤ u * 2^n)
    (mu : ℕ → ℝ) (cell : ℕ → Prop) [DecidablePred cell]
    (chi : ℕ → ℂ) :
    (∑ p ∈ sourceOriginalActualPrimeBand434 u v,
      (mu p:ℂ) * (if cell p then chi p else 0)) =
    ∑ i ∈ Finset.range n,
      ∑ p ∈ sourceOriginalActualPrimeBand434
          (sourceSWClippedDyad434 u v i)
          (sourceSWClippedDyad434 u v (i+1)),
        (mu p:ℂ) * (if cell p then chi p else 0) := by
  classical
  let F : ℕ → ℂ := fun p =>
    if p.Prime then (mu p:ℂ) * (if cell p then chi p else 0) else 0
  have hsub (a b : ℕ) :
      (∑ p ∈ sourceOriginalActualPrimeBand434 a b,
        (mu p:ℂ) * (if cell p then chi p else 0)) =
      ∑ p ∈ Finset.Ioc a b, F p := by
    simp only [sourceOriginalActualPrimeBand434, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · simp [F, hprime]
    · simp [F, hprime]
  calc
    _ = ∑ p ∈ Finset.Ioc u v, F p := hsub u v
    _ = ∑ i ∈ Finset.range n,
          ∑ p ∈ Finset.Ioc
            (sourceSWClippedDyad434 u v i)
            (sourceSWClippedDyad434 u v (i+1)), F p :=
      source_original_exact_clipped_dyadic_partition434
        u v n huv hcover F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsub _ _).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFractionalDyadicSWReady -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact D-SW input data for an ORIGINAL C38 moving GLOBAL cell
at the ACTUAL fractional BIG-group scale exp(L^gamma).
The two source characters need not share their modulus;
the primitive inducing character is genuinely nonprincipal. -/
theorem source_original_fractional_moving_dyadic_SW_ready434
    (Q Cq u v a k lo hi : ℕ) (L gamma C : ℝ)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u) (hdyad : v ≤ 2*(u+1))
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    let η := sourceOriginalPrimitivePairQuotient434 Q c d
    η.primitiveCharacter.IsPrimitive ∧ η.primitiveCharacter ≠ 1 ∧
    (η.conductor:ℝ) ≤ (Real.log ((u+1:ℕ):ℝ))^C ∧
    ((u+1:ℕ):ℝ) ≤ ((max a (max u lo):ℕ):ℝ)+1 ∧
    ((min k (min v hi):ℕ):ℝ) ≤ 2*((u+1:ℕ):ℝ) ∧
    (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then star (c.2 (p:ZMod (c.1.val+1))) *
         d.2 (p:ZMod (d.1.val+1)) else 0) =
    (∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then η.primitiveCharacter (p:ZMod η.conductor)
       else 0) := by
  dsimp
  obtain ⟨hprim,hnon,hcond⟩ :=
    source_original_primitive_pair_SW_fractional_log_scale434
      Q Cq u L gamma C hL hgamma hC hExponent hQ huLarge
      c d hc hd hne
  have hleft : ((u+1:ℕ):ℝ) ≤
      ((max a (max u lo):ℕ):ℝ)+1 := by
    have h : u ≤ max a (max u lo) := by omega
    exact_mod_cast (Nat.add_le_add_right h 1)
  have hright : ((min k (min v hi):ℕ):ℝ) ≤
      2*((u+1:ℕ):ℝ) := by
    have h : min k (min v hi) ≤ 2*(u+1) := by omega
    exact_mod_cast h
  have hBIG : ∀ p ∈ Finset.Ioc (max a (max u lo))
      (min k (min v hi)), p.Prime → Q^2 < p := by
    intro p hp _
    have hpl := (Finset.mem_Ioc.mp hp).1
    omega
  refine ⟨hprim,hnon,hcond,hleft,hright,?_⟩
  exact source_original_primitive_pair_SW_interval_equal434
    Q c d (max a (max u lo)) (min k (min v hi)) hBIG
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMovingDyadicSWApplication -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Apply the exact SOURCE D Siegel–Walfisz statement (when available
in the same Lean kernel) to the genuine C38/C39 original primitive
character product, moving GLOBAL cell, and fractional BIG dyadic band.
The sole hypothesis hSW has exactly the pointwise conclusion of D's
verified theorem; it is not a Gram/frame norm hypothesis. -/
theorem source_original_moving_dyadic_SW_apply434
    (Q Cq u v a k lo hi : ℕ) (L gamma C A K : ℝ)
    (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u) (hdyad : v ≤ 2*(u+1))
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (hSW :
      ∀ (f aa bb : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
        χ.IsPrimitive → χ ≠ 1 →
        (f:ℝ) ≤ (Real.log ((u+1:ℕ):ℝ))^C →
        ((u+1:ℕ):ℝ) ≤ (aa:ℝ)+1 → aa ≤ bb →
        (bb:ℝ) ≤ 2*((u+1:ℕ):ℝ) →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then χ p else 0‖ ≤
        K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)) :
    ‖∑ p ∈ Finset.Ioc (max a (max u lo)) (min k (min v hi)),
       if p.Prime then
         star (c.2 (p:ZMod (c.1.val+1))) *
           d.2 (p:ZMod (d.1.val+1)) else 0‖ ≤
      K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A) := by
  let eta := sourceOriginalPrimitivePairQuotient434 Q c d
  let lower := max a (max u lo)
  let upper := min k (min v hi)
  obtain ⟨hprim, hnon, hcond, hleft, hright, heq⟩ :=
    source_original_fractional_moving_dyadic_SW_ready434
      Q Cq u v a k lo hi L gamma C hL hgamma hC
      hExponent hQ huLarge huBIG hdyad c d hc hd hne
  rw [heq]
  by_cases horder : lower ≤ upper
  · have hlevel : 0 < sourceOriginalPrimitiveCommonLevel434 Q c d := by
      unfold sourceOriginalPrimitiveCommonLevel434
      exact Nat.lcm_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    letI : NeZero (sourceOriginalPrimitiveCommonLevel434 Q c d) :=
      ⟨Nat.ne_of_gt hlevel⟩
    letI : NeZero eta.conductor := ⟨eta.conductor_ne_zero⟩
    exact hSW eta.conductor lower upper eta.primitiveCharacter
      hprim hnon hcond hleft horder hright
  · have hrev : upper ≤ lower := by omega
    have hy1 : (1:ℝ) ≤ ((u+1:ℕ):ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le u))
    have hy0 : 0 ≤ ((u+1:ℕ):ℝ) := by linarith
    have hnonneg :
        0 ≤ K*((u+1:ℕ):ℝ)*
             (Real.log ((u+1:ℕ):ℝ))^(-A) := by
      exact mul_nonneg (mul_nonneg hK hy0)
        (Real.rpow_nonneg (Real.log_nonneg hy1) _)
    change ‖∑ p ∈ Finset.Ioc lower upper,
      if p.Prime then eta.primitiveCharacter (p:ZMod eta.conductor)
      else 0‖ ≤ _
    rw [Finset.Ioc_eq_empty_of_le hrev]
    simpa only [Finset.sum_empty, norm_zero] using hnonneg
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeActiveCellWitness -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Each active source03 log-cell is witnessed by a TRUE complete
independent labelled prime tuple in the ORIGINAL finite product
support. The witness includes multiplicity of equal numerical
primes in distinct labelled slots. No synthetic continuous product
distribution or positive-mass surrogate is used. -/
theorem source_original_active_cell_true_product_witness434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h xi : ℝ) (hh : 0 < h)
    (j : ℤ)
    (hj : j ∈ sourceOriginalFiniteActiveLogCells434 S mu h xi) :
    ∃ a ∈ Fintype.piFinset S,
      sourceOriginalLiteralLogCell434 h j (∏ i : ι,a i) := by
  classical
  have hc : j ∈ sourceOriginalCandidateLogCells434 S h :=
    (Finset.mem_filter.mp hj).1
  obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hc
  refine ⟨a,ha,?_⟩
  rw [← heq]
  exact source_original_literal_log_cell_index_mem434
    h hh (∏ i : ι,a i)

/-- A source03 TRUE A-block active cell has a product witness
drawn from EXACTLY the source probe subset ν.A, not from a
fixed external comparison index type. -/
theorem source_original_probe_active_A_product_witness434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h xi : ℝ) (hh : 0 < h) (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsA434 m P V ν h xi) :
    ∃ a ∈ Fintype.piFinset (fun z : ν.1 => P z.val.1),
      sourceOriginalLiteralLogCell434 h j
        (∏ z : ν.1,a z) := by
  exact source_original_active_cell_true_product_witness434
    (fun z : ν.1 => P z.val.1)
    (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1))
    h xi hh j hj

theorem source_original_probe_active_B_product_witness434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h xi : ℝ) (hh : 0 < h) (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsB434 m P V ν h xi) :
    ∃ a ∈ Fintype.piFinset (fun z : ν.2 => P z.val.1),
      sourceOriginalLiteralLogCell434 h j
        (∏ z : ν.2,a z) := by
  exact source_original_active_cell_true_product_witness434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1))
    h xi hh j hj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeIndexedPrimes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5200000

/-- Canonical numeric index for the TRUE finite labelled source03
probe-slot family. The chosen equivFin bijection enumerates all
original slots exactly once. A missing out-of-range index is 1;
inside the true index interval no index is lost or duplicated. -/
noncomputable def sourceOriginalProbeIndexedPrime434
    {α : Type} [Fintype α]
    (a : α → ℕ) (n : ℕ) : ℕ :=
  if h : n < Fintype.card α then
    a ((Fintype.equivFin α).symm ⟨n,h⟩)
  else 1

/-- The product of a TRUE labelled source03 prime tuple is EXACTLY
its original numeric-index product required by
SourceComparisonData434.F1,p1 and F2,p2. This bijection keeps
repeated numerical primes in different labelled positions. -/
theorem source_original_probe_indexed_prime_product434
    {α : Type} [Fintype α]
    (a : α → ℕ) :
    (∏ n ∈ Finset.range (Fintype.card α),
      sourceOriginalProbeIndexedPrime434 a n) =
      ∏ z : α, a z := by
  classical
  let e := Fintype.equivFin α
  let f : Fin (Fintype.card α) → ℕ := fun j => a (e.symm j)
  calc
    _ = ∏ j : Fin (Fintype.card α),f j := by
      simpa only [sourceOriginalProbeIndexedPrime434, f, e] using
        (Finset.prod_fin_eq_prod_range (c:=f)).symm
    _ = ∏ z : α,a z := by
      have h := Fintype.prod_equiv e a f (by intro z; simp [f])
      exact h.symm

/-- The original numeric-index set of probes is nonempty whenever
the source03 selected probe set is nonempty. No artificially
introduced prime index is required. -/
theorem source_original_probe_indexed_support_nonempty434
    {α : Type} [Fintype α] [Nonempty α] :
    (Finset.range (Fintype.card α)).Nonempty := by
  classical
  have hCard : 0 < Fintype.card α :=
    Fintype.card_pos
  exact ⟨0,Finset.mem_range.mpr hCard⟩

/-- Source03 numeric-index probe coefficients keep EVERY true prime
support membership and individual lower prime bound. -/
theorem source_original_probe_indexed_prime_min434
    {α : Type} [Fintype α]
    (a : α → ℕ) (B : ℝ)
    (hMin : ∀ z, B ≤ (a z:ℝ))
    (n : ℕ) (hn : n ∈ Finset.range (Fintype.card α)) :
    B ≤ (sourceOriginalProbeIndexedPrime434 a n:ℝ) := by
  classical
  have hn' : n < Fintype.card α := Finset.mem_range.mp hn
  simpa only [sourceOriginalProbeIndexedPrime434,dif_pos hn'] using
    hMin ((Fintype.equivFin α).symm ⟨n,hn'⟩)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeConcreteC1Budget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- SOURCE03's original RAW + true two-global signed comparison
coefficient budget, without hFamilyBudget. All patterns are EXACT
pairs of nonempty designated probe subsets, all source comparison
coefficients use true primitive characters and logarithmic cells,
and each auxiliary label / unshared endpoint index varies with ν.

The sole source-specific cell assumptions are that the ACTIVE true
probability cells have mass >= ξ, as prescribed by source03.
The fixed final log-power exponent is independent of J. -/
theorem source_original_probe_concrete_raw_plus_C1_budget434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (L C0 : ℝ) (Q : ℕ) (xi : ℝ) (Cq Cxi : ℕ)
    (hL : 2 ≤ L) (hC0 : 0 ≤ C0)
    (hxi : 0 < xi)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0 * Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (JA JB : SourceOriginalProbePattern434 G m → Finset ℤ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (hMassA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JA ν, xi ≤ sourceOriginalProbeCellA434 m P V ν (hA ν) j)
    (hMassB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JB ν, xi ≤ sourceOriginalProbeCellB434 m P V ν (hB ν) j)
    (a : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target : (ν : SourceOriginalProbePattern434 G m) →
      ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    1 + (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalProbeConcreteKnu434
        J ell m hmJ ν Q (JA ν) (JB ν) (hA ν) (hB ν)
        P V (a ν) (source ν) (target ν)‖) ≤
    L^((m:ℝ)*C0*Real.log 2 + ((4*Cq+2*Cxi:ℕ):ℝ)+1) := by
  apply source_original_probe_raw_plus_cost_fixed_power434
    blockA blockB m Q L C0 xi Cq Cxi hL hC0 hxi hGroups hQ hXi
  exact source_original_probe_concrete_physical_Knu_family_bound434
    blockA blockB J ell m hmJ Q xi hxi
    P V JA JB hA hB hhA hhB hMassA hMassB a source target
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalKnu -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The FULLY CANONICAL source03 signed two-global comparison,
with the ORIGINAL ν-specific active log-cell families, genuine
Dirichlet primitive characters, true first-m free slot products,
and the unconditioned independent auxiliary prime values. -/
noncomputable def sourceOriginalProbeCanonicalKnu434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  sourceOriginalProbeConcreteKnu434 J ell m hmJ ν Q
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB P V a source target

/-- The fully canonical Knu is IDENTICAL to the original signed
source03 expression evaluated on the original full J+ell lists,
including ALL primitive characters of conductor <=Q and precisely
the j for which the true independent-prime probability ν_j>=xi. -/
theorem source_original_probe_canonical_full_physical_identity434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ ν Q hA hB xi
      P V a source target =
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalProbeDA434 m ν a)
      (sourceOriginalProbeOriginalTargetX434 J ell m hmJ ν
        (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared target))
      (sourceOriginalProbeDB434 m ν a)
      (sourceOriginalProbeOriginalSourceX434 J ell m hmJ ν
        (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared source))
      (ν.1.card+ν.2.card) := by
  exact source_original_probe_concrete_full_Knu_identity434
    J ell m hmJ ν Q
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB P V a shared source target

/-- The raw source03 pattern, plus all canonical physical comparison
kernels, obeys the ORIGINAL C1 fixed log-power budget with no
external hFamilyBudget or hMassA/B assumptions: those are now
theorems about the true finite active source probability cells. -/
theorem source_original_probe_canonical_raw_plus_C1_budget434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (L C0 : ℝ) (Q : ℕ) (xi : ℝ) (Cq Cxi : ℕ)
    (hL : 2 ≤ L) (hC0 : 0 ≤ C0) (hxi : 0 < xi)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0 * Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (a : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target : (ν : SourceOriginalProbePattern434 G m) →
      ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    1 + (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalProbeCanonicalKnu434 J ell m hmJ ν Q
        (hA ν) (hB ν) xi P V (a ν) (source ν) (target ν)‖) ≤
    L^((m:ℝ)*C0*Real.log 2 + ((4*Cq+2*Cxi:ℕ):ℝ)+1) := by
  apply source_original_probe_concrete_raw_plus_C1_budget434
    blockA blockB J ell m hmJ L C0 Q xi Cq Cxi
    hL hC0 hxi hGroups hQ hXi P V
    (fun ν => sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi)
    (fun ν => sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi)
    hA hB hhA hhB
  · intro ν hν j hj
    exact (source_original_probe_active_cell_A_mem_iff434
      m P V ν (hA ν) xi (hhA ν hν) hxi j).mp hj
  · intro ν hν j hj
    exact (source_original_probe_active_cell_B_mem_iff434
      m P V ν (hB ν) xi (hhB ν hν) hxi j).mp hj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeConcreteMarkedKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Literal true SOURCE03 marked comparison on the two ORIGINAL
(J+ell)-slot physical endpoint lists. The two complex endpoint
tests remain independent and the signed Knu is COUPLED. The
actual ν-dependent shared-slot complement is fixed canonically. -/
noncomputable def sourceOriginalProbeConcretePhysicalMark434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (src tgt : G → Fin (J+ell) → ℕ) : ℂ :=
  sourceAuxiliaryCoupledPatternMark434
    (J+ell)
    (sourceOriginalProbeSharedSlots434 J ell m hmJ ν)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν)
    bSrc bTgt
    (sourceOriginalProbeConcreteKnu434 J ell m hmJ ν Q JA JB hA hB
      P V a)
    src tgt

/-- Uniform source03 physical marked Knu cap for ALL real physical
source/target label states, with two separately bounded complex b
tests, true variable free-mark coordinates, and original signed Knu.
Nothing about conditional mark-test factorization is required. -/
theorem source_original_probe_concrete_physical_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (P : G → Finset ℕ) (V : G → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ sourceOriginalProbeCellA434 m P V ν hA j)
    (hMassB : ∀ j ∈ JB, xi ≤ sourceOriginalProbeCellB434 m P V ν hB j)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (hbSrc : ∀ u,‖bSrc u‖ ≤ 1)
    (hbTgt : ∀ u,‖bTgt u‖ ≤ 1)
    (src tgt : G → Fin (J+ell) → ℕ) :
    ‖sourceOriginalProbeConcretePhysicalMark434 J ell m hmJ ν Q
      JA JB hA hB P V a bSrc bTgt src tgt‖ ≤
    (Q:ℝ)^4*(xi⁻¹)^2 := by
  have hCap : 0 ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by positivity
  have hKnu (u v :
      ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
      ‖sourceOriginalProbeConcreteKnu434 J ell m hmJ ν Q JA JB hA hB
        P V a u v‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
    exact source_original_actual_primitive_physical_Knu_bound434
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
      Q xi hxi JA JB hA hB hhA hhB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      hMassA hMassB
      (sourceOriginalProbeDA434 m ν a)
      (sourceOriginalProbeDB434 m ν a)
      (ν.1.card+ν.2.card)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν)
      u v
  exact source_auxiliary_coupled_pattern_mark_bound434
    (J+ell)
    (sourceOriginalProbeSharedSlots434 J ell m hmJ ν)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν)
    bSrc bTgt
    (sourceOriginalProbeConcreteKnu434 J ell m hmJ ν Q JA JB hA hB
      P V a)
    ((Q:ℝ)^4*(xi⁻¹)^2) hCap hbSrc hbTgt hKnu src tgt

/-- The first-collision restriction of the literal SOURCE03
marked comparison has the SAME uniform cap even when the selected
auxiliary prime p also occurs in multiple distinct labelled slots. -/
theorem source_original_probe_concrete_collision_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (P : G → Finset ℕ) (V : G → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ sourceOriginalProbeCellA434 m P V ν hA j)
    (hMassB : ∀ j ∈ JB, xi ≤ sourceOriginalProbeCellB434 m P V ν hB j)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (hbSrc : ∀ u,‖bSrc u‖ ≤ 1)
    (hbTgt : ∀ u,‖bTgt u‖ ≤ 1)
    (p : ℕ) (src tgt : G → Fin (J+ell) → ℕ) :
    ‖if (∃ g j, src g
        ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p) ∨
      (∃ g j, tgt g
        ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p)
      then sourceOriginalProbeConcretePhysicalMark434 J ell m hmJ ν Q
        JA JB hA hB P V a bSrc bTgt src tgt
      else 0‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
  by_cases hhit :
    (∃ g j, src g
       ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p) ∨
    (∃ g j, tgt g
       ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p)
  · simpa only [if_pos hhit] using
      source_original_probe_concrete_physical_mark_bound434
        J ell m hmJ ν Q JA JB hA hB hhA hhB P V xi hxi
        hMassA hMassB a bSrc bTgt hbSrc hbTgt src tgt
  · simp only [if_neg hhit,norm_zero]
    positivity
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalMarkedKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Two original independently evaluated COMPLEX endpoint mark tests
and the TRUE canonical source03 signed two-primitive-kernel Knu.
The physical full lists are of length J+ell, the complement map
depends on the actual selected probes of this pattern. -/
noncomputable def sourceOriginalProbeCanonicalPhysicalMark434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (src tgt : G → Fin (J+ell) → ℕ) : ℂ :=
  sourceOriginalProbeConcretePhysicalMark434 J ell m hmJ ν Q
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB P V a bSrc bTgt src tgt

/-- The TRUE source03 physical marked coefficient is bounded with
no active-cell or character-family assumptions: finite active cells
and true character count have already been proved. Both endpoint
tests remain arbitrary complex functions bounded by one. -/
theorem source_original_probe_canonical_physical_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (hbSrc : ∀ u,‖bSrc u‖ ≤ 1)
    (hbTgt : ∀ u,‖bTgt u‖ ≤ 1)
    (src tgt : G → Fin (J+ell) → ℕ) :
    ‖sourceOriginalProbeCanonicalPhysicalMark434 J ell m hmJ ν Q
      hA hB xi P V a bSrc bTgt src tgt‖ ≤
      (Q:ℝ)^4*(xi⁻¹)^2 := by
  exact source_original_probe_concrete_physical_mark_bound434
    J ell m hmJ ν Q
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB hhA hhB P V xi hxi
    (fun j hj => (source_original_probe_active_cell_A_mem_iff434
      m P V ν hA xi hhA hxi j).mp hj)
    (fun j hj => (source_original_probe_active_cell_B_mem_iff434
      m P V ν hB xi hhB hxi j).mp hj)
    a bSrc bTgt hbSrc hbTgt src tgt

/-- The first-colliding auxiliary prime p can appear at either
endpoint. The same exact source03 canonical Knu cap survives the
physical collision indicator, with all additional occurrences
of p in other auxiliary coordinates permitted. -/
theorem source_original_probe_canonical_collision_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (bSrc bTgt :
      (∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) → ℂ)
    (hbSrc : ∀ u,‖bSrc u‖ ≤ 1)
    (hbTgt : ∀ u,‖bTgt u‖ ≤ 1)
    (p : ℕ) (src tgt : G → Fin (J+ell) → ℕ) :
    ‖if (∃ g j, src g
        ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p) ∨
      (∃ g j, tgt g
        ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g) j)=p)
      then sourceOriginalProbeCanonicalPhysicalMark434 J ell m hmJ ν Q
        hA hB xi P V a bSrc bTgt src tgt
      else 0‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
  exact source_original_probe_concrete_collision_mark_bound434
    J ell m hmJ ν Q
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB hhA hhB P V xi hxi
    (fun j hj => (source_original_probe_active_cell_A_mem_iff434
      m P V ν hA xi hhA hxi j).mp hj)
    (fun j hj => (source_original_probe_active_cell_B_mem_iff434
      m P V ν hB xi hhB hxi j).mp hj)
    a bSrc bTgt hbSrc hbTgt p src tgt
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalFibreInputs -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Source03's actual ν-dependent auxiliary law has positive
normalizations inherited from the true V_g reciprocal prime mass. -/
theorem source_original_probe_aux_norms_positive434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m) (V : G → ℝ)
    (hV : ∀ g,0 < V g) :
    ∀ z : SourceOriginalProbeAuxIndex434 m ν,
      0 < sourceOriginalProbeAuxV434 m ν V z := by
  intro z
  cases z with
  | inl a => exact hV a.val.1
  | inr b => exact hV b.val.1

theorem source_original_probe_aux_true_prime434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (hPrime : ∀ g p,p ∈ P g → p.Prime) :
    ∀ z : SourceOriginalProbeAuxIndex434 m ν,
      ∀ p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z,p.Prime := by
  intro z
  cases z with
  | inl a => exact hPrime a.val.1
  | inr b => exact hPrime b.val.1

theorem source_original_probe_aux_true_min434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (q : ℝ)
    (hMin : ∀ g p,p ∈ P g → q ≤ (p:ℝ)) :
    ∀ z : SourceOriginalProbeAuxIndex434 m ν,
      ∀ p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z,
        q ≤ (p:ℝ) := by
  intro z
  cases z with
  | inl a => exact hMin a.val.1
  | inr b => exact hMin b.val.1

theorem source_original_probe_aux_true_union434
    {G : Type} [Fintype G] [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) :
    ∀ z : SourceOriginalProbeAuxIndex434 m ν,
      ∀ p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z,
        p ∈ Finset.univ.biUnion P := by
  intro z p hp
  cases z with
  | inl a => exact Finset.mem_biUnion.mpr ⟨a.val.1,Finset.mem_univ _,hp⟩
  | inr b => exact Finset.mem_biUnion.mpr ⟨b.val.1,Finset.mem_univ _,hp⟩

/-- This discharges the ORIGINAL conditional first-collision
theorem's coupled-Knu cap for every true auxiliary tuple and physical
source/target marks: no separately assumed hKnu, no external
active-cell normalization and no hFamilyBudget. -/
theorem source_original_probe_canonical_Knu_true_uniform434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target :
      ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    ‖sourceOriginalProbeCanonicalKnu434 J ell m hmJ ν Q hA hB xi
       P V a source target‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
  exact source_original_actual_primitive_physical_Knu_bound434
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    Q xi hxi
    (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    hA hB hhA hhB
    (sourceOriginalProbeCellA434 m P V ν hA)
    (sourceOriginalProbeCellB434 m P V ν hB)
    (fun j hj => (source_original_probe_active_cell_A_mem_iff434
      m P V ν hA xi hhA hxi j).mp hj)
    (fun j hj => (source_original_probe_active_cell_B_mem_iff434
      m P V ν hB xi hhB hxi j).mp hj)
    (sourceOriginalProbeDA434 m ν a)
    (sourceOriginalProbeDB434 m ν a)
    (ν.1.card+ν.2.card)
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν)
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν)
    source target
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeBigOnlyPrimeMin -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Source03's comparisons free slots ONLY in the two designated
blocks of BIG prime groups. This holds for every ν in the
ACTUAL first-m probe comparison family, even though the
physical source/target lists also contain SMALL prime groups. -/
theorem source_original_probe_aux_groups_are_big434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
    ∀ i : SourceOriginalProbeAuxIndex434 m ν,
      (match i with
        | .inl a => a.val.1
        | .inr b => b.val.1) ∈ blockA ∪ blockB := by
  classical
  obtain ⟨_,hA,_,hB⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
  intro i
  cases i with
  | inl a =>
      have hMember : (a.val.1,a.val.2) ∈
          blockA.product (Finset.univ : Finset (Fin m)) :=
        hA a.property
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_product.mp hMember).1)
  | inr b =>
      have hMember : (b.val.1,b.val.2) ∈
          blockB.product (Finset.univ : Finset (Fin m)) :=
        hB b.property
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_product.mp hMember).1)

/-- True source03 lower prime bound in auxiliary comparisons:
it suffices to assume p>=exp(L^c) on BIG groups alone.
The SMALL groups remain entirely unrestricted at this exponent,
as required by the original sh:groups hypotheses.
This is the exact source-specific hMin premise needed in the
conditionally verified first-collision and dependent-family lemmas. -/
theorem source_original_probe_aux_big_only_prime_min434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (P : G → Finset ℕ) (L c : ℝ)
    (hBig : ∀ g ∈ blockA ∪ blockB,∀ p ∈ P g,
        Real.exp (L^c) ≤ (p:ℝ)) :
    ∀ i : SourceOriginalProbeAuxIndex434 m ν,
      ∀ p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i,
        Real.exp (L^c) ≤ (p:ℝ) := by
  intro i p hp
  have hG := source_original_probe_aux_groups_are_big434
    blockA blockB m ν hν i
  cases i with
  | inl a =>
      exact hBig a.val.1 hG p hp
  | inr b =>
      exact hBig b.val.1 hG p hp
end Green64Analytic.CorrelationSquare

end

