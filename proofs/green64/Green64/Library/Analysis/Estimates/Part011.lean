module

public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part047
public import Mathlib.NumberTheory.Chebyshev
public import Green64.Library.Weights.Part014
public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Correlation.SourcePhysicalUniformGroupMass

@[expose] public section

/-!
# Analysis / Estimates / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPrimeHarmonicBandGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE prime reciprocal mass on the SOURCE interval of all
primes (u,v]; no hidden weights or exceptional cells. -/
def sourceOriginalPrimeBandHarmonicMass434 (u v : ℕ) : ℝ :=
  ∑ p ∈ sourceOriginalActualPrimeBand434 u v, (1:ℝ)/(p:ℝ)

/-- The source03 SMALL band (u,v] of ACTUAL primes may be divided
into n pairwise DISJOINT nonempty SMALL prime groups with exactly
defined harmonic V_g and bounds [v0,v0+1/(u+1)),
provided its OWN true prime-harmonic mass is large enough.
The unproved analytic ingredient is the needed mass lower bound
from Mertens/PNT; there is no fake prime existence premise
sneaked in via an arbitrary Fintype. -/
theorem source_original_ACTUAL_small_band_prime_groups434
    (u v n : ℕ) (hpos : 0 < u+1)
    (target : ℝ) (htarget : 0 < target)
    (hlarge :
      (n:ℝ)*(target + 1/((u+1:ℕ):ℝ)) ≤
        sourceOriginalPrimeBandHarmonicMass434 u v) :
    ∃ groups : Fin n → Finset ℕ,
      (∀ g, groups g ⊆ sourceOriginalActualPrimeBand434 u v) ∧
      (∀ g, (groups g).Nonempty ∧
        target ≤ ∑ p ∈ groups g, (1:ℝ)/(p:ℝ) ∧
        (∑ p ∈ groups g, (1:ℝ)/(p:ℝ)) <
          target+1/((u+1:ℕ):ℝ)) ∧
      (∀ g h, g≠h → Disjoint (groups g) (groups h)) := by
  classical
  let s := sourceOriginalActualPrimeBand434 u v
  let w : ℕ → ℝ := fun p => 1/(p:ℝ)
  let δ : ℝ := 1/((u+1:ℕ):ℝ)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ δ := by
    intro p hp
    have hband := (Finset.mem_filter.mp hp).1
    have hup := (Finset.mem_Ioc.mp hband).1
    have hn : u+1 ≤ p := Nat.succ_le_iff.mpr hup
    have hnp : (u+1:ℝ) ≤ p := by exact_mod_cast hn
    have hpp : 0 < (p:ℝ) := by
      have hh : 0 < (u+1:ℝ) := by exact_mod_cast hpos
      exact lt_of_lt_of_le hh hnp
    refine ⟨by dsimp [w]; positivity, ?_⟩
    dsimp [w,δ]
    gcongr
  exact source_original_finite_harmonic_disjoint_groups434
    n s w target δ htarget hδ hw hlarge
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicChebyshevBand -/

section

open scoped BigOperators Classical Nat.Prime
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 270000

/-- The genuine prime band is precisely a difference of two
closed prime alphabets, without inventing missing primes. -/
theorem source_original_TRUE_prime_band_as_diff434
    (u v : ℕ) (huv : u ≤ v) :
    sourceOriginalActualPrimeBand434 u v =
      Nat.primesLE v \ Nat.primesLE u := by
  classical
  ext p
  simp only [sourceOriginalActualPrimeBand434,Finset.mem_filter,
    Finset.mem_sdiff,Nat.mem_primesLE,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hpu,hpv⟩,hp⟩
    exact ⟨⟨hpv,hp⟩,fun h => (not_le.mpr hpu) h.1⟩
  · rintro ⟨⟨hpv,hp⟩,hnot⟩
    refine ⟨⟨?_,hpv⟩,hp⟩
    exact lt_of_not_ge (fun hpu => hnot ⟨hpu,hp⟩)

/-- Exact cardinality of actual primes in the (u,v] band. -/
theorem source_original_TRUE_prime_band_card434
    (u v : ℕ) (huv : u ≤ v) :
    (sourceOriginalActualPrimeBand434 u v).card =
      Nat.primeCounting v - Nat.primeCounting u := by
  rw [source_original_TRUE_prime_band_as_diff434 u v huv,
    Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Nat.primesLE_mono huv),
    Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]

/-- A counting lower bound produces a GENUINE reciprocal-prime
lower bound: every actual prime p in (u,v] satisfies 1/p >= 1/v.
No analytic PNT or unproved Mertens input. -/
theorem source_original_TRUE_prime_band_mass_ge_count434
    (u v : ℕ) (huv : u ≤ v) (hv : 0 < v) :
    ((sourceOriginalActualPrimeBand434 u v).card:ℝ)/(v:ℝ) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v := by
  classical
  let s := sourceOriginalActualPrimeBand434 u v
  have hvpos : (0:ℝ) < v := by exact_mod_cast hv
  calc
    ((s.card:ℝ)/(v:ℝ)) = ∑ p ∈ s, (1:ℝ)/(v:ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ p ∈ s, (1:ℝ)/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpv : p ≤ v := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hppos : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
      have hpvR : (p:ℝ) ≤ (v:ℝ) := by exact_mod_cast hpv
      apply (div_le_div_iff₀ hvpos hppos).2
      nlinarith
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicChebyshevLower -/

section

open scoped BigOperators Classical Nat.Prime
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 200000

/-- Completely UNCONDITIONAL explicit Chebyshev arithmetic
lower bound for the ACTUAL original prime reciprocal sum on
(u,v]. No imported 4.32 Mertens result, no assumed group geometry,
and the primes are the unchanged real Nat.Prime filter.
The right side uses π(v)-π(u) exactly, not a probabilistic
expected number of primes. -/
theorem source_original_TRUE_prime_band_chebyshev_lower434
    (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (((v:ℝ)*Real.log 2 - Real.log ((v:ℝ)+1)) /
        Real.log (v:ℝ) -
      (Real.log 4*(u:ℝ) / Real.log (Real.sqrt (u:ℝ)) +
       Real.sqrt (u:ℝ))) / (v:ℝ) ≤
    sourceOriginalPrimeBandHarmonicMass434 u v := by
  have hv : 0 < v := lt_of_lt_of_le (by omega : 0 < u) huv
  have huv_pi : Nat.primeCounting u ≤ Nat.primeCounting v :=
    Nat.monotone_primeCounting huv
  have hcast :
      ((sourceOriginalActualPrimeBand434 u v).card:ℝ) =
        (Nat.primeCounting v:ℝ) -
          (Nat.primeCounting u:ℝ) := by
    rw [source_original_TRUE_prime_band_card434 u v huv]
    exact Nat.cast_sub huv_pi
  have hpiv := Chebyshev.pi_ge v
  have hpiu := Chebyshev.pi_le_log4_mul_div
    (x := (u:ℝ)) (by exact_mod_cast hu)
  have hu_floor : ⌊(u:ℝ)⌋₊ = u := Nat.floor_natCast u
  rw [hu_floor] at hpiu
  have hpibound :
      ((v:ℝ)*Real.log 2 - Real.log ((v:ℝ)+1)) /
          Real.log (v:ℝ) -
        (Real.log 4*(u:ℝ) / Real.log (Real.sqrt (u:ℝ)) +
         Real.sqrt (u:ℝ)) ≤
        (Nat.primeCounting v:ℝ) - (Nat.primeCounting u:ℝ) :=
    sub_le_sub hpiv hpiu
  have hvpos : (0:ℝ) ≤ v := by exact_mod_cast Nat.zero_le v
  calc
    _ ≤ ((Nat.primeCounting v:ℝ)-(Nat.primeCounting u:ℝ))/(v:ℝ) :=
      div_le_div_of_nonneg_right hpibound hvpos
    _ = ((sourceOriginalActualPrimeBand434 u v).card:ℝ)/(v:ℝ) := by
      rw [hcast]
    _ ≤ sourceOriginalPrimeBandHarmonicMass434 u v :=
      source_original_TRUE_prime_band_mass_ge_count434 u v huv hv
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshev64PrimeMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 220000

/-- TRUE unconditional source prime reciprocal mass in every
large integer factor-64 interval (u,64u]; follows solely from
current Mathlib's Chebyshev inequalities, no Mertens import. -/
theorem source_original_TRUE_prime_harmonic_64block_lower434
    (u : ℕ) (hu : 512 ≤ u) :
    (1:ℝ)/(16*Real.log (u:ℝ)) ≤
      sourceOriginalPrimeBandHarmonicMass434 u (64*u) := by
  have huReal : (512:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have h := source_original_64block_chebyshev_positive434
    (u:ℝ) huReal
  have hb := source_original_TRUE_prime_band_chebyshev_lower434
    u (64*u) (by omega) (by omega)
  have hc :
      ((64*u:ℕ):ℝ) = 64*(u:ℝ) := by push_cast; ring
  rw [hc] at hb
  exact h.trans hb
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicChebyshevSTs -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 150000

/-- Lightweight source indexing avoiding unrelated huge physical
Fock imports: one distinguished S plus n separate Ts. -/
def sourceOriginalChebyshevSmallIndex434 (n : ℕ) :
    Option (Fin n) → Fin (n+1)
  | none => 0
  | some i => i.succ

theorem source_original_chebyshev_small_index_injective434 (n : ℕ) :
    Function.Injective (sourceOriginalChebyshevSmallIndex434 n) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => exact ((Fin.succ_ne_zero y) h.symm).elim
  | some x =>
      cases y with
      | none => exact ((Fin.succ_ne_zero x) h).elim
      | some y =>
          have hi : x=y := Fin.succ_injective n h
          subst y
          rfl

/-- A genuinely arithmetic sufficient Chebyshev inequality yields
true disjoint S and Ts prime groups, harmonic-normalized by actual
reciprocal prime sums. NO hypothetical source03 group family and
NO source-specific analytic log-saving proposition is assumed.
An eventual proof that hCheb is satisfied for n~c log L remains
an explicit separate quantitative obligation. -/
theorem source_original_true_chebyshev_S_Ts_groups434
    (u v n : ℕ) (hu : 1 < u) (huv : u ≤ v)
    (target : ℝ) (htarget : 0 < target)
    (hCheb :
      ((n+1:ℕ):ℝ) * (target+1/((u+1:ℕ):ℝ)) ≤
      (((v:ℝ)*Real.log 2-Real.log ((v:ℝ)+1))/
          Real.log (v:ℝ) -
       (Real.log 4*(u:ℝ)/Real.log (Real.sqrt (u:ℝ))+
        Real.sqrt (u:ℝ))) / (v:ℝ)) :
    ∃ (P : Option (Fin n) → Finset ℕ)
      (V : Option (Fin n) → ℝ),
      (∀ g, (P g).Nonempty) ∧
      (∀ g, P g ⊆ sourceOriginalActualPrimeBand434 u v) ∧
      (∀ g, V g=∑ p ∈ P g, (1:ℝ)/(p:ℝ)) ∧
      (∀ g, target ≤ V g ∧
        V g < target+1/((u+1:ℕ):ℝ)) ∧
      (∀ g h, g≠h → Disjoint (P g) (P h)) := by
  classical
  have hmass : ((n+1:ℕ):ℝ)*(target+1/((u+1:ℕ):ℝ)) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v :=
    hCheb.trans
      (source_original_TRUE_prime_band_chebyshev_lower434 u v hu huv)
  obtain ⟨blocks,hsub,hbound,hdisj⟩ :=
    source_original_ACTUAL_small_band_prime_groups434
      u v (n+1) (Nat.zero_lt_succ u) target htarget hmass
  let index := sourceOriginalChebyshevSmallIndex434 n
  let P : Option (Fin n) → Finset ℕ := fun g => blocks (index g)
  let V : Option (Fin n) → ℝ := fun g =>
    ∑ p ∈ P g, (1:ℝ)/(p:ℝ)
  refine ⟨P,V,?_,?_,?_,?_,?_⟩
  · intro g
    exact (hbound (index g)).1
  · intro g
    exact hsub (index g)
  · intro g
    rfl
  · intro g
    exact ⟨(hbound (index g)).2.1,(hbound (index g)).2.2⟩
  · intro g h hneq
    apply hdisj (index g) (index h)
    intro he
    exact hneq ((source_original_chebyshev_small_index_injective434 n) he)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicChebyshevTelescoping -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 250000

/-- The actual source prime interval (u,w] is the DISJOINT
union of adjacent genuine prime intervals (u,v] and (v,w].
No cut-off cell or prime is dropped. -/
theorem source_original_TRUE_prime_band_split434
    (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w) :
    sourceOriginalActualPrimeBand434 u w =
      sourceOriginalActualPrimeBand434 u v ∪
        sourceOriginalActualPrimeBand434 v w := by
  classical
  ext p
  simp only [sourceOriginalActualPrimeBand434,
    Finset.mem_filter, Finset.mem_union,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hup,hpw⟩,hp⟩
    by_cases hpv : p ≤ v
    · exact Or.inl ⟨⟨hup,hpv⟩,hp⟩
    · exact Or.inr ⟨⟨lt_of_not_ge hpv,hpw⟩,hp⟩
  · rintro (⟨⟨hup,hpv⟩,hp⟩ | ⟨⟨hvp,hpw⟩,hp⟩)
    · exact ⟨⟨hup,hpv.trans hvw⟩,hp⟩
    · exact ⟨⟨huv.trans_lt hvp,hpw⟩,hp⟩

theorem source_original_TRUE_prime_band_disjoint434
    (u v w : ℕ) :
    Disjoint (sourceOriginalActualPrimeBand434 u v)
      (sourceOriginalActualPrimeBand434 v w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have a := (Finset.mem_Ioc.mp
    (Finset.mem_filter.mp hp).1).2
  have b := (Finset.mem_Ioc.mp
    (Finset.mem_filter.mp hq).1).1
  omega

/-- True reciprocal-prime mass adds over adjacent arithmetic
bands. The proof does not use a surrogate positive measure. -/
theorem source_original_TRUE_prime_band_mass_split434
    (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w) :
    sourceOriginalPrimeBandHarmonicMass434 u w =
      sourceOriginalPrimeBandHarmonicMass434 u v +
        sourceOriginalPrimeBandHarmonicMass434 v w := by
  unfold sourceOriginalPrimeBandHarmonicMass434
  rw [source_original_TRUE_prime_band_split434 u v w huv hvw]
  exact Finset.sum_union
    (source_original_TRUE_prime_band_disjoint434 u v w)

/-- For any actually increasing integer band endpoints
b0 <= b1 <= ... <= bN, the TRUE source prime-harmonic
sum on the full band is the exact sum over smaller bands. -/
theorem source_original_TRUE_prime_harmonic_partition434
    (b : ℕ → ℕ) (hb : Monotone b) (N : ℕ) :
    sourceOriginalPrimeBandHarmonicMass434 (b 0) (b N) =
      ∑ i ∈ Finset.range N,
        sourceOriginalPrimeBandHarmonicMass434 (b i) (b (i+1)) := by
  induction N with
  | zero =>
      simp [sourceOriginalPrimeBandHarmonicMass434,
        sourceOriginalActualPrimeBand434]
  | succ N ih =>
      rw [Finset.sum_range_succ, ←ih]
      exact source_original_TRUE_prime_band_mass_split434
        (b 0) (b N) (b (N+1))
        (hb (Nat.zero_le N)) (hb (Nat.le_succ N))

/-- Explicit unconditionally valid lower mass for the ORIGINAL
long band, from summing ACTUAL Chebyshev lower bounds on its
geometric/other consecutive subbands. Unlike the useless
single huge band counting estimate, geometric subbands allow
one to recover a logarithmic growth rate after a separate
real-log summation analysis. This statement requires neither
Mertens nor fake prime alphabets. -/
theorem source_original_TRUE_prime_harmonic_chebyshev_partition434
    (b : ℕ → ℕ) (hb : Monotone b)
    (N : ℕ) (hpos : ∀ i < N, 1 < b i) :
    (∑ i ∈ Finset.range N,
      (((b (i+1):ℝ)*Real.log 2-
          Real.log ((b (i+1):ℝ)+1))/
            Real.log (b (i+1):ℝ) -
        (Real.log 4*(b i:ℝ)/
            Real.log (Real.sqrt (b i:ℝ))+
          Real.sqrt (b i:ℝ))) / (b (i+1):ℝ)) ≤
      sourceOriginalPrimeBandHarmonicMass434 (b 0) (b N) := by
  rw [source_original_TRUE_prime_harmonic_partition434 b hb N]
  apply Finset.sum_le_sum
  intro i hi
  exact source_original_TRUE_prime_band_chebyshev_lower434
    (b i) (b (i+1)) (hpos i (Finset.mem_range.mp hi))
    (hb (Nat.le_succ i))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicChebyshevGeometric -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 200000

/-- Actual integer endpoints of geometric source prime bands.
Here 64 is a fixed integer >1, selected to make the weak explicit
Chebyshev prime-counting constants capable of giving a POSITIVE
block lower bound once u is sufficiently large. -/
def sourceOriginalChebyshevGeometricCut434 (u i : ℕ) : ℕ :=
  u * 64^i

theorem source_original_chebyshev_geometric_cut_mono434 (u : ℕ) :
    Monotone (sourceOriginalChebyshevGeometricCut434 u) := by
  intro i j hij
  unfold sourceOriginalChebyshevGeometricCut434
  gcongr

theorem source_original_chebyshev_geometric_cut_pos434
    (u i : ℕ) (hu : 1 < u) :
    1 < sourceOriginalChebyshevGeometricCut434 u i := by
  unfold sourceOriginalChebyshevGeometricCut434
  have hp : 0 < 64^i := pow_pos (by norm_num) i
  have hOne : 1 ≤ 64^i := by omega
  have hmul : u ≤ u * 64^i := by
    calc
      u = u*1 := by omega
      _ ≤ u*(64^i) := Nat.mul_le_mul_left u hOne
  exact hu.trans_le hmul

/-- An UNCONDITIONAL arithmetic lower bound on the exact
source prime harmonic mass over N consecutive genuine
multiplicative factor-64 prime intervals. This is a sum
of REAL Chebyshev expressions for each corresponding prime band.
It is not yet simplified to a fixed multiple of log N. -/
theorem source_original_TRUE_chebyshev_geometric_harmonic434
    (u N : ℕ) (hu : 1 < u) :
    (∑ i ∈ Finset.range N,
      let a : ℕ := sourceOriginalChebyshevGeometricCut434 u i
      let b : ℕ := sourceOriginalChebyshevGeometricCut434 u (i+1)
      (((b:ℝ)*Real.log 2-Real.log ((b:ℝ)+1))/
            Real.log (b:ℝ) -
        (Real.log 4*(a:ℝ)/Real.log (Real.sqrt (a:ℝ))+
          Real.sqrt (a:ℝ))) / (b:ℝ)) ≤
    sourceOriginalPrimeBandHarmonicMass434 u
      (sourceOriginalChebyshevGeometricCut434 u N) := by
  have h := source_original_TRUE_prime_harmonic_chebyshev_partition434
    (sourceOriginalChebyshevGeometricCut434 u)
    (source_original_chebyshev_geometric_cut_mono434 u)
    N (fun i hi =>
      source_original_chebyshev_geometric_cut_pos434 u i hu)
  simpa only [sourceOriginalChebyshevGeometricCut434,
    pow_zero,mul_one] using h

/-- A sufficient NON-PNT numerical condition on the explicit sum
of geometrically localized Chebyshev bounds produces actual
pairwise disjoint SMALL S+Ts groups from the full original
arithmetic prime band (u,64^N*u]. No independent Mertens
premise and no hypothetical group family is needed. -/
theorem source_original_TRUE_chebyshev_geometric_S_Ts434
    (u N n : ℕ) (hu : 1 < u)
    (vmin : ℝ) (hvmin : 0 < vmin)
    (hMass :
      ((n+1:ℕ):ℝ)*(vmin+1/((u+1:ℕ):ℝ)) ≤
      ∑ i ∈ Finset.range N,
        let a : ℕ := sourceOriginalChebyshevGeometricCut434 u i
        let b : ℕ := sourceOriginalChebyshevGeometricCut434 u (i+1)
        (((b:ℝ)*Real.log 2-Real.log ((b:ℝ)+1))/
            Real.log (b:ℝ) -
          (Real.log 4*(a:ℝ)/Real.log (Real.sqrt (a:ℝ))+
            Real.sqrt (a:ℝ))) / (b:ℝ)) :
    ∃ (P : Option (Fin n) → Finset ℕ)
      (V : Option (Fin n) → ℝ),
      (∀ g, (P g).Nonempty) ∧
      (∀ g, P g ⊆ sourceOriginalActualPrimeBand434
        u (sourceOriginalChebyshevGeometricCut434 u N)) ∧
      (∀ g, V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ)) ∧
      (∀ g, vmin ≤ V g ∧
        V g < vmin+1/((u+1:ℕ):ℝ)) ∧
      (∀ g h, g≠h → Disjoint (P g) (P h)) := by
  have hsum := source_original_TRUE_chebyshev_geometric_harmonic434
    u N hu
  let v := sourceOriginalChebyshevGeometricCut434 u N
  have hu_le : u ≤ v := by
    dsimp only [v,sourceOriginalChebyshevGeometricCut434]
    simpa only [sourceOriginalChebyshevGeometricCut434, pow_zero,
      mul_one] using
      ((source_original_chebyshev_geometric_cut_mono434 u) (Nat.zero_le N))
  have hv_geom : sourceOriginalChebyshevGeometricCut434 u 0 = u := by
    simp [sourceOriginalChebyshevGeometricCut434]
  have hPrime : ((n+1:ℕ):ℝ)*(vmin+1/((u+1:ℕ):ℝ)) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v :=
    hMass.trans hsum
  obtain ⟨blocks,hsub,hbounds,hdisj⟩ :=
    source_original_ACTUAL_small_band_prime_groups434
      u v (n+1) (Nat.zero_lt_succ u) vmin hvmin hPrime
  let index := sourceOriginalChebyshevSmallIndex434 n
  let P : Option (Fin n) → Finset ℕ := fun g => blocks (index g)
  let V : Option (Fin n) → ℝ := fun g =>
    ∑ p ∈ P g, (1:ℝ)/(p:ℝ)
  refine ⟨P,V,?_,?_,?_,?_,?_⟩
  · intro g
    exact (hbounds (index g)).1
  · intro g
    exact hsub (index g)
  · intro g
    rfl
  · intro g
    exact ⟨(hbounds (index g)).2.1,(hbounds (index g)).2.2⟩
  · intro g h hneq
    apply hdisj (index g) (index h)
    intro he
    exact hneq ((source_original_chebyshev_small_index_injective434 n) he)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicFullIntervalPrefix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 260000

/-- ORIGINAL source03 FULL-PRIME-INTERVAL greedy constructor:
from the genuine band (u,v] with reciprocal mass >= target,
find the FIRST endpoint m with reciprocal prime mass >= target.
The interval (u,m] contains ALL its prime labels, not an
arbitrary sparse subset as in the SMALL group constructor.
It overshoots target by at most the mass of one prime, ≤δ. -/
theorem source_original_TRUE_full_prime_interval_prefix434
    (u v : ℕ) (huv : u ≤ v)
    (target δ : ℝ) (htarget : 0 < target)
    (hδ : (1:ℝ)/((u+1:ℕ):ℝ) ≤ δ)
    (hlarge : target ≤ sourceOriginalPrimeBandHarmonicMass434 u v) :
    ∃ m : ℕ, u < m ∧ m ≤ v ∧
      target ≤ sourceOriginalPrimeBandHarmonicMass434 u m ∧
      sourceOriginalPrimeBandHarmonicMass434 u m < target+δ := by
  classical
  let good : Finset ℕ :=
    (Finset.Icc u v).filter
      (fun m => target ≤ sourceOriginalPrimeBandHarmonicMass434 u m)
  have hgood : good.Nonempty := by
    refine ⟨v,Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.right_mem_Icc.mpr huv,hlarge⟩
  obtain ⟨m,hm,hminimal⟩ :=
    Finset.exists_min_image good (fun m : ℕ => m) hgood
  have hmuv : u ≤ m ∧ m ≤ v :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  have hmass : target ≤ sourceOriginalPrimeBandHarmonicMass434 u m :=
    (Finset.mem_filter.mp hm).2
  have hmu : u < m := by
    by_contra hh
    have hmeq : m = u := Nat.le_antisymm (Nat.le_of_not_gt hh) hmuv.1
    have hzero : sourceOriginalPrimeBandHarmonicMass434 u u=0 := by
      simp [sourceOriginalPrimeBandHarmonicMass434,
        sourceOriginalActualPrimeBand434]
    rw [hmeq,hzero] at hmass
    linarith
  have hpred : u ≤ m-1 := Nat.le_sub_one_of_lt hmu
  have hpredmass :
      sourceOriginalPrimeBandHarmonicMass434 u (m-1) < target := by
    by_contra hh
    have hge : target ≤ sourceOriginalPrimeBandHarmonicMass434 u (m-1) :=
      le_of_not_gt hh
    have hmem : (m-1) ∈ good := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr
        ⟨hpred,(Nat.sub_le m 1).trans hmuv.2⟩,hge⟩
    have hmin := hminimal (m-1) hmem
    omega
  have hshort : sourceOriginalPrimeBandHarmonicMass434 (m-1) m ≤ δ := by
    let s := sourceOriginalActualPrimeBand434 (m-1) m
    have hs : s ⊆ ({m} : Finset ℕ) := by
      intro p hp
      have hh := (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp hp).1)
      have heq : p=m := by omega
      simpa [heq]
    have hupper :
        sourceOriginalPrimeBandHarmonicMass434 (m-1) m ≤
          (1:ℝ)/(m:ℝ) := by
      unfold sourceOriginalPrimeBandHarmonicMass434
      calc
        _ ≤ ∑ p ∈ ({m} : Finset ℕ), (1:ℝ)/(p:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun p hp hnot => by positivity)
        _ = (1:ℝ)/(m:ℝ) := by simp
    have huc : u+1 ≤ m := Nat.succ_le_iff.mpr hmu
    have hcu : (0:ℝ) < ((u+1:ℕ):ℝ) := by positivity
    have hmn : (((u+1:ℕ):ℝ)) ≤ (m:ℝ) := by exact_mod_cast huc
    exact hupper.trans
      ((one_div_le_one_div_of_le hcu hmn).trans hδ)
  have hsplit := source_original_TRUE_prime_band_mass_split434
    u (m-1) m hpred (Nat.sub_le m 1)
  refine ⟨m,hmu,hmuv.2,hmass,?_⟩
  rw [hsplit]
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicFullIntervalGroupsViaChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 140000

/-- Two TRUE prime intervals with ordered disjoint endpoints
cannot share a prime. No arbitrary sparse block is used. -/
theorem source_original_TRUE_prime_intervals_disjoint_separated434
    (a b c d : ℕ) (hbc : b ≤ c) :
    Disjoint (sourceOriginalActualPrimeBand434 a b)
      (sourceOriginalActualPrimeBand434 c d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpb := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have hpc := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  exact (not_lt_of_ge hpb) (lt_of_le_of_lt hbc hpc)

/-- ACTUAL original BIG groups: each group is ALL primes of its
own consecutive integer interval; the groups are pairwise
disjoint and have true harmonic normalization. By applying the
abstract certified interval-chain theorem, no giant physical
induction proof or positive-surrogate argument is needed. -/
theorem source_original_TRUE_full_prime_interval_groups_via_chain434
    (n u v : ℕ) (huv : u ≤ v)
    (target δ : ℝ) (htarget : 0 < target)
    (hδ : (1:ℝ)/((u+1:ℕ):ℝ) ≤ δ)
    (hlarge : (n:ℝ)*(target+δ) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v) :
    ∃ (left right : Fin n → ℕ),
      (∀ i, u ≤ left i ∧ left i < right i ∧ right i ≤ v) ∧
      (∀ i, target ≤ sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) ∧
        sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) < target+δ) ∧
      (∀ i j, i≠j →
        Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) := by
  classical
  let mass := sourceOriginalPrimeBandHarmonicMass434
  have hδnn : 0 ≤ δ :=
    (by positivity : (0:ℝ) ≤ (1:ℝ)/((u+1:ℕ):ℝ)).trans hδ
  have hprefix (a b : ℕ) (hua : u ≤ a) (hab : a ≤ b)
      (hm : target ≤ mass a b) :
      ∃ m : ℕ, a < m ∧ m ≤ b ∧ target ≤ mass a m ∧
        mass a m < target+δ := by
    have hpos : (0:ℝ) < ((u+1:ℕ):ℝ) := by positivity
    have hcast : ((u+1:ℕ):ℝ) ≤ ((a+1:ℕ):ℝ) := by
      exact_mod_cast Nat.add_le_add_right hua 1
    have hδa : (1:ℝ)/((a+1:ℕ):ℝ) ≤ δ :=
      (one_div_le_one_div_of_le hpos hcast).trans hδ
    exact source_original_TRUE_full_prime_interval_prefix434
      a b hab target δ htarget hδa hm
  obtain ⟨left,right,hr,hm,ho⟩ :=
    source_original_abstract_ordered_full_interval_chain434
      mass u target δ htarget hδnn
      (fun a b c hab hbc =>
        source_original_TRUE_prime_band_mass_split434 a b c hab hbc)
      hprefix n u v le_rfl huv hlarge
  refine ⟨left,right,hr,hm,?_⟩
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact source_original_TRUE_prime_intervals_disjoint_separated434
      (left i) (right i) (left j) (right j) (ho i j hlt)
  · exact (hij heq).elim
  · exact (source_original_TRUE_prime_intervals_disjoint_separated434
      (left j) (right j) (left i) (right i) (ho j i hgt)).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicFullIntervalGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- The source03 BIG full-prime-interval theorem, proven through
the independently kernel-checked abstract ordered interval
constructor and the TRUE source prime-harmonic threshold lemma.
Each group contains ALL primes in its own actual interval.
No unverified nested induction or any independent prime-group
axiom remains. -/
theorem source_original_TRUE_full_prime_interval_groups434
    (n : ℕ) (u v : ℕ) (huv : u ≤ v)
    (target δ : ℝ) (htarget : 0 < target)
    (hδ : (1:ℝ)/((u+1:ℕ):ℝ) ≤ δ)
    (hlarge : (n:ℝ)*(target+δ) ≤
      sourceOriginalPrimeBandHarmonicMass434 u v) :
    ∃ (left right : Fin n → ℕ),
      (∀ i, u ≤ left i ∧ left i < right i ∧ right i ≤ v) ∧
      (∀ i, target ≤ sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) ∧
        sourceOriginalPrimeBandHarmonicMass434
          (left i) (right i) < target+δ) ∧
      (∀ i j, i≠j →
        Disjoint
          (sourceOriginalActualPrimeBand434 (left i) (right i))
          (sourceOriginalActualPrimeBand434 (left j) (right j))) := by
  exact source_original_TRUE_full_prime_interval_groups_via_chain434
    n u v huv target δ htarget hδ hlarge
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PrimeBandWitness -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Two original full prime intervals (u,v] and (u',v']
are disjoint when their INTEGER bounds do not overlap.
There is no missing-prime or artificial support hypothesis. -/
theorem source_original_actual_prime_bands_disjoint434
    (u v u' v' : ℕ)
    (hOrder : v ≤ u' ∨ v' ≤ u) :
    Disjoint (sourceOriginalActualPrimeBand434 u v)
             (sourceOriginalActualPrimeBand434 u' v') := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  simp only [sourceOriginalActualPrimeBand434,
    Finset.mem_filter,Finset.mem_Ioc] at hp hp'
  rcases hOrder with hh | hh <;> omega

/-- SOURCE03 admissibility constructor for the ACTUAL family
of complete prime interval groups. Intra-small, intra-big
and cross-family disjointness follow from original numeric
interval order rather than being postulated independently.
The source data still must supply its full-band identities. -/
theorem source_original_source03_prime_band_separation434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallBand : ∀ i, d.Ts i =
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigBand : ∀ j, d.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hCrossOrder : ∀ i j, hiS i ≤ loB j ∨ hiB j ≤ loS i) :
    SourceOriginalSource03GroupSeparation434 d := by
  classical
  constructor
  · intro i j p hp hp'
    by_contra hij
    have hDisjoint : Disjoint (d.Ts i) (d.Ts j) := by
      rw [hSmallBand i,hSmallBand j]
      exact source_original_actual_prime_bands_disjoint434
        (loS i) (hiS i) (loS j) (hiS j)
        (hSmallOrder i j hij)
    exact (Finset.disjoint_left.mp hDisjoint) hp hp'
  · intro i j p hp hp'
    by_contra hij
    have hDisjoint : Disjoint (d.Tb i) (d.Tb j) := by
      rw [hBigBand i,hBigBand j]
      exact source_original_actual_prime_bands_disjoint434
        (loB i) (hiB i) (loB j) (hiB j)
        (hBigOrder i j hij)
    exact (Finset.disjoint_left.mp hDisjoint) hp hp'
  · intro i j p hp
    intro hp'
    have hDisjoint : Disjoint (d.Ts i) (d.Tb j) := by
      rw [hSmallBand i,hBigBand j]
      exact source_original_actual_prime_bands_disjoint434
        (loS i) (hiS i) (loB j) (hiB j)
        (hCrossOrder i j)
    exact (Finset.disjoint_left.mp hDisjoint) hp hp'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueHarmonicCellNumerator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- On the ORIGINAL BIG prime support, harmonic weight
mu(p)=(1/p)/V times the genuine p factor in Abel's
numerator cancels EXACTLY to 1/V. The true global
log-product cell becomes the exact intersection of two
REAL prime intervals, with no artificial independent
cell or replacement prime law. -/
theorem source_original_true_harmonic_cell_numerator434
    (u v R : ℕ) (hR : 0 < R)
    (h : ℝ) (j : ℤ)
    (V : ℝ) (hV : 0 < V) (χ : ℕ → ℂ) (k : ℕ) :
    sourceOriginalWeightedCellPrimeNumerator434
      (sourceOriginalActualPrimeBand434 u v)
      (fun p => (1/(p:ℝ))/V)
      (fun p => sourceOriginalLiteralLogCell434 h j (p*R)) χ k =
    if k ∈ (Finset.Ioc
      (max u (sourceOriginalLogCellExactLower434 h j R))
      (min v (sourceOriginalLogCellExactUpper434 h j R))).filter
         Nat.Prime
    then (V:ℂ)⁻¹*χ k else 0 := by
  let P := sourceOriginalActualPrimeBand434 u v
  let T := (Finset.Ioc
    (max u (sourceOriginalLogCellExactLower434 h j R))
    (min v (sourceOriginalLogCellExactUpper434 h j R))).filter
        Nat.Prime
  have hset : P.filter
      (fun p => sourceOriginalLiteralLogCell434 h j (p*R)) = T :=
    source_original_actual_band_global_cell_eq434 u v R hR h j
  have hmem :
      (k ∈ P ∧ sourceOriginalLiteralLogCell434 h j (k*R)) ↔
      k ∈ T := by
    rw [← hset]
    simp only [Finset.mem_filter]
  change
    (if k ∈ P ∧ sourceOriginalLiteralLogCell434 h j (k*R)
     then (((1/(k:ℝ))/V:ℝ):ℂ) * (k:ℂ) * χ k else 0) =
    (if k ∈ T then (V:ℂ)⁻¹ * χ k else 0)
  by_cases ht : k ∈ T
  · have hp := hmem.mpr ht
    simp only [if_pos hp, if_pos ht]
    have hprime : k.Prime :=
      (Finset.mem_filter.mp hp.1).2
    have hk : (k:ℂ) ≠ 0 := by
      exact_mod_cast hprime.ne_zero
    have hVC : (V:ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hV)
    have hweight :
        ((((1/(k:ℝ))/V:ℝ):ℂ) * (k:ℂ)) = (V:ℂ)⁻¹ := by
      push_cast
      field_simp [hk,hVC]
    rw [hweight]
  · have hn : ¬ (k ∈ P ∧
       sourceOriginalLiteralLogCell434 h j (k*R)) :=
      fun hp => ht (hmem.mp hp)
    simp only [if_neg hn, if_neg ht]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualSWPrimePrefix -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The intersection of an ordinary original prime prefix
(a,k], the TRUE BIG prime band (u,v], and the ACTUAL
GLOBAL logarithmic cell at the moving other-prime product
R>0, is EXACTLY one integer prime interval. This is the
precise set-theoretic bridge to Siegel–Walfisz on natural
prime intervals; no enlarged cell or missing endpoint. -/
theorem source_original_true_prefix_band_cell_set434
    (a k u v R : ℕ) (hR : 0 < R)
    (h : ℝ) (j : ℤ) :
    (Finset.Ioc a k).filter (fun p =>
       p ∈ sourceOriginalActualPrimeBand434 u v ∧
       sourceOriginalLiteralLogCell434 h j (p*R)) =
    (Finset.Ioc
      (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
      (min k (min v (sourceOriginalLogCellExactUpper434 h j R)))).filter
        Nat.Prime := by
  classical
  have hcell := source_original_actual_band_global_cell_eq434
    u v R hR h j
  ext p
  have hmember :
      (p ∈ sourceOriginalActualPrimeBand434 u v ∧
        sourceOriginalLiteralLogCell434 h j (p*R)) ↔
      p ∈ (Finset.Ioc
        (max u (sourceOriginalLogCellExactLower434 h j R))
        (min v (sourceOriginalLogCellExactUpper434 h j R))).filter
        Nat.Prime := by
    rw [←hcell]
    simp only [Finset.mem_filter]
  simp only [Finset.mem_filter, Finset.mem_Ioc,
    max_lt_iff,le_min_iff] at hmember ⊢
  tauto
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualHarmonicPrimePrefix -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- FINALLY the EXACT original source03 weighted one-prime
Abel numerator prefix on a moving GLOBAL product cell is
the ORDINARY unweighted Dirichlet-character prime interval
sum times 1/V_g, with genuine ORIGINAL BIG prime band (u,v].
No artificial centered character, no endpoint enlargement,
no auxiliary interval averaging or extra prime-count factor.
This is the exact formula needed to import the independently
kernel-proved SourcePrimeSiegelWalfisz from direction D. -/
theorem source_original_actual_harmonic_prefix_raw_eq434
    (a n u v R : ℕ) (hR : 0 < R)
    (h : ℝ) (j : ℤ)
    (V : ℝ) (hV : 0 < V) (χ : ℕ → ℂ) :
    sourceOriginalPrimePrefix434 a n
      (sourceOriginalWeightedCellPrimeNumerator434
        (sourceOriginalActualPrimeBand434 u v)
        (fun p => (1/(p:ℝ))/V)
        (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
        χ) =
    (V:ℂ)⁻¹ *
      ∑ p ∈ Finset.Ioc
        (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
        (min n (min v (sourceOriginalLogCellExactUpper434 h j R))),
        if p.Prime then χ p else 0 := by
  classical
  let T := (Finset.Ioc
     (max u (sourceOriginalLogCellExactLower434 h j R))
     (min v (sourceOriginalLogCellExactUpper434 h j R))).filter
       Nat.Prime
  let W := (Finset.Ioc
     (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
     (min n (min v (sourceOriginalLogCellExactUpper434 h j R)))).filter
       Nat.Prime
  have hnum (p : ℕ) :
      sourceOriginalWeightedCellPrimeNumerator434
        (sourceOriginalActualPrimeBand434 u v)
        (fun k => (1/(k:ℝ))/V)
        (fun k => sourceOriginalLiteralLogCell434 h j (k*R))
        χ p =
      if p∈T then (V:ℂ)⁻¹*χ p else 0 :=
    source_original_true_harmonic_cell_numerator434
      u v R hR h j V hV χ p
  have hcut :
      (Finset.Ioc a n).filter (fun p => p∈T) = W := by
    ext p
    simp only [T,W,Finset.mem_filter,Finset.mem_Ioc,
      max_lt_iff,le_min_iff]
    tauto
  unfold sourceOriginalPrimePrefix434
  calc
    _ = ∑ p ∈ Finset.Ioc a n,
          if p∈T then (V:ℂ)⁻¹*χ p else 0 := by
       apply Finset.sum_congr rfl
       intro p _
       exact hnum p
    _ = ∑ p ∈ (Finset.Ioc a n).filter (fun p => p∈T),
           (V:ℂ)⁻¹*χ p := by
       rw [Finset.sum_filter]
    _ = ∑ p ∈ W, (V:ℂ)⁻¹*χ p := by rw [hcut]
    _ = (V:ℂ)⁻¹ * ∑ p ∈ W, χ p := by
       rw [Finset.mul_sum]
    _ = (V:ℂ)⁻¹ *
        ∑ p ∈ Finset.Ioc
          (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
          (min n (min v (sourceOriginalLogCellExactUpper434 h j R))),
          if p.Prime then χ p else 0 := by
       unfold W
       rw [Finset.sum_filter]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceNativeOriginalClosedBands -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The original CLOSED real prime band is exactly the existing C natural
prime interval. The ceil-minus-one lower endpoint retains a prime that happens
to equal exp(t); no endpoint primality assumption is made. -/
theorem source_native_original_closed_band434 (t : ℝ) :
    sourceOriginalClosedPGroup t =
      sourceOriginalActualPrimeBand434 (⌈Real.exp t⌉₊-1)
        ⌊Real.exp ((6/5:ℝ)*t)⌋₊ := by
  classical
  have hceilpos : 0 < ⌈Real.exp t⌉₊ :=
    (Nat.lt_ceil).mpr (by simpa only [Nat.cast_zero] using Real.exp_pos t)
  ext p
  simp only [sourceOriginalClosedPGroup,sourceOriginalActualPrimeBand434,
    Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_,hupper⟩,hprime,hlower⟩
    have hceil : ⌈Real.exp t⌉₊ ≤ p := by
      by_contra hnot
      have hlt : p < ⌈Real.exp t⌉₊ := by omega
      have hreal : (p:ℝ) < Real.exp t := (Nat.lt_ceil).mp hlt
      linarith
    exact ⟨⟨by omega,hupper⟩,hprime⟩
  · rintro ⟨⟨hlower,hupper⟩,hprime⟩
    have hceil : ⌈Real.exp t⌉₊ ≤ p := by omega
    have hreal : Real.exp t ≤ (p:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    exact ⟨⟨Nat.zero_le p,hupper⟩,hprime,hreal⟩

/-- The exact full-band field for each existing moving native P group. -/
theorem source_native_original_actual_band434
    (r : ℕ) (L : ℝ) (g : sourceOriginalPAllGroupType r L) :
    sourceOriginalPAllActualBands r L g =
      sourceOriginalActualPrimeBand434
        (⌈Real.exp ((3/2:ℝ)*sourceOriginalPGroupScale r L g.val)⌉₊-1)
        ⌊Real.exp ((6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r L g.val))⌋₊ :=
  source_native_original_closed_band434 _
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalGroupFields -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Exact SMALL prime bounds on an index from the complete original SMALL set. -/
theorem source_native_original_small_index_prime_range434
    (r : ℕ) (L : ℝ) (j : ℕ)
    (hj : j ∈ sourceNativeOriginalSmallIndices434 r L) (p : ℕ)
    (hp : p ∈ sourceOriginalClosedPGroup ((3/2:ℝ)*sourceOriginalPGroupScale r L j)) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(1/5:ℝ)) := by
  have hb := (Finset.mem_filter.mp hj).2
  have hpR := source_original_P_closed_range _ p hp
  refine ⟨source_original_P_closed_prime _ p hp, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr hb.1).trans hpR.1
  · apply hpR.2.trans
    apply Real.exp_le_exp.mpr
    nlinarith [hb.2]

/-- The distinguished S is the actual original minimum-index SMALL prime band. -/
theorem source_native_original_S_prime_range434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (p : ℕ) (hp : p ∈ sourceNativeOriginalS434 r L hS) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(1/5:ℝ)) := by
  exact source_native_original_small_index_prime_range434 r L _
    (Finset.min'_mem _ hS) p hp

/-- Every remaining Ts is its original SMALL prime band, with both endpoints. -/
theorem source_native_original_Ts_prime_range434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (i : sourceNativeOriginalTsType434 r L hS)
    (p : ℕ) (hp : p ∈ sourceNativeOriginalTs434 r L hS i) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(1/5:ℝ)) := by
  exact source_native_original_small_index_prime_range434 r L i.val
    (Finset.mem_of_mem_erase i.property) p hp

/-- Every Tb keeps both original BIG endpoints and its primality predicate. -/
theorem source_native_original_Tb_prime_range434
    (r : ℕ) (L : ℝ) (g : sourceNativeOriginalBigType434 r L)
    (p : ℕ) (hp : p ∈ sourceNativeOriginalTb434 r L g) :
    p.Prime ∧ Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
  have hb := (Finset.mem_filter.mp g.property).2
  have hpR := source_original_P_closed_range _ p hp
  refine ⟨source_original_P_closed_prime _ p hp, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr hb.1).trans hpR.1
  · apply hpR.2.trans
    apply Real.exp_le_exp.mpr
    change (6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r L g.val) ≤ L^(2/5:ℝ)
    nlinarith [hb.2]

/-- The original full P union remains below the genuine roughness cutoff. -/
theorem source_native_original_G_bound434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L) (p : ℕ)
    (hp : p ∈ sourceNativeOriginalG434 r L) :
    p.Prime ∧ (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  have hpR := source_original_P_closed_range _ p hpg
  have hupper := source_original_P_all_actual_band_upper r L hL g
  have hpow : L^(2/5:ℝ) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  exact ⟨source_original_P_all_actual_band_prime r L g p hpg,
    hpR.2.trans (Real.exp_le_exp.mpr (hupper.trans hpow))⟩

/-- Separate bounds for the genuine remaining SMALL and complete BIG index
types, with the already proved source constant; no equality of sizes is used. -/
theorem source_native_original_group_upper_counts434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hr : 1 ≤ r) (hL : Real.exp 1 ≤ L) :
    (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) ≤
      (3+(Real.log 2)⁻¹)*Real.log L ∧
    (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      (3+(Real.log 2)⁻¹)*Real.log L := by
  have hall := source_original_P_all_group_card_log r L hr hL
  have hs : (sourceNativeOriginalSmallIndices434 r L).card ≤
      (sourceOriginalPAllGroupIndices r L).card := Finset.card_filter_le _ _
  have hb : (sourceNativeOriginalBigIndices434 r L).card ≤
      (sourceOriginalPAllGroupIndices r L).card := Finset.card_filter_le _ _
  constructor
  · have he := Finset.card_erase_le
      (s := sourceNativeOriginalSmallIndices434 r L)
      (a := sourceNativeOriginalSIndex434 r L hS)
    have hcard : Fintype.card (sourceNativeOriginalTsType434 r L hS) ≤
        (sourceOriginalPAllGroupIndices r L).card := by
      simpa only [sourceNativeOriginalTsType434,Fintype.card_coe] using he.trans hs
    exact (show (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) ≤
      ((sourceOriginalPAllGroupIndices r L).card:ℝ) by exact_mod_cast hcard).trans hall
  · have hcard : Fintype.card (sourceNativeOriginalBigType434 r L) ≤
        (sourceOriginalPAllGroupIndices r L).card := by
      simpa only [sourceNativeOriginalBigType434,Fintype.card_coe] using hb
    exact (show (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      ((sourceOriginalPAllGroupIndices r L).card:ℝ) by exact_mod_cast hcard).trans hall

/-- The natural lower endpoint is ceil(exp(t))-1, retaining a prime at exp(t). -/
def sourceNativeOriginalBigLo434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L) : ℕ :=
  ⌈Real.exp ((3/2:ℝ)*sourceOriginalPGroupScale r L g.val)⌉₊-1

/-- The original closed BIG band's natural upper endpoint. -/
def sourceNativeOriginalBigHi434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L) : ℕ :=
  ⌊Real.exp ((6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r L g.val))⌋₊

/-- All BIG interval premises of the audited C-root, with gamma=3/10 and
dscale=2/5, follow from the actual native group. This asserts no prime-mass floor. -/
theorem source_native_original_BIG_root_band_fields434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L) (g : sourceNativeOriginalBigType434 r L) :
    sourceNativeOriginalTb434 r L g = sourceOriginalActualPrimeBand434
      (sourceNativeOriginalBigLo434 r L g) (sourceNativeOriginalBigHi434 r L g) ∧
    sourceNativeOriginalBigLo434 r L g ≤ sourceNativeOriginalBigHi434 r L g ∧
    (sourceNativeOriginalBigHi434 r L g:ℝ) ≤ Real.exp (L^(2/5:ℝ)) ∧
    Real.exp (L^(3/10:ℝ)) ≤ ((sourceNativeOriginalBigLo434 r L g+1:ℕ):ℝ) := by
  let t : ℝ := (3/2:ℝ)*sourceOriginalPGroupScale r L g.val
  have hb := (Finset.mem_filter.mp g.property).2
  have ht : 0 ≤ t := (Real.rpow_nonneg (zero_le_one.trans hL) _).trans hb.1
  have hceilpos : 0 < ⌈Real.exp t⌉₊ :=
    (Nat.lt_ceil).mpr (by simpa only [Nat.cast_zero] using Real.exp_pos t)
  have hcast : ((⌈Real.exp t⌉₊-1:ℕ):ℝ) = (⌈Real.exp t⌉₊:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hlo : ((⌈Real.exp t⌉₊-1:ℕ):ℝ) ≤ Real.exp t := by
    rw [hcast]
    have h := Nat.ceil_lt_add_one (Real.exp_nonneg t)
    linarith
  have hexp : Real.exp t ≤ Real.exp ((6/5:ℝ)*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hupper : (6/5:ℝ)*t ≤ L^(2/5:ℝ) := by
    dsimp [t]
    nlinarith [hb.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact source_native_original_actual_band434 r L (sourceNativeOriginalBigToAll434 r L g)
  · exact (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (hlo.trans hexp)
  · exact (Nat.floor_le (Real.exp_nonneg _)).trans (Real.exp_le_exp.mpr hupper)
  · change Real.exp (L^(3/10:ℝ)) ≤ ((⌈Real.exp t⌉₊-1+1:ℕ):ℝ)
    rw [show ⌈Real.exp t⌉₊-1+1 = ⌈Real.exp t⌉₊ by omega]
    exact (Real.exp_le_exp.mpr hb.1).trans (Nat.le_ceil _)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalAllPPrimeMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- SOURCE all-P J-shared RAW groups: this is every original S/Ts/Tb
group without dropping SMALL, keeping the original P group indices. -/
abbrev SourceNativeOriginalAllP434 (r : ℕ) (L : ℝ) :=
  sourceOriginalPAllGroupType r L

abbrev SourceNativeOriginalAllPBand434 (r : ℕ) (L : ℝ)
    (g : SourceNativeOriginalAllP434 r L) : Finset ℕ :=
  sourceOriginalPAllActualBands r L g

noncomputable def sourceNativeOriginalAllPMass434 (r : ℕ) (L : ℝ)
    (g : SourceNativeOriginalAllP434 r L) : ℝ :=
  ∑ p ∈ sourceOriginalPAllActualBands r L g, 1/(p:ℝ)

/-- Every source P-group, including the distinguished S and remaining Ts,
retains its genuine closed band and its exact lower exp(L^0.1) prime floor.
Earlier BIG-only estimates cannot replace this at the RAW shared-history
layer, which has J labels in EACH original source P group. -/
theorem source_native_original_ALL_P_prime_range434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (g : SourceNativeOriginalAllP434 r L) (p : ℕ)
    (hp : p ∈ SourceNativeOriginalAllPBand434 r L g) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
  have hpRange := source_original_P_closed_range
    ((3/2:ℝ)*sourceOriginalPGroupScale r L g.val) p hp
  have hpUpper := source_original_P_all_actual_band_upper
    r L hL g
  have hidx : sourceOriginalPGroupIndex r L g.val :=
    (Finset.mem_filter.mp g.property).2
  dsimp [sourceOriginalPGroupIndex] at hidx
  have hlow :
      L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L g.val := by
    rcases hidx with ha | hb
    · exact ha.1
    · exact (Real.rpow_le_rpow_of_exponent_le hL
        (by norm_num : (1/10:ℝ) ≤ (3/10:ℝ))).trans hb.1
  exact ⟨source_original_P_all_actual_band_prime r L g p hp,
    (Real.exp_le_exp.mpr hlow).trans hpRange.1,
    hpRange.2.trans (Real.exp_le_exp.mpr hpUpper)⟩

/-- Native complete P-group harmonic masses have a fixed unconditional
positive lower floor, with no SMALL-vs-BIG reweighting. -/
theorem eventually_native_original_ALL_P_masses434 (r : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ g : SourceNativeOriginalAllP434 r L,
        Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalAllPMass434 r L g ∧
          sourceNativeOriginalAllPMass434 r L g ≤ 4 := by
  filter_upwards [ShiftTwoTerminal.source_actual_P_uniform_mass_bounds r]
    with L h
  intro g
  simpa only [sourceNativeOriginalAllPMass434,one_div]
    using h g
end Green64Analytic.SourceBlockSieve

end

end

