module

public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Weights.Part028

@[expose] public section

/-!
# Correlation / MemoryActualDomain

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeMemoryActualDomain -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev SourceNativeMemorySG434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :=
  Option (sourceNativeOriginalTsType434 r L hS)

abbrev SourceNativeMemorySP434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS) : Type :=
  {p : ℕ // p ∈ match g with
    | none => sourceNativeOriginalS434 r L hS
    | some i => sourceNativeOriginalTs434 r L hS i}

abbrev SourceNativeMemoryBP434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L) : Type :=
  {p : ℕ // p ∈ sourceNativeOriginalTb434 r L g}

abbrev SourceNativeMemorySmallMass434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS) : ℝ :=
  match g with
  | none => sourceNativeOriginalVs434 r L hS
  | some i => sourceNativeOriginalVsmall434 r L hS i

theorem source_native_memory_small_prime434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS)
    (p : SourceNativeMemorySP434 r L hS g) : p.val.Prime := by
  cases g with
  | none => exact (source_native_original_S_prime_range434 r L hS p.val p.property).1
  | some i => exact (source_native_original_Ts_prime_range434 r L hS i p.val p.property).1

theorem source_native_memory_big_prime434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L)
    (p : SourceNativeMemoryBP434 r L g) : p.val.Prime :=
  (source_native_original_Tb_prime_range434 r L g p.val p.property).1

private theorem source_native_memory_small_mass_eq434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS) :
    SourceNativeMemorySmallMass434 r L hS g =
      ∑ p : SourceNativeMemorySP434 r L hS g, 1/(p.val:ℝ) := by
  cases g with
  | none =>
    simpa [SourceNativeMemorySmallMass434, sourceNativeOriginalVs434,
      SourceNativeMemorySP434, one_div] using
      (Finset.sum_attach (sourceNativeOriginalS434 r L hS)
        (fun p => (p:ℝ)⁻¹)).symm
  | some i =>
    simpa [SourceNativeMemorySmallMass434, sourceNativeOriginalVsmall434,
      SourceNativeMemorySP434, one_div] using
      (Finset.sum_attach (sourceNativeOriginalTs434 r L hS i)
        (fun p => (p:ℝ)⁻¹)).symm

private theorem source_native_memory_big_mass_eq434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L) :
    sourceNativeOriginalVbig434 r L g =
      ∑ p : SourceNativeMemoryBP434 r L g, 1/(p.val:ℝ) := by
  simpa [sourceNativeOriginalVbig434, SourceNativeMemoryBP434, one_div] using
    (Finset.sum_attach (sourceNativeOriginalTb434 r L g) (fun p => (p:ℝ)⁻¹)).symm

instance sourceNativeMemorySmallModNonzero434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS)
    (p : SourceNativeMemorySP434 r L hS g) : NeZero p.val :=
  ⟨(source_native_memory_small_prime434 r L hS g p).ne_zero⟩

instance sourceNativeMemoryBigModNonzero434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L)
    (p : SourceNativeMemoryBP434 r L g) : NeZero p.val :=
  ⟨(source_native_memory_big_prime434 r L g p).ne_zero⟩

private theorem source_native_memory_sigma_injective434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (hSep : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    Function.Injective (fun x : Σ g : G, {p : ℕ // p ∈ P g} => x.2.val) := by
  intro x y hxy
  rcases x with ⟨g, p⟩
  rcases y with ⟨h, q⟩
  change p.val = q.val at hxy
  have hmem : p.val ∈ P h := hxy ▸ q.property
  have hg : g = h := hSep g h p.val p.property hmem
  cases hg
  have hp : p = q := Subtype.ext hxy
  cases hp
  rfl

abbrev SourceNativeMemorySmallSet434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS) : Finset ℕ :=
  match g with
  | none => sourceNativeOriginalS434 r L hS
  | some i => sourceNativeOriginalTs434 r L hS i

private theorem source_native_memory_small_group_eq434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g h : SourceNativeMemorySG434 r L hS) (p : ℕ)
    (hp : p ∈ SourceNativeMemorySmallSet434 r L hS g)
    (hq : p ∈ SourceNativeMemorySmallSet434 r L hS h) : g = h := by
  have hSep := source_native_original_small_group_disjoint434 r L hS hr hL
  cases g with
  | none =>
    cases h with
    | none => rfl
    | some j => exact False.elim ((Finset.disjoint_left.mp (hSep.1 j)) hp hq)
  | some i =>
    cases h with
    | none => exact False.elim ((Finset.disjoint_left.mp (hSep.1 i)) hq hp)
    | some j =>
      by_cases hij : i = j
      · subst j; rfl
      · exact False.elim ((Finset.disjoint_left.mp (hSep.2.2.1 hij)) hp hq)

private theorem source_native_memory_big_group_eq434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g h : sourceNativeOriginalBigType434 r L) (p : ℕ)
    (hp : p ∈ sourceNativeOriginalTb434 r L g)
    (hq : p ∈ sourceNativeOriginalTb434 r L h) : g = h := by
  by_contra hne
  have hSep := source_native_original_small_group_disjoint434 r L hS hr hL
  exact (Finset.disjoint_left.mp (hSep.2.2.2.1 hne)) hp hq

private theorem source_native_memory_small_big_disjoint434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS)
    (h : sourceNativeOriginalBigType434 r L) (p : ℕ)
    (hp : p ∈ SourceNativeMemorySmallSet434 r L hS g)
    (hq : p ∈ sourceNativeOriginalTb434 r L h) : False := by
  have hSep := source_native_original_small_group_disjoint434 r L hS hr hL
  cases g with
  | none => exact (Finset.disjoint_left.mp (hSep.2.1 h)) hp hq
  | some i => exact (Finset.disjoint_left.mp (hSep.2.2.2.2 i h)) hp hq

private theorem source_native_memory_small_lower434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (g : SourceNativeMemorySG434 r L hS)
    (p : SourceNativeMemorySP434 r L hS g) :
    Real.exp (L^(1/10:ℝ)) ≤ (p.val:ℝ) := by
  cases g with
  | none => exact (source_native_original_S_prime_range434 r L hS p.val p.property).2.1
  | some i => exact (source_native_original_Ts_prime_range434 r L hS i p.val p.property).2.1

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Full actual SMALL/BIG domain, with numeric gates still to be derived
from the original signed native Type-II windows. All group types, fibres,
prime masses and the cap are the literal source groups, not surrogate data. -/
theorem source_native_memory_domain_of_numeric_gates434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (q rho : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hrhoSq : Real.sqrt q < rho^2)
    (k : ℤ) (hk : k ≠ 0)
    (hK : (k.natAbs:ℝ) < Real.exp (L^(1/10:ℝ)))
    (R : ℕ) (hR : 0 < R)
    (hVisits : ((2*R+1:ℕ):ℝ) < Real.exp (L^(3/10:ℝ)))
    (hVs : 0 < sourceNativeOriginalVs434 r L hS)
    (hTs : ∀ i, 0 < sourceNativeOriginalVsmall434 r L hS i)
    (hTb : ∀ g, 0 < sourceNativeOriginalVbig434 r L g) :
    MemorySourceDomain
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (fun g => (sourceNativeOriginalTb434 r L g).card)
      q rho (SourceNativeMemorySmallMass434 r L hS)
      (sourceNativeOriginalVbig434 r L) k R := by
  classical
  have hBigPow : L^(1/10:ℝ) ≤ L^(3/10:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hL) (by norm_num)
  have hBigK : (k.natAbs:ℝ) < Real.exp (L^(3/10:ℝ)) :=
    hK.trans_le (Real.exp_le_exp.mpr hBigPow)
  refine {
    q_pos := hq0
    q_lt_one := hq1
    rho_pos := hrho0
    rho_lt_one := hrho1
    rho_sq := hrhoSq
    R_pos := hR
    k_ne := hk
    small_prime := ?_
    big_prime := ?_
    small_injective := ?_
    big_injective := ?_
    disjoint := ?_
    small_above_k := ?_
    big_above_k := ?_
    big_above_visits := ?_
    Vsmall_eq := ?_
    Vbig_eq := ?_
    Vsmall_pos := ?_
    Vbig_pos := ?_
    cap_saturated := ?_
  }
  · intro g p
    exact source_native_memory_small_prime434 r L hS g p
  · intro g p
    exact source_native_memory_big_prime434 r L g p
  · exact source_native_memory_sigma_injective434
      (SourceNativeMemorySmallSet434 r L hS)
      (source_native_memory_small_group_eq434 r L hr hL hS)
  · exact source_native_memory_sigma_injective434
      (sourceNativeOriginalTb434 r L)
      (source_native_memory_big_group_eq434 r L hr hL hS)
  · intro gs ps gb pb hEq
    apply source_native_memory_small_big_disjoint434
      r L hr hL hS gs gb ps.val ps.property
    simpa [hEq] using pb.property
  · intro g p
    have hp := source_native_memory_small_lower434 r L hS g p
    exact_mod_cast hK.trans_le hp
  · intro g p
    have hp := (source_native_original_Tb_prime_range434 r L g p.val p.property).2.1
    exact_mod_cast hBigK.trans_le hp
  · intro g p
    have hp := (source_native_original_Tb_prime_range434 r L g p.val p.property).2.1
    exact_mod_cast hVisits.trans_le hp
  · intro g
    exact source_native_memory_small_mass_eq434 r L hS g
  · intro g
    exact source_native_memory_big_mass_eq434 r L g
  · intro g
    cases g with
    | none => exact hVs
    | some i => exact hTs i
  · intro g
    exact hTb g
  · intro g
    simp [SourceNativeMemoryBP434]
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
open Filter
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- After the established native reciprocal-mass theorem, the complete
actual memory domain needs only signed shift/visit numeric gates and the
fixed physical contraction parameters. Every band and mass is literal. -/
theorem eventually_source_native_memory_domain434
    (r : ℕ) (hr : 1 ≤ r)
    (q rho : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hrhoSq : Real.sqrt q < rho^2)
    (k : ℝ → ℤ) (R : ℝ → ℕ)
    (hk : ∀ᶠ L : ℝ in atTop, k L ≠ 0)
    (hK : ∀ᶠ L : ℝ in atTop,
      (((k L).natAbs:ℕ):ℝ) < Real.exp (L^(1/10:ℝ)))
    (hR : ∀ᶠ L : ℝ in atTop, 0 < R L)
    (hVisits : ∀ᶠ L : ℝ in atTop,
      ((2*(R L)+1:ℕ):ℝ) < Real.exp (L^(3/10:ℝ))) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧
      ∀ hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty,
        MemorySourceDomain
          (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
          (fun g => (sourceNativeOriginalTb434 r L g).card)
          q rho (SourceNativeMemorySmallMass434 r L hS)
          (sourceNativeOriginalVbig434 r L) (k L) (R L) := by
  classical
  have hFloor : 0 < Real.log (6/5:ℝ)/2 :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  filter_upwards [eventually_source_native_original_group_masses434 r hr,
    hk, hK, hR, hVisits] with L hMass hkL hKL hRL hVisitsL
  refine ⟨hMass.1, ?_⟩
  intro hS
  have hm := hMass.2.2 hS
  exact source_native_memory_domain_of_numeric_gates434
    r L hr hMass.1 hS q rho hq0 hq1 hrho0 hrho1 hrhoSq
    (k L) hkL hKL (R L) hRL hVisitsL
    (hFloor.trans_le hm.1.1)
    (fun i => hFloor.trans_le (hm.2.1 i).1)
    (fun g => hFloor.trans_le (hm.2.2 g).1)
end Green64Analytic.SourceBlockSieve

end

end

