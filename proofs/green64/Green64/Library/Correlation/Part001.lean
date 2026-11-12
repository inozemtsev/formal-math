module

public import Green64.Library.Correlation.PhysicalPermutationLegalCounterexample
public import Green64.Library.Weights.Part002
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Weights.Part009
public import Green64.Library.Analysis.Estimates.Part003
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part001
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Analysis.Estimates.SourceDivisorPrimePowerComparison
public import Mathlib.Algebra.Order.Floor.Semiring
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# Correlation / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalOrientedBigEdge -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Unshared positions of the PATTERN in the ordered frame lying
between the two independently sampled endpoint permutations. -/
noncomputable def orientedUnshared
    (shared : Finset (Fin M)) : Finset (Fin M) :=
  Finset.univ \ shared

noncomputable def orientedFresh
    (shared promote : Finset (Fin M)) : Finset (Fin M) :=
  orientedUnshared M shared \ promote

/-- This is the source's unsymmetrized BIG edge legality with
the independently permuted ordered endpoints, OLD-index injections,
the single Delta, actual store/promotion divisibility exclusions
and the Fock capacity. -/
structure OrientedBigEdgeLegal
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) : Prop where
  shared_copy : ∀ j ∈ shared, x.1 (sigma j) = target (tau j)
  stores_unshared : c.1 ⊆ orientedUnshared M shared
  promotes_unshared : c.2.1 ⊆ orientedUnshared M shared
  promoted_matches : ∀ j : ↥c.2.1,
    target (tau j.val) = (x.2.2 (c.2.2 j)).1
  promoted_zero : ∀ j : ↥c.2.1,
    (x.2.2 (c.2.2 j)).2 +
      (step : ZMod (modulus (x.2.2 (c.2.2 j)).1)) = 0
  promoted_not_dividing : ∀ j : ↥c.2.1,
    ¬ modulus ((x.2.2 (c.2.2 j)).1) ∣ D
  stored_not_dividing : ∀ j ∈ c.1,
    ¬ modulus (x.1 (sigma j)) ∣ D
  output_within_cutoff :
    (physicalPendingOutput modulus M B x sigma step c).length ≤ B

/-- Actual independent target integrations under mu-tilde:
one for each pattern-unshared slot that was not filled by a
promotion from OLD memory. Not one for shared/promoted slots. -/
noncomputable def orientedBigBranchCoefficient
    (mu : P → ℝ) (V rho : ℝ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (step : ℤ) (c : BigEdgeChoice modulus M B x) : ℂ :=
  ((rho : ℂ) ^ (Green64PhysicalEdge.oldZeroCount x.2 +
    outputZeroCount modulus M B x sigma step c)) *
  ((1 : ℂ) / (V : ℂ) ^ c.2.1.card) *
  (∏ j ∈ orientedFresh M shared c.2.1,
    (mu (target (tau j)) : ℂ))

/-- At identity target permutation the corrected fresh mass is the
old physical formula. This isolates the permutation-dependent error. -/
theorem orientedFresh_eq_old_at_identity
    (shared promote : Finset (Fin M)) :
    orientedFresh M shared promote =
    freshTargetSlots M shared (Equiv.refl _) promote := by
  have hu : unsharedTarget M shared (Equiv.refl _) =
      Finset.univ \ shared := by
    ext i
    have h1 : i ∈ unsharedTarget M shared (Equiv.refl _) ↔ i ∉ shared := by
      unfold unsharedTarget
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
    have h2 : i ∈ (Finset.univ \ shared) ↔ i ∉ shared :=
      Finset.mem_sdiff.trans (and_iff_right (Finset.mem_univ i))
    exact h1.trans h2.symm
  simp only [orientedFresh, orientedUnshared, freshTargetSlots, hu]

end Green64FullPhysicalE

end

/-! ## MemoryOriginalCleanFreshTargetLaw -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The ORIGINAL oriented BIG physical legality on a CLEAN edge
contains precisely source/target shared-prime equality. All
promotion, store and OLD-capacity constraints are automatic.
No auxiliary assumptions about output independence or prime
collision events are introduced. -/
theorem memory_original_clean_big_legal_iff_shared
    (x : BigState modulus M B)
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hStore : c.1 = ∅) (hPromote : c.2.1 = ∅) :
    OrientedBigEdgeLegal modulus M B x target shared
      sigma tau D step c ↔
    (∀ j ∈ shared, x.1 (sigma j) = target (tau j)) := by
  constructor
  · intro h
    exact h.shared_copy
  · intro h
    refine {
      shared_copy := h
      stores_unshared := ?_
      promotes_unshared := ?_
      promoted_matches := ?_
      promoted_zero := ?_
      promoted_not_dividing := ?_
      stored_not_dividing := ?_
      output_within_cutoff := ?_
    }
    · simp [hStore]
    · simp [hPromote]
    · intro j
      have hj := j.property
      simp [hPromote] at hj
    · intro j
      have hj := j.property
      simp [hPromote] at hj
    · intro j
      have hj := j.property
      simp [hPromote] at hj
    · intro j hj
      simp [hStore] at hj
    · have hl := pending_output_length modulus M B
        x sigma step c
      simp [hStore, hPromote] at hl
      rw [hl]
      omega

/-- The exact original BIG branch coefficient on CLEAN edges:
target-variable factors are ONLY the independent mu-tilde draws
at the unshared positions. Repeated target prime values remain
allowed and preserve their indexed multiplicities. The true OLD
zero-count / phase-free weight is fixed by x, step and c. -/
theorem memory_original_clean_big_fresh_target_coefficient
    (mu : P → ℝ) (V rho : ℝ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hStore : c.1 = ∅) (hPromote : c.2.1 = ∅) :
    orientedBigBranchCoefficient modulus M B mu V rho x
      target shared sigma tau step c =
    ((rho : ℂ) ^
       (Green64PhysicalEdge.oldZeroCount x.2 +
        outputZeroCount modulus M B x sigma step c)) *
    (∏ j ∈ Finset.univ \ shared,
      (mu (target (tau j)) : ℂ)) := by
  unfold orientedBigBranchCoefficient orientedFresh orientedUnshared
  simp only [hPromote, Finset.card_empty, pow_zero, div_one,
    Finset.sdiff_empty, one_mul]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalCleanFreshTargetTensorSum -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- EXACT product-law normalization of ALL free target slots while
fixing the original shared target coordinates. This is not an
assumed output-independence hypothesis: it is a finite-sum identity
which will be instantiated on the literal CLEAN oriented BIG edge.
Repeated numerical prime values in distinct slots remain allowed. -/
theorem memory_original_clean_target_tensored_mass
    {I P : Type} [Fintype I] [DecidableEq I]
    [Fintype P] [DecidableEq P]
    (shared : Finset I) (source : I → P) (mu : P → ℂ) :
    (∑ target : I → P, ∏ i : I,
       if i ∈ shared then
         (if target i = source i then (1:ℂ) else 0)
       else mu (target i)) =
    (∑ p : P, mu p)^((Finset.univ \ shared).card) := by
  classical
  calc
    _ = (∏ i : I, ∑ p : P, if i ∈ shared then
           (if p = source i then (1:ℂ) else 0) else mu p) := by
      simpa only [] using (Fintype.prod_sum
        (fun (i : I) (p : P) => if i ∈ shared then
           (if p = source i then (1:ℂ) else 0) else mu p)).symm
    _ = _ := by
      have hcoord (i : I) :
          (∑ p : P, if i ∈ shared then
             (if p = source i then (1:ℂ) else 0) else mu p) =
          if i ∈ shared then 1 else ∑ p : P, mu p := by
        by_cases hi : i ∈ shared
        · simp [hi]
        · simp [hi]
      simp_rw [hcoord]
      simp [Finset.prod_ite, Finset.prod_const,
        Finset.filter_notMem_eq_sdiff]
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalCleanOrientedTargetMass -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- For the ORIGINAL independently permuted BIG source and target
slots, the fresh-label target law is EXACTLY the harmonic/tilted
product law after conditioning on the shared source prime labels.
No assumption of DISTINCT numerical prime values is made. -/
theorem memory_original_oriented_clean_target_product_total
    (x : BigState modulus M B)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (mu : P → ℂ) :
    (∑ target : Fin M → P,
      ∏ i : Fin M,
        if tau.symm i ∈ shared then
          (if target i = x.1 (sigma (tau.symm i)) then
            (1:ℂ) else 0)
        else mu (target i)) =
    (∑ p : P, mu p)^(M-shared.card) := by
  classical
  let S : Finset (Fin M) := shared.image tau
  have hMem (i : Fin M) :
      i ∈ S ↔ tau.symm i ∈ shared := by
    simp only [S,Finset.mem_image]
    constructor
    · rintro ⟨j,hj,hji⟩
      have he : tau.symm i = j := by
        rw [← hji]
        simp
      rwa [he]
    · intro hi
      exact ⟨tau.symm i, hi, Equiv.apply_symm_apply _ _⟩
  have hCard : S.card = shared.card := by
    exact Finset.card_image_iff.mpr
      (fun a ha b hb h => tau.injective h)
  have hSize : (Finset.univ \ S).card = M-shared.card := by
    simp only [Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
    rw [hCard]
  have hTarget := memory_original_clean_target_tensored_mass
    S (fun i : Fin M => x.1 (sigma (tau.symm i))) mu
  simp_rw [hMem] at hTarget
  simpa only [hSize] using hTarget
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalCleanOriginalTargetRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The EXACT oriented BIG source target measure conditional on
source x, actual shared slots, both endpoint permutations, and the
real CLEAN no-promotion/no-store choice. Both repeated numerical
primes and their distinct ordered labels are retained.
Crucially, the ONLY variable target coefficient is the fresh
product law, not an assumed output-state independent law. -/
theorem memory_original_clean_big_target_indicator_factors
    (mu : P → ℝ) (V rho : ℝ)
    (x : BigState modulus M B)
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hStore : c.1 = ∅) (hPromote : c.2.1 = ∅) :
    (if OrientedBigEdgeLegal modulus M B x target shared
        sigma tau D step c then
        orientedBigBranchCoefficient modulus M B mu V rho x
          target shared sigma tau step c
     else 0) =
    ((rho : ℂ) ^
       (Green64PhysicalEdge.oldZeroCount x.2 +
        outputZeroCount modulus M B x sigma step c)) *
      (∏ i : Fin M,
        if tau.symm i ∈ shared then
          (if target i = x.1 (sigma (tau.symm i))
            then (1:ℂ) else 0)
        else (mu (target i):ℂ)) := by
  let C : ℂ := (rho : ℂ) ^
    (Green64PhysicalEdge.oldZeroCount x.2 +
      outputZeroCount modulus M B x sigma step c)
  let g : Fin M → ℂ := fun i =>
    if tau.symm i ∈ shared then
      (if target i = x.1 (sigma (tau.symm i))
        then (1:ℂ) else 0)
    else (mu (target i):ℂ)
  have hperm : (∏ i : Fin M, g i) =
      ∏ j : Fin M, (if j ∈ shared then
        (if target (tau j) = x.1 (sigma j) then (1:ℂ) else 0)
        else (mu (target (tau j)):ℂ)) := by
    have heq := Fintype.prod_equiv tau
      (fun j : Fin M => g (tau j)) g (fun j => rfl)
    simpa only [g, Equiv.symm_apply_apply] using heq.symm
  have hsplit : (∏ i : Fin M, g i) =
      (if ∀ j ∈ shared, x.1 (sigma j) = target (tau j)
         then (1:ℂ) else 0) *
       (∏ j ∈ Finset.univ \ shared,
          (mu (target (tau j)):ℂ)) := by
    rw [hperm, Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter,
      Finset.filter_notMem_eq_sdiff, Finset.univ_inter]
    have hb : (∏ j ∈ shared,
        if target (tau j) = x.1 (sigma j) then (1:ℂ) else 0) =
        (if ∀ j ∈ shared, x.1 (sigma j) = target (tau j)
          then (1:ℂ) else 0) := by
      rw [Finset.prod_ite_zero]
      simp only [Finset.prod_const, one_pow]
      simp only [eq_comm]
    rw [hb]
  have hleg := memory_original_clean_big_legal_iff_shared
    modulus M B x target shared sigma tau D step c
    hStore hPromote
  have hcoef := memory_original_clean_big_fresh_target_coefficient
    modulus M B mu V rho x target shared sigma tau step c
    hStore hPromote
  change (if OrientedBigEdgeLegal modulus M B x target shared
    sigma tau D step c then
      orientedBigBranchCoefficient modulus M B mu V rho x
        target shared sigma tau step c
    else 0) = C * ∏ i : Fin M, g i
  rw [hsplit]
  by_cases h : ∀ j ∈ shared, x.1 (sigma j) = target (tau j)
  · rw [if_pos (hleg.mpr h), if_pos h, one_mul, hcoef]
  · rw [if_neg (fun hh => h (hleg.mp hh)), if_neg h, zero_mul,
        mul_zero]

/-- FULL actual clean BIG row summed over every target ordered tuple.
Source shared labels are held, all fresh targets integrated exactly:
the factor is the `mu` total mass to the number of original
unshared positions. No extra independence of SMALL or Fock OUTPUT
is asserted; this proves exactly its BIG fresh-target component. -/
theorem memory_original_clean_big_full_target_mass
    (mu : P → ℝ) (V rho : ℝ)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hStore : c.1 = ∅) (hPromote : c.2.1 = ∅) :
    (∑ target : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x target shared
        sigma tau D step c then
        orientedBigBranchCoefficient modulus M B mu V rho x
          target shared sigma tau step c
      else 0) =
    ((rho : ℂ) ^
      (Green64PhysicalEdge.oldZeroCount x.2 +
       outputZeroCount modulus M B x sigma step c)) *
    (∑ p : P, (mu p : ℂ))^(M-shared.card) := by
  classical
  simp_rw [memory_original_clean_big_target_indicator_factors
    modulus M B mu V rho x _ shared sigma tau D step c
    hStore hPromote]
  rw [← Finset.mul_sum]
  exact congrArg (fun a : ℂ =>
    ((rho : ℂ) ^
      (Green64PhysicalEdge.oldZeroCount x.2 +
       outputZeroCount modulus M B x sigma step c))*a)
    (memory_original_oriented_clean_target_product_total
      modulus M B x shared sigma tau (fun p => (mu p:ℂ)))
end Green64FullPhysicalE

end

end

/-! ## PhysicalActualSourceSetConservation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- SOURCE BIG shared prime values, using the sampled source
permutation rather than the old raw-index approximation. -/
noncomputable def trueBigSharedValues
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M)) : Finset P :=
  shared.image (fun i => x.1 (sigma i))

/-- Prime values returned to active lists from OLD pending indices. -/
noncomputable def trueBigPromotedValues
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x) :
    Finset P :=
  c.2.1.attach.image (fun i => (x.2.2 (c.2.2 i)).1)

/-- Prime values of all and only new target active births. -/
noncomputable def trueBigFreshValues
    (target : Fin M → P) (shared promote : Finset (Fin M))
    (tau : Equiv.Perm (Fin M)) : Finset P :=
  (orientedFresh M shared promote).image (fun i => target (tau i))

/-- Checked concrete SOURCE E_i active-set update, not a
postulated transition. Every term comes from real store/promotion/
fresh fields of the existing independently permuted physical edge. -/
theorem real_oriented_E_active_set_conservation
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (h : OrientedBigEdgeLegal modulus M B x target shared
      sigma tau D step c) :
    (Finset.univ : Finset (Fin M)).image target =
      trueBigSharedValues modulus M B x shared sigma ∪
      trueBigPromotedValues modulus M B x c ∪
      trueBigFreshValues M target shared c.2.1 tau := by
  have hslots :
      orientedFresh M shared c.2.1 =
        Finset.univ \ (shared ∪ c.2.1) := by
    ext i
    simp [orientedFresh, orientedUnshared]
  simpa only [trueBigSharedValues, trueBigPromotedValues,
      trueBigFreshValues, hslots] using
    (source_oriented_active_slot_partition
      x.1 target (fun i : Fin x.2.1.val => (x.2.2 i).1)
      sigma tau shared c.2.1 c.2.2
      h.shared_copy h.promoted_matches)

/-- The exact BIG Fock survivor support, measured by source OLD indices. -/
noncomputable def trueBigSurvivorValues
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x) :
    Finset P :=
  (survivorIndices modulus M B x c).image (fun i => (x.2.2 i).1)

/-- Exactly the source active prime labels stored into pending memory. -/
noncomputable def trueBigStoredValues
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M))
    (c : BigEdgeChoice modulus M B x) : Finset P :=
  c.1.image (fun i => x.1 (sigma i))

/-- The OLD survivor and newly stored supports are the only primes
in the actual physical E output Fock memory; no fresh active birth
or same-edge newly stored promotion is counted in this support. -/
theorem real_oriented_E_pending_set_conservation
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M))
    (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    ((physicalPendingOutput modulus M B x sigma step c).map
       (fun z => z.1)).toFinset =
      trueBigSurvivorValues modulus M B x c ∪
      trueBigStoredValues modulus M B x sigma c := by
  classical
  ext v
  simp [trueBigSurvivorValues, trueBigStoredValues,
    physicalPendingOutput, survivors, newlyStored,
    Green64PhysicalEdge.translateAtom, List.mem_map,
    Finset.mem_image, Finset.mem_toList, List.mem_append]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEdgeCoverage -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- ALL pattern-unshared target slots are partitioned by
OLD promotions and independent mu-tilde fresh integrations.
This statement concerns the CORRECTED oriented slot set. -/
theorem oriented_target_coverage
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (h : OrientedBigEdgeLegal modulus M B x target
      shared sigma tau D step c) :
    orientedFresh M shared c.2.1 ∪ c.2.1 =
      orientedUnshared M shared := by
  exact Finset.sdiff_union_of_subset h.promotes_unshared

/-- Newly sampled oriented slots are disjoint from OLD target
promotion slots, so a promotion is never charged a fresh birth. -/
theorem oriented_fresh_disjoint_promotions
    (shared promote : Finset (Fin M)) :
    Disjoint (orientedFresh M shared promote) promote :=
  Finset.sdiff_disjoint

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTargetNodup -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- A genuinely legal original BIG E witness cannot merge two
distinct previously born primes into one target active list.
Given input active/OLD uniqueness and fresh births disjoint from
both pre-existing pools, EVERY target slot remains distinct.
The distinction between OLD promotion and fresh birth is essential. -/
theorem oriented_legal_target_injective
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hleg : OrientedBigEdgeLegal modulus M B
      x target shared sigma tau D step c)
    (hSrc : Function.Injective x.1)
    (hOld : Function.Injective
      (fun r : Fin x.2.1.val => (x.2.2 r).1))
    (hSep : ∀ (j : Fin M) (r : Fin x.2.1.val),
      x.1 j ≠ (x.2.2 r).1)
    (hFreshInj : ∀ j ∈ orientedFresh M shared c.2.1,
        ∀ l ∈ orientedFresh M shared c.2.1,
        target (tau j) = target (tau l) → j = l)
    (hFreshOldActive : ∀ j ∈ orientedFresh M shared c.2.1,
        ∀ t : Fin M, target (tau j) ≠ x.1 t)
    (hFreshOldPending : ∀ j ∈ orientedFresh M shared c.2.1,
        ∀ r : Fin x.2.1.val,
          target (tau j) ≠ (x.2.2 r).1) :
    Function.Injective target := by
  have hpDisj (j : Fin M) (hj : j ∈ c.2.1) : j ∉ shared := by
    have hs := hleg.promotes_unshared hj
    simpa [orientedUnshared] using hs
  have hFresh (j : Fin M) (hj : j ∉ shared)
      (hp : j ∉ c.2.1) :
      j ∈ orientedFresh M shared c.2.1 := by
    simp [orientedFresh, orientedUnshared, hj, hp]
  have hsval (j : Fin M) (hj : j ∈ shared) :
      target (tau j) = x.1 (sigma j) :=
    (hleg.shared_copy j hj).symm
  have hpval (j : Fin M) (hj : j ∈ c.2.1) :
      target (tau j) = (x.2.2 (c.2.2 ⟨j,hj⟩)).1 :=
    hleg.promoted_matches ⟨j,hj⟩
  have hinj : Function.Injective (fun j : Fin M => target (tau j)) := by
    intro j l heq
    by_cases hjS : j ∈ shared
    · by_cases hlS : l ∈ shared
      · apply sigma.injective
        apply hSrc
        exact (hsval j hjS).symm.trans
          (heq.trans (hsval l hlS))
      · by_cases hlP : l ∈ c.2.1
        · have he : x.1 (sigma j) =
              (x.2.2 (c.2.2 ⟨l,hlP⟩)).1 :=
            (hsval j hjS).symm.trans (heq.trans (hpval l hlP))
          exact False.elim ((hSep (sigma j) (c.2.2 ⟨l,hlP⟩)) he)
        · have hfl := hFresh l hlS hlP
          have he : target (tau l) = x.1 (sigma j) :=
            heq.symm.trans (hsval j hjS)
          exact False.elim ((hFreshOldActive l hfl (sigma j)) he)
    · by_cases hjP : j ∈ c.2.1
      · by_cases hlS : l ∈ shared
        · have he : x.1 (sigma l) =
              (x.2.2 (c.2.2 ⟨j,hjP⟩)).1 :=
            (hsval l hlS).symm.trans
              (heq.symm.trans (hpval j hjP))
          exact False.elim ((hSep (sigma l) (c.2.2 ⟨j,hjP⟩)) he)
        · by_cases hlP : l ∈ c.2.1
          · have hIdx : c.2.2 ⟨j,hjP⟩ = c.2.2 ⟨l,hlP⟩ := by
              apply hOld
              exact (hpval j hjP).symm.trans (heq.trans (hpval l hlP))
            have hSub : (⟨j,hjP⟩ : ↥c.2.1) = ⟨l,hlP⟩ :=
              c.2.2.injective hIdx
            exact congrArg Subtype.val hSub
          · have hfl := hFresh l hlS hlP
            have he : target (tau l) =
                (x.2.2 (c.2.2 ⟨j,hjP⟩)).1 :=
              heq.symm.trans (hpval j hjP)
            exact False.elim ((hFreshOldPending l hfl
              (c.2.2 ⟨j,hjP⟩)) he)
      · have hfj := hFresh j hjS hjP
        by_cases hlS : l ∈ shared
        · have he : target (tau j) = x.1 (sigma l) :=
            heq.trans (hsval l hlS)
          exact False.elim ((hFreshOldActive j hfj (sigma l)) he)
        · by_cases hlP : l ∈ c.2.1
          · have he : target (tau j) =
                (x.2.2 (c.2.2 ⟨l,hlP⟩)).1 :=
              heq.trans (hpval l hlP)
            exact False.elim ((hFreshOldPending j hfj
              (c.2.2 ⟨l,hlP⟩)) he)
          · exact hFreshInj j hfj l (hFresh l hlS hlP) heq
  intro j l hval
  have he : target (tau (tau.symm j)) =
      target (tau (tau.symm l)) := by simpa using hval
  have h := hinj he
  simpa using congrArg tau h

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedPendingNodup -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The ORIGINAL physical E operation preserves PRIME uniqueness
inside pending Fock memory when its input active and OLD particles
are unique and disjoint. No false deduplication of repeated atoms
is inserted into the operator; this is an invariant of legal
distinct-birth paths, not of the ambient Fock Hilbert space. -/
theorem oriented_E_pending_prime_nodup
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hSrc : Function.Injective x.1)
    (hOld : Function.Injective
      (fun i : Fin x.2.1.val => (x.2.2 i).1))
    (hSep : ∀ (i : Fin M) (r : Fin x.2.1.val),
      x.1 i ≠ (x.2.2 r).1) :
    ((physicalPendingOutput modulus M B x sigma step c).map
      (fun z => z.1)).Nodup := by
  classical
  let S := survivorIndices modulus M B x c
  let A := c.1
  have hSrcSigma : Function.Injective
      (fun i : Fin M => x.1 (sigma i)) := by
    intro i j h
    exact sigma.injective (hSrc h)
  have hKeep : (S.toList.map
      (fun i : Fin x.2.1.val => (x.2.2 i).1)).Nodup := by
    exact (Finset.nodup_toList S).map hOld
  have hStore : (A.toList.map
      (fun i : Fin M => x.1 (sigma i))).Nodup := by
    exact (Finset.nodup_toList A).map hSrcSigma
  have hSepLists :
      ∀ u ∈ S.toList.map
        (fun i : Fin x.2.1.val => (x.2.2 i).1),
      ∀ v ∈ A.toList.map
        (fun i : Fin M => x.1 (sigma i)),
      u ≠ v := by
    intro u hu v hv hEq
    rcases List.mem_map.mp hu with ⟨i,hi,rfl⟩
    rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
    exact (hSep (sigma j) i) hEq.symm
  have hFull :
      ((S.toList.map (fun i : Fin x.2.1.val => (x.2.2 i).1)) ++
        (A.toList.map (fun i : Fin M => x.1 (sigma i)))).Nodup :=
    (List.nodup_append).mpr ⟨hKeep, hStore, hSepLists⟩
  simpa [physicalPendingOutput, survivors, newlyStored,
    S, A, List.map_append, List.map_map, Function.comp_def,
    Green64PhysicalEdge.translateAtom] using hFull

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedOutputDisjoint -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Every output pending prime in the original E branch is either
an OLD nonpromoted survivor or a stored source active prime.
Crucially a newly stored particle is NOT eligible as an OLD
promotion on the same edge. -/
theorem physical_E_pending_prime_mem_iff
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) (v : P) :
    v ∈ (physicalPendingOutput modulus M B x sigma step c).map
      (fun z => z.1) ↔
    (∃ i ∈ survivorIndices modulus M B x c, v = (x.2.2 i).1) ∨
      (∃ j ∈ c.1, v = x.1 (sigma j)) := by
  simp [physicalPendingOutput, survivors, newlyStored,
    List.mem_map, List.mem_append, Finset.mem_toList,
    Green64PhysicalEdge.translateAtom, eq_comm,
    or_left_comm, or_comm, or_assoc]
/-- An input with one physical copy of each previously born prime
cannot have the same prime ACTIVE and PENDING after a legal
oriented E transfer, provided the new E births avoid the input.
This is a concrete source-history conservation rule. -/
theorem oriented_E_target_pending_disjoint
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hleg : OrientedBigEdgeLegal modulus M B
      x target shared sigma tau D step c)
    (hSrc : Function.Injective x.1)
    (hOld : Function.Injective
      (fun i : Fin x.2.1.val => (x.2.2 i).1))
    (hSep : ∀ (i : Fin M) (r : Fin x.2.1.val),
      x.1 i ≠ (x.2.2 r).1)
    (hFreshActive : ∀ j ∈ orientedFresh M shared c.2.1,
      ∀ i : Fin M, target (tau j) ≠ x.1 i)
    (hFreshOld : ∀ j ∈ orientedFresh M shared c.2.1,
      ∀ r : Fin x.2.1.val,
        target (tau j) ≠ (x.2.2 r).1) :
    ∀ (i : Fin M) (v : P),
      v ∈ (physicalPendingOutput modulus M B x sigma step c).map
        (fun z => z.1) → target i ≠ v := by
  have hStoreNotShared (j : Fin M) (hj : j ∈ c.1) :
      j ∉ shared := by
    have hs := hleg.stores_unshared hj
    simpa [orientedUnshared] using hs
  have hPromoNotShared (j : Fin M) (hj : j ∈ c.2.1) :
      j ∉ shared := by
    have hs := hleg.promotes_unshared hj
    simpa [orientedUnshared] using hs
  have hFresh (j : Fin M) (hjs : j ∉ shared)
      (hjp : j ∉ c.2.1) :
      j ∈ orientedFresh M shared c.2.1 := by
    simp [orientedFresh, orientedUnshared, hjs, hjp]
  have hsval (j : Fin M) (hj : j ∈ shared) :
      target (tau j) = x.1 (sigma j) :=
    (hleg.shared_copy j hj).symm
  have hpval (j : Fin M) (hj : j ∈ c.2.1) :
      target (tau j) = (x.2.2 (c.2.2 ⟨j,hj⟩)).1 :=
    hleg.promoted_matches ⟨j,hj⟩
  intro i v hv
  have hv' := (physical_E_pending_prime_mem_iff
    modulus M B x sigma step c v).mp hv
  let j : Fin M := tau.symm i
  have hitarget : target i = target (tau j) := by
    simp [j]
  by_cases hjS : j ∈ shared
  · rcases hv' with ⟨r,hr,hrv⟩ | ⟨s,hs,hsv⟩
    · intro heq
      have he : x.1 (sigma j) = (x.2.2 r).1 :=
        (hsval j hjS).symm.trans
          (hitarget.symm.trans (heq.trans hrv))
      exact (hSep (sigma j) r) he
    · intro heq
      have he : x.1 (sigma j) = x.1 (sigma s) :=
        (hsval j hjS).symm.trans
          (hitarget.symm.trans (heq.trans hsv))
      have jEq : j = s := sigma.injective (hSrc he)
      exact (hStoreNotShared s hs) (jEq ▸ hjS)
  · by_cases hjP : j ∈ c.2.1
    · rcases hv' with ⟨r,hr,hrv⟩ | ⟨s,hs,hsv⟩
      · intro heq
        have hIdx : c.2.2 ⟨j,hjP⟩ = r := by
          apply hOld
          exact (hpval j hjP).symm.trans
            (hitarget.symm.trans (heq.trans hrv))
        have hSelected : r ∈ selectedOld modulus M B x c := by
          rw [← hIdx]
          exact Finset.mem_image.mpr
            ⟨⟨j,hjP⟩, Finset.mem_univ _, rfl⟩
        exact (Finset.mem_sdiff.mp hr).2 hSelected
      · intro heq
        have he : x.1 (sigma s) = (x.2.2 (c.2.2 ⟨j,hjP⟩)).1 :=
          hsv.symm.trans (heq.symm.trans
            (hitarget.trans (hpval j hjP)))
        exact (hSep (sigma s) (c.2.2 ⟨j,hjP⟩)) he
    · have hf := hFresh j hjS hjP
      rcases hv' with ⟨r,hr,hrv⟩ | ⟨s,hs,hsv⟩
      · intro heq
        have he : target (tau j) = (x.2.2 r).1 :=
          hitarget.symm.trans (heq.trans hrv)
        exact (hFreshOld j hf r) he
      · intro heq
        have he : target (tau j) = x.1 (sigma s) :=
          hitarget.symm.trans (heq.trans hsv)
        exact (hFreshActive j hf (sigma s)) he

end Green64FullPhysicalE

end

/-! ## PhysicalSourceESurvivorDifference -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- At the original physical E edge, SELECTED old indices map to
exactly the OLD prime values promoted into target slots. This
preserves indexed-multiplicity semantics prior to symmetrization. -/
theorem selectedOld_values_eq_promoted
    (x : BigState modulus M B)
    (c : BigEdgeChoice modulus M B x) :
    (selectedOld modulus M B x c).image
      (fun i => (x.2.2 i).1) =
      trueBigPromotedValues modulus M B x c := by
  classical
  ext v
  simp [selectedOld, trueBigPromotedValues, Finset.mem_image]

/-- Source E survivor prime SET is OLD memory minus promoted values,
provided every incoming pending numerical prime occurs once.
This uses the actual OLD-index injection, not a guessed Markov law. -/
theorem physical_E_survivors_equal_set_difference
    (x : BigState modulus M B)
    (c : BigEdgeChoice modulus M B x)
    (hOld : Function.Injective
      (fun i : Fin x.2.1.val => (x.2.2 i).1)) :
    trueBigSurvivorValues modulus M B x c =
      ((Finset.univ : Finset (Fin x.2.1.val)).image
        (fun i => (x.2.2 i).1)) \
      trueBigPromotedValues modulus M B x c := by
  unfold trueBigSurvivorValues survivorIndices
  rw [Finset.image_sdiff Finset.univ
    (selectedOld modulus M B x c) hOld]
  rw [selectedOld_values_eq_promoted]

end Green64FullPhysicalE

end

/-! ## GroupAveragedSmallHilbert -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)]
variable [∀ g, DecidableEq (P g)]
variable (modulus : (g : G) → P g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]
variable (M : ℕ)

/-- The true FINITE small-state physical E operator in all small groups,
averaged independently over every source AND target active-list
permutation, with the original source physical pattern normalization. -/
noncomputable def groupAveragedSmallEdgeAct
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M →
      GroupPermFamily (G := G) M → ℂ)
    (F : GroupState P modulus M → ℂ)
    (x : GroupState P modulus M) : ℂ :=
  ∑ z : GroupState P modulus M,
    groupAveragedSmallKernel P modulus M q V shared step K x z *
      F z

/-- FULL finite physical small-Haar Hilbert adjoint with the true
product source/target endpoint permutation symmetrization.
The forward kernel K may vary arbitrarily with the TWO families
of sampled permutations; reversal uses conjugate transpose.
No spurious cross-group factorial or 1/p residue weight occurs. -/
theorem groupAveragedSmallEdgeAct_adjoint
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M →
      GroupPermFamily (G := G) M → ℂ)
    (F H : GroupState P modulus M → ℂ) :
    groupSmallInner P modulus M V F
      (groupAveragedSmallEdgeAct P modulus M q V shared step K H) =
    groupSmallInner P modulus M V
      (groupAveragedSmallEdgeAct P modulus M q V shared (-step)
        (reverseGroupPermutationKernel (G := G) M K) F) H := by
  let W : ℂ := (groupStateMass P modulus M V : ℂ)
  let A : GroupState P modulus M → GroupState P modulus M → ℂ :=
    groupAveragedSmallKernel P modulus M q V shared step K
  let B : GroupState P modulus M → GroupState P modulus M → ℂ :=
    groupAveragedSmallKernel P modulus M q V shared (-step)
      (reverseGroupPermutationKernel (G := G) M K)
  have hpair (x z : GroupState P modulus M) :
      W * star (F x) * (A x z * H z) =
      W * star (B z x * F x) * H z := by
    have hker := groupAveragedSmallKernel_reverse P modulus M
      q V shared step K x z
    change A x z = star (B z x) at hker
    rw [hker,star_mul]
    ring
  have hleft :
      groupSmallInner P modulus M V F
        (groupAveragedSmallEdgeAct P modulus M q V shared step K H) =
        ∑ x : GroupState P modulus M,
          ∑ z : GroupState P modulus M,
            W * star (F x) * (A x z * H z) := by
    unfold groupSmallInner groupAveragedSmallEdgeAct
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  have hright :
      groupSmallInner P modulus M V
        (groupAveragedSmallEdgeAct P modulus M q V shared (-step)
          (reverseGroupPermutationKernel (G := G) M K) F) H =
        ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (B z x * F x) * H z := by
    unfold groupSmallInner groupAveragedSmallEdgeAct
    apply Finset.sum_congr rfl
    intro z hz
    rw [star_sum]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
  calc
    groupSmallInner P modulus M V F
      (groupAveragedSmallEdgeAct P modulus M q V shared step K H) =
        ∑ x : GroupState P modulus M,
          ∑ z : GroupState P modulus M,
            W * star (F x) * (A x z * H z) := hleft
    _ = ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (F x) * (A x z * H z) :=
          Finset.sum_comm
    _ = ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (B z x * F x) * H z := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair x z
    _ = groupSmallInner P modulus M V
        (groupAveragedSmallEdgeAct P modulus M q V shared (-step)
          (reverseGroupPermutationKernel (G := G) M K) F) H :=
          hright.symm

/-- With ZERO small groups the independent source/target symmetrization
has unit mass, not an extra factorial from a nonexistent small group. -/
theorem groupPermutationPairMass_noGroups
    (hG : IsEmpty G) :
    groupPermutationPairMass (G := G) M = 1 := by
  classical
  letI : IsEmpty G := hG
  simp [groupPermutationPairMass]

end Green64SmallHaar

end

/-! ## PhysicalFullHaarFockEdge -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Actual finite source SMALL physical Haar × BIG ACTIVE L2 ×
BIG 1/j_g! symmetric-sector REPRESENTATIVES, including zero sector. -/
abbrev FullPhysicalState :=
  Green64SmallHaar.GroupState SP smallMod M ×
    BigGroupState BP bigMod M cap

/-- Physical output uses truly symmetric pending multisets, NOT
sets of distinct numerical primes or artificially chosen finite proxy. -/
abbrev FullPhysicalOutput :=
  Green64SmallHaar.GroupState SP smallMod M ×
    BigGroupTarget BP bigMod M

noncomputable def fullPhysicalMass
    (Vsmall : SG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap) : ℝ :=
  Green64SmallHaar.groupStateMass SP smallMod M Vsmall *
    bigGroupStateMass BP bigMod M cap muBig x.2

/-- The original source symmetrizes independently in EACH big group:
the total BIG pair factor is product_g (M!)^-2, not (M!^#groups)^-1.
The separate small-group permutation average is contained in
groupAveragedSmallKernel and MUST NOT be duplicated here. -/
noncomputable def bigEndpointPairMass : ℝ :=
  ∏ g : BG, Green64SmallHaar.permutationPairMass M

theorem bigEndpointPairMass_normalized :
    (bigEndpointPairMass (BG := BG) M : ℂ) *
      ((Fintype.card (BigGroupPerm (BG := BG) M) : ℂ) ^ 2) = 1 := by
  simpa [bigEndpointPairMass,Green64SmallHaar.groupPermutationPairMass,
    BigGroupPerm,Green64SmallHaar.GroupPermFamily] using
      (Green64SmallHaar.groupPermutationPairMass_normalized (G := BG) M)

/-- An ACTUAL finite source E_i branch contains one independently
sampled source/target active-list permutation in EACH big group,
all independent BIG store/OLD promotion/fresh choices, and one
genuine small physical target residue+ordered-mark state. -/
structure FullPhysicalEdgeBranch
    (x : FullPhysicalState SP smallMod BP bigMod M cap) where
  sigmaBig : BigGroupPerm (BG := BG) M
  tauBig : BigGroupPerm (BG := BG) M
  bigChoice : BigGroupBranch BP bigMod M cap x.2
  smallTarget : Green64SmallHaar.GroupState SP smallMod M

noncomputable instance
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :
    Fintype (FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x) := by
  let e :
      FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x ≃
        (BigGroupPerm (BG := BG) M) ×
        (BigGroupPerm (BG := BG) M) ×
        (BigGroupBranch BP bigMod M cap x.2) ×
        Green64SmallHaar.GroupState SP smallMod M :=
    { toFun := fun b => (b.sigmaBig,b.tauBig,b.bigChoice,b.smallTarget)
      invFun := fun b => ⟨b.1,b.2.1,b.2.2.1,b.2.2.2⟩
      left_inv := by intro b; cases b; rfl
      right_inv := by intro b; cases b with | mk a b => cases b with
        | mk c d => cases d; rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Full fixed-D source BIG E_i branch legality in every group.
The actual source SMALL validity is encoded by its already-checked
physical Haar kernel (zero when residues/marks are incompatible). -/
def FullPhysicalEdgeLegal
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ)
    (b : FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x) : Prop :=
  BigGroupEdgeLegal BP bigMod M cap x.2 sharedBig
    b.sigmaBig b.tauBig D step b.bigChoice

noncomputable def legalFullPhysicalBranches
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ) :
    Finset (FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x) :=
  Finset.univ.filter
    (FullPhysicalEdgeLegal SP smallMod BP bigMod M cap x sharedBig D step)

/-- The source one global complex multiplier may depend on BIG and
SMALL endpoint permutations and sampled big physical branch labels.
Full source K_nu D^(iζ) and Fourier phase must be instantiated
rather than postulated as a new physical theorem. -/
abbrev GlobalSourceK
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :=
  (BigGroupPerm (BG := BG) M) →
  (BigGroupPerm (BG := BG) M) →
  (BigGroupBranch BP bigMod M cap x.2) →
  (Green64SmallHaar.GroupPermFamily (G := SG) M) →
  (Green64SmallHaar.GroupPermFamily (G := SG) M) → ℂ

/-- Exactly ONE original source complex K is included INSIDE the
real all-small-group Haar endpoint-permutation sum; all-big
source branch coefficients are products of original rho,V,mu
with NO duplicate K, Fock j!, or zero-residue 1/p. -/
noncomputable def fullPhysicalBranchCoefficient
    (q rho : ℝ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (sharedBig : (g : BG) → Finset (Fin M))
    (step : ℤ)
    (K : GlobalSourceK SP smallMod BP bigMod M cap x)
    (b : FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x) : ℂ :=
  (bigEndpointPairMass (BG := BG) M : ℂ) *
    bigGroupBranchWeight BP bigMod M cap muBig Vbig rho
      x.2 sharedBig b.sigmaBig b.tauBig step b.bigChoice *
    Green64SmallHaar.groupAveragedSmallKernel
      SP smallMod M q Vsmall sharedSmall step
      (fun ss tt => K b.sigmaBig b.tauBig b.bigChoice ss tt)
      x.1 b.smallTarget

noncomputable def fullPhysicalBranchOutput
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (step : ℤ)
    (b : FullPhysicalEdgeBranch SP smallMod BP bigMod M cap x) :
    FullPhysicalOutput SP smallMod BP bigMod M :=
  (b.smallTarget,
    bigGroupBranchOutput BP bigMod M cap x.2 b.sigmaBig step b.bigChoice)

/-- This is the genuine FINITE fixed-pattern/free D source physical
E_i operator row, including all independent BIG endpoint
permutations, target ACTIVE µ integrations, OLD-index injections,
big Fock residue transitions, actual SMALL Haar+ordered marks,
small source/target permutations and ONE global complex K.
It is not the unrestricted full E_i until D/pattern/free sampling
and symmetric Hilbert extension have been proved. -/
noncomputable def fullPhysicalFixedD_E
    (q rho : ℝ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ)
    (K : GlobalSourceK SP smallMod BP bigMod M cap x)
    (F : FullPhysicalOutput SP smallMod BP bigMod M → ℂ) : ℂ :=
  ∑ b ∈ legalFullPhysicalBranches SP smallMod BP bigMod M cap
      x sharedBig D step,
    fullPhysicalBranchCoefficient SP smallMod BP bigMod M cap
      q rho Vsmall Vbig muBig x sharedSmall sharedBig step K b *
      F (fullPhysicalBranchOutput SP smallMod BP bigMod M cap x step b)

end Green64FullPhysicalE

end

/-! ## PhysicalFullEdgeKernel -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- All and ONLY output small torus/ordered-mark states and
big ACTIVE × symmetric Fock memory states reached by the
original fixed-(pattern,D,step) physical E_i choice enumeration. -/
noncomputable def fullEdgeOutputSupport
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ) :
    Finset (FullPhysicalOutput SP smallMod BP bigMod M) :=
  (legalFullPhysicalBranches SP smallMod BP bigMod M cap
    x sharedBig D step).image
    (fullPhysicalBranchOutput SP smallMod BP bigMod M cap x step)

/-- Exact physical source edge state-to-state kernel: *all* independent
big source/target permutation families, store/promotion OLD injections,
target fresh prime draws, real small Haar target states, its own small
source/target permutation families, with a single coupled complex K.
No branching multiplicity is collapsed when output states coincide. -/
noncomputable def fullEdgeStateKernel
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ)
    (K : GlobalSourceK SP smallMod BP bigMod M cap x)
    (out : FullPhysicalOutput SP smallMod BP bigMod M) : ℂ := by
  classical
  letI : DecidableEq (FullPhysicalOutput SP smallMod BP bigMod M) := Classical.decEq _
  exact ∑ b ∈ legalFullPhysicalBranches SP smallMod BP bigMod M cap
      x sharedBig D step,
    if fullPhysicalBranchOutput SP smallMod BP bigMod M cap x step b = out then
      fullPhysicalBranchCoefficient SP smallMod BP bigMod M cap
        q rho Vsmall Vbig muBig x sharedSmall sharedBig step K b
    else 0

/-- At a fixed source pattern/free D and common Δ, the whole
physical multi-group E_i operator with true active L2, Fock 1/j!,
Haar torus, independently sampled endpoint permutations and
ordered Old promotions is exactly the kernel over physical output
states. This is the genuine physical suboperator, NOT an abstract
postulated transition law. Missing next: sample prescribed source
patterns/free D and lift to unrestricted symmetric Hilbert root moment. -/
theorem fullPhysicalFixedD_E_kernel_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (sharedBig : (g : BG) → Finset (Fin M))
    (D : ℕ) (step : ℤ)
    (K : GlobalSourceK SP smallMod BP bigMod M cap x)
    (F : FullPhysicalOutput SP smallMod BP bigMod M → ℂ) :
    fullPhysicalFixedD_E SP smallMod BP bigMod M cap
      q rho Vsmall Vbig muBig x sharedSmall sharedBig D step K F =
    ∑ out ∈ fullEdgeOutputSupport SP smallMod BP bigMod M cap
      x sharedBig D step,
      fullEdgeStateKernel SP smallMod BP bigMod M cap
        q rho Vsmall Vbig muBig x sharedSmall sharedBig D step K out * F out := by
  unfold fullPhysicalFixedD_E fullEdgeOutputSupport fullEdgeStateKernel
  classical
  simpa only using (sum_over_exact_output_fibres
    (legalFullPhysicalBranches SP smallMod BP bigMod M cap
      x sharedBig D step)
    (fullPhysicalBranchOutput SP smallMod BP bigMod M cap x step)
    (fullPhysicalBranchCoefficient SP smallMod BP bigMod M cap
      q rho Vsmall Vbig muBig x sharedSmall sharedBig step K) F)

end Green64FullPhysicalE

end

/-! ## PhysicalFullJointReversal -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ)

/-- The ACTUAL physical small joint Haar kernel sampled at one pair
of independent small endpoint permutation families; multiplied by
one global complex source coefficient K. -/
noncomputable def smallJointSample
    (q : ℝ) (Vsmall : SG → ℝ)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (step : ℤ)
    (K : Green64SmallHaar.GroupPermFamily (G := SG) M →
         Green64SmallHaar.GroupPermFamily (G := SG) M → ℂ)
    (sigmaSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (sourceSmall targetSmall : Green64SmallHaar.GroupState SP smallMod M) : ℂ :=
  (Green64SmallHaar.groupStateMass SP smallMod M Vsmall : ℂ) *
  Green64SmallHaar.groupPermutedKernel SP smallMod M q Vsmall
    sharedSmall step K sigmaSmall tauSmall sourceSmall targetSmall

/-- Reversal has the ACTUAL small Haar q,V normalization,
reverses Delta and swaps the two independent endpoint
permutation families; the ONE complex K is conjugated. -/
theorem smallJointSample_reverse
    (q : ℝ) (Vsmall : SG → ℝ)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (step : ℤ)
    (K : Green64SmallHaar.GroupPermFamily (G := SG) M →
         Green64SmallHaar.GroupPermFamily (G := SG) M → ℂ)
    (sigmaSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (sourceSmall targetSmall : Green64SmallHaar.GroupState SP smallMod M) :
    smallJointSample SP smallMod M q Vsmall sharedSmall step K
      sigmaSmall tauSmall sourceSmall targetSmall =
    star (smallJointSample SP smallMod M q Vsmall sharedSmall (-step)
      (Green64SmallHaar.reverseGroupPermutationKernel (G := SG) M K)
      tauSmall sigmaSmall targetSmall sourceSmall) := by
  unfold smallJointSample
  rw [star_mul,Green64SmallHaar.groupPermutedKernel_reverse]
  rw [Complex.star_def,Complex.conj_ofReal]
  ring

/-- Big ACTIVE L2×Fock joint weight times the genuine small Haar
kernel, with ONE coupled source complex K. The big input/output
active labels, OLD particles, store/promote and fresh measures
are all physical source objects, not generic abstract rows. -/
noncomputable def fullPhysicalForwardJointSample
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (step : ℤ)
    (survivors : GroupJointSurvivors BP bigMod)
    (sourceBig targetBig : GroupActiveSlots BP M)
    (sharedBig stores promote : GroupIndexSets (BG := BG) M)
    (sigmaBig tauBig : BigGroupPerm (BG := BG) M)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (K : Green64SmallHaar.GroupPermFamily (G := SG) M →
         Green64SmallHaar.GroupPermFamily (G := SG) M → ℂ)
    (sigmaSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (sourceSmall targetSmall : Green64SmallHaar.GroupState SP smallMod M) : ℂ :=
  (fullBigJointForward BP bigMod M muBig Vbig rho step survivors
     sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
  smallJointSample SP smallMod M q Vsmall sharedSmall step K
    sigmaSmall tauSmall sourceSmall targetSmall

/-- Source reverse joint with all BIG stores/promotions swapped in
the physical joint variables and all SMALL permutations reversed. -/
noncomputable def fullPhysicalReverseJointSample
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (step : ℤ)
    (survivors : GroupJointSurvivors BP bigMod)
    (sourceBig targetBig : GroupActiveSlots BP M)
    (sharedBig stores promote : GroupIndexSets (BG := BG) M)
    (sigmaBig tauBig : BigGroupPerm (BG := BG) M)
    (sharedSmall : (g : SG) → Finset (Fin M))
    (K : Green64SmallHaar.GroupPermFamily (G := SG) M →
         Green64SmallHaar.GroupPermFamily (G := SG) M → ℂ)
    (sigmaSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (sourceSmall targetSmall : Green64SmallHaar.GroupState SP smallMod M) : ℂ :=
  (fullBigJointReverse BP bigMod M muBig Vbig rho step survivors
     sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
  star (smallJointSample SP smallMod M q Vsmall sharedSmall (-step)
    (Green64SmallHaar.reverseGroupPermutationKernel (G := SG) M K)
    tauSmall sigmaSmall targetSmall sourceSmall)

/-- EXACT source physical big-active/Fock/small-Haar joint detailed
balance: for every fixed sampled source D/pattern and full pair of
endpoint permutation families,
forward_joint * prod_big V_g^a = reverse_joint * prod_big V_g^b.
This retains the true SMALL q/V Haar and BIG mu^M × λ^j/j!,
rho and repeated atoms with K charged once. A bijection of ALL
physical branch choices still must be proved to conclude global E_i
adjoint and the Exact Memory Identity. -/
theorem fullPhysicalJointSample_V_reversal
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, Vbig g ≠ 0)
    (step : ℤ)
    (survivors : GroupJointSurvivors BP bigMod)
    (sourceBig targetBig : GroupActiveSlots BP M)
    (sharedBig stores promote : GroupIndexSets (BG := BG) M)
    (sigmaBig tauBig : BigGroupPerm (BG := BG) M)
    (hshared : ∀ g j, j ∈ sharedBig g → sourceBig g j = targetBig g j)
    (hs : ∀ g, stores g ⊆ unsharedSource M (sharedBig g) (sigmaBig g))
    (hp : ∀ g, promote g ⊆ unsharedTarget M (sharedBig g) (tauBig g))
    (sharedSmall : (g : SG) → Finset (Fin M))
    (K : Green64SmallHaar.GroupPermFamily (G := SG) M →
         Green64SmallHaar.GroupPermFamily (G := SG) M → ℂ)
    (sigmaSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (sourceSmall targetSmall : Green64SmallHaar.GroupState SP smallMod M) :
    fullPhysicalForwardJointSample SP smallMod BP bigMod M
      q rho Vsmall Vbig muBig step survivors sourceBig targetBig
      sharedBig stores promote sigmaBig tauBig sharedSmall K
      sigmaSmall tauSmall sourceSmall targetSmall *
      ((∏ g : BG, Vbig g ^ (promote g).card : ℝ) : ℂ) =
    fullPhysicalReverseJointSample SP smallMod BP bigMod M
      q rho Vsmall Vbig muBig step survivors sourceBig targetBig
      sharedBig stores promote sigmaBig tauBig sharedSmall K
      sigmaSmall tauSmall sourceSmall targetSmall *
      ((∏ g : BG, Vbig g ^ (stores g).card : ℝ) : ℂ) := by

  have hb := fullBigJoint_exact_reversal BP bigMod M
    muBig Vbig hV rho step survivors sourceBig targetBig
    sharedBig stores promote sigmaBig tauBig hshared hs hp
  have hbc :
      (fullBigJointForward BP bigMod M muBig Vbig rho step survivors
        sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
        ((∏ g : BG, Vbig g ^ (promote g).card : ℝ) : ℂ) =
      (fullBigJointReverse BP bigMod M muBig Vbig rho step survivors
        sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
        ((∏ g : BG, Vbig g ^ (stores g).card : ℝ) : ℂ) := by
    exact_mod_cast hb
  unfold fullPhysicalForwardJointSample fullPhysicalReverseJointSample
  rw [smallJointSample_reverse]
  calc
    _ = ((fullBigJointForward BP bigMod M muBig Vbig rho step survivors
        sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
       ((∏ g : BG, Vbig g ^ (promote g).card : ℝ) : ℂ)) *
       star (smallJointSample SP smallMod M q Vsmall sharedSmall (-step)
        (Green64SmallHaar.reverseGroupPermutationKernel (G := SG) M K)
        tauSmall sigmaSmall targetSmall sourceSmall) := by ring
    _ = ((fullBigJointReverse BP bigMod M muBig Vbig rho step survivors
        sourceBig targetBig sharedBig stores promote sigmaBig tauBig : ℂ) *
       ((∏ g : BG, Vbig g ^ (stores g).card : ℝ) : ℂ)) *
       star (smallJointSample SP smallMod M q Vsmall sharedSmall (-step)
        (Green64SmallHaar.reverseGroupPermutationKernel (G := SG) M K)
        tauSmall sigmaSmall targetSmall sourceSmall) := by rw [hbc]
    _ = _ := by ring

end Green64FullPhysicalE

end

/-! ## SourceActualArcRatio -/

section

namespace Green64Analytic.CorrelationSquare

/-- Exact physical source ratio: H=H'/L^Carc and Y=Z*H'. -/
theorem source_actual_arc_ratio_identity434
    (L Hprime Z Y Carc : ℝ) (hL : 0 < L) (hH : 0 < Hprime)
    (hZ : 0 < Z) (hY : Y = Z*Hprime) :
    (Hprime/L^Carc)/Y = 1/(Z*L^Carc) := by
  rw [hY]
  have hLp : L^Carc ≠ 0 := (Real.rpow_pos_of_pos hL Carc).ne'
  field_simp

/-- Source geometry, not a free approximation-energy premise, makes the
linear/log replacement exponentially small relative to physical Y. -/
theorem source_actual_arc_ratio_exp_bound434
    (L x Z Hprime Y Carc CZ : ℝ) (hL : 1 ≤ L) (hx : 0 < x)
    (hLog : L = Real.log x) (hZlower : x*L^(-CZ) ≤ Z)
    (hH : 0 < Hprime) (hY : Y = Z*Hprime) (hCarc : 0 ≤ Carc) :
    (Hprime/L^Carc)/Y ≤ L^CZ*Real.exp (-L) := by
  have hLp : 0 < L := by linarith
  have hPow : 0 < L^CZ := Real.rpow_pos_of_pos hLp CZ
  have hZlow : x/L^CZ ≤ Z := by
    simpa only [Real.rpow_neg hLp.le,div_eq_mul_inv] using hZlower
  have hZp : 0 < Z := (div_pos hx hPow).trans_le hZlow
  have hArc : 1 ≤ L^Carc := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL hCarc
  have hZden : Z ≤ Z*L^Carc := by nlinarith
  have hInv := one_div_le_one_div_of_le hZp hZden
  have hInvZ : 1/Z ≤ L^CZ/x := by
    have hh := one_div_le_one_div_of_le (div_pos hx hPow) hZlow
    convert hh using 1 <;> field_simp
  rw [source_actual_arc_ratio_identity434 L Hprime Z Y Carc hLp hH hZp hY]
  calc
    _ ≤ 1/Z := hInv
    _ ≤ L^CZ/x := hInvZ
    _ = L^CZ*Real.exp (-L) := by
      rw [Real.exp_neg,hLog,Real.exp_log hx]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualFourDyadComparison -/

section

namespace Green64Analytic.CorrelationMellin

/-! Recover the exact four-dyad product scale comparisons
from one nonzero source coefficient's genuine m, p_s, p_l, r
support, with the original compact smooth-window scale w≈Y.
This elementary lemma is for the NONEMPTY box case only. -/
theorem source_actual_four_dyadic_box_comparison
    (Y A : ℝ) (M0 P P0 R0 m ps p r : ℕ)
    (hY : 0 ≤ Y) (hA : 1 ≤ A)
    (hm : m ∈ Finset.Icc M0 (2*M0))
    (hps : ps ∈ Finset.Icc P (2*P))
    (hp : p ∈ Finset.Icc P0 (2*P0))
    (hr : r ∈ Finset.Icc R0 (2*R0))
    (hWlow : Y ≤ A*((m*ps*p*r:ℕ):ℝ))
    (hWhigh : ((m*ps*p*r:ℕ):ℝ) ≤ A*Y) :
    Y ≤ (16*A)*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) ∧
    ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) ≤ (16*A)*Y := by
  have hm0 : (M0:ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hps0 : (P:ℝ) ≤ ps := by exact_mod_cast (Finset.mem_Icc.mp hps).1
  have hp0 : (P0:ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
  have hr0 : (R0:ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hm1 : (m:ℝ) ≤ 2*(M0:ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hm).2
  have hps1 : (ps:ℝ) ≤ 2*(P:ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hps).2
  have hp1 : (p:ℝ) ≤ 2*(P0:ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hp).2
  have hr1 : (r:ℝ) ≤ 2*(R0:ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).2
  have hlo : ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) ≤
      ((m*ps*p*r:ℕ):ℝ) := by
    calc
      ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) =
        (M0:ℝ)*P*P0*R0 := by push_cast; ring
      _ ≤ (m:ℝ)*ps*p*r := by gcongr
      _ = ((m*ps*p*r:ℕ):ℝ) := by push_cast; ring
  have hhi : ((m*ps*p*r:ℕ):ℝ) ≤
      16*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) := by
    calc
      ((m*ps*p*r:ℕ):ℝ) =
        (m:ℝ)*ps*p*r := by push_cast; ring
      _ ≤ (2*(M0:ℝ))*(2*(P:ℝ))*(2*(P0:ℝ))*(2*(R0:ℝ)) := by
        gcongr
      _ = 16*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) := by push_cast; ring
  have hC : (0:ℝ) ≤ A := by linarith
  constructor
  · calc
      Y ≤ A*((m*ps*p*r:ℕ):ℝ) := hWlow
      _ ≤ A*(16*(P:ℝ)*((M0*P0*R0:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_left hhi hC
      _ = (16*A)*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) := by ring
  · calc
      ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) ≤ ((m*ps*p*r:ℕ):ℝ) := hlo
      _ ≤ A*Y := hWhigh
      _ ≤ (16*A)*Y := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A) hY]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighNumeric -/

section

namespace Green64Analytic.CorrelationMellin

/-! Exact high-frequency coefficient budget: the restored literal
short-prime factor costs (2Cs)^2 and is absorbed into a larger
previously certified U1 saving without any new cardinality condition. -/

theorem source_actual_high_numeric_log_crush
    (L Cs : ℝ) (E D : ℕ)
    (hL : 3 ≤ L) (hCs : 0 ≤ Cs) (hCsBudget : Cs ≤ L^E) :
    (2*Cs)^2 * ((L^(D+2*E+5))⁻¹) ≤ (L^D)⁻¹ := by
  let B : ℕ := D+2*E+5
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hCsSq : Cs^2 ≤ (L^E)^2 :=
    (sq_le_sq₀ hCs (by positivity)).mpr hCsBudget
  have h4 : (4:ℝ) ≤ L^2 := by nlinarith [sq_nonneg (L-3)]
  have hExponent : 2+2*E+D ≤ B := by dsimp [B]; omega
  have hPower : L^(2+2*E+D) ≤ L^B :=
    pow_le_pow_right₀ hLone hExponent
  have hNumer : (2*Cs)^2 * L^D ≤ L^B := by
    calc
      _ = 4*Cs^2 * L^D := by ring
      _ ≤ 4*(L^E)^2 * L^D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCsSq (by norm_num))
          (pow_nonneg hLpos.le D)
      _ ≤ (L^2)*(L^E)^2 * L^D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h4 (sq_nonneg _))
          (pow_nonneg hLpos.le D)
      _ = L^(2+2*E+D) := by
        rw [←pow_mul, ←pow_add, ←pow_add]
        congr 1
        omega
      _ ≤ L^B := hPower
  have hDen : 0 < L^B := by positivity
  have hTarget : 0 < L^D := by positivity
  have hFrac : (2*Cs)^2 / L^B ≤ 1/L^D := by
    apply (div_le_div_iff₀ hDen hTarget).mpr
    simpa only [one_mul] using hNumer
  simpa only [B, div_eq_mul_inv, one_mul] using hFrac
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualJointModulusBudget -/

section

namespace Green64Analytic.CorrelationMellin

/-! Source rational-character modulus budget for ALL gcd classes d.
When the original character and the rational denominator both have
modulus at most L^C, every induced joint character has modulus at
most L^B as soon as 2*C ≤ B. No character-family size hypothesis. -/

theorem source_actual_joint_reduced_modulus_budget
    (qBase den d : ℕ) (L C B : ℝ)
    (hL : 1 ≤ L)
    (hBase : (qBase:ℝ) ≤ L^C)
    (hDen : (den:ℝ) ≤ L^C)
    (hB : 2*C ≤ B) :
    ((qBase*(den/d):ℕ):ℝ) ≤ L^B := by
  have hDiv : ((den/d:ℕ):ℝ) ≤ L^C := by
    calc
      _ ≤ (den:ℝ) := by
        exact_mod_cast Nat.div_le_self den d
      _ ≤ _ := hDen
  have hPowPos : 0 ≤ L^C := by
    exact Real.rpow_nonneg (by linarith) _
  have hMul :
      (qBase:ℝ)*((den/d:ℕ):ℝ) ≤ (L^C)*(L^C) :=
    mul_le_mul hBase hDiv (Nat.cast_nonneg _) hPowPos
  have hPow : L^C * L^C = L^(2*C) := by
    rw [←Real.rpow_add (by linarith : 0 < L)]
    congr 1
    ring
  calc
    _ = (qBase:ℝ)*((den/d:ℕ):ℝ) := by push_cast; ring
    _ ≤ L^C*L^C := hMul
    _ = L^(2*C) := hPow
    _ ≤ L^B := Real.rpow_le_rpow_of_exponent_le hL hB
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualRoughJointCharacter -/

section

namespace Green64Analytic.CorrelationMellin

/-! Character specialization for the genuine rough-alpha source
support. Uses exactly the source definition: every prime divisor of
m exceeds exp(sqrt L). The modulus qBase*(den/d) is bounded for all
gcd classes d|den by a fixed log power and is therefore coprime
to m. No free character or discrepancy hypothesis is inserted. -/

theorem source_actual_joint_character_rough_alpha
    (qBase den d m : ℕ)
    (chi0 : DirichletCharacter ℂ qBase)
    (xi : DirichletCharacter ℂ (den/d))
    (L C B : ℝ)
    (hBasePos : 0 < qBase) (hDenPos : 0 < den)
    (hd : d ∣ den)
    (hL : 1 ≤ L)
    (hBase : (qBase:ℝ) ≤ L^C)
    (hDen : (den:ℝ) ≤ L^C)
    (hB : 2*C ≤ B)
    (hW : L^B ≤ Real.exp (Real.sqrt L))
    (hRough : ∀ p : ℕ, p.Prime → p ∣ m →
       Real.exp (Real.sqrt L) < (p:ℝ)) :
    sourceJointCharacter qBase (den/d) chi0 xi
      (m : ZMod (qBase*(den/d))) =
        chi0 (m : ZMod qBase) * xi (m : ZMod (den/d)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hDenPos
  have hqpos : 0 < den/d :=
    Nat.div_pos (Nat.le_of_dvd hDenPos hd) hdpos
  have hmodpos : 0 < qBase*(den/d) :=
    Nat.mul_pos hBasePos hqpos
  have hModBudget :=
    source_actual_joint_reduced_modulus_budget
      qBase den d L C B hL hBase hDen hB
  have hCoprime : Nat.Coprime m (qBase*(den/d)) := by
    by_contra hh
    obtain ⟨p,hPrime,hDivM,hDivQ⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hh
    have hPLe : (p:ℝ) ≤ (qBase*(den/d):ℕ) := by
      exact_mod_cast Nat.le_of_dvd hmodpos hDivQ
    exact (not_lt_of_ge (hPLe.trans (hModBudget.trans hW)))
      (hRough p hPrime hDivM)
  have hUnit : IsCoprime (m:ℤ) (qBase*(den/d)) :=
    Nat.isCoprime_iff_coprime.mpr hCoprime
  simpa using source_joint_character_source_unit_exact
    qBase (den/d) chi0 xi (m:ℤ) hUnit
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLogWindowSchwartz -/

section

open scoped FourierTransform SchwartzMap ContDiff
namespace Green64Analytic.CorrelationMellin

/-! The ACTUAL source normalized logarithmic cutoff is a
compactly supported smooth function:
     u ↦ exp(u) * ψ₁(exp(u)).
No Fourier tail or artificial smoothness assertion is postulated. -/
noncomputable def sourceActualLogWindow
    (psi1 : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.exp u : ℝ) : ℂ) * psi1 (Real.exp u)

theorem source_actual_log_window_contDiff
    (psi1 : ℝ → ℂ) (hPsi : ContDiff ℝ ∞ psi1) :
    ContDiff ℝ ∞ (sourceActualLogWindow psi1) := by
  unfold sourceActualLogWindow
  change ContDiff ℝ ∞ (fun u : ℝ =>
    Complex.ofRealCLM (Real.exp u) * psi1 (Real.exp u))
  have he : ContDiff ℝ ∞ (Real.exp : ℝ → ℝ) := Real.contDiff_exp
  exact (Complex.ofRealCLM.contDiff.comp he).mul (hPsi.comp he)
theorem source_actual_log_window_hasCompactSupport
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A)
    (hPsi : ∀ u : ℝ, psi1 u ≠ 0 →
      (1/A ≤ u ∧ u ≤ A)) :
    HasCompactSupport (sourceActualLogWindow psi1) := by
  have hApos : 0 < A := by linarith
  have hInvPos : 0 < (1/A:ℝ) := one_div_pos.mpr hApos
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (Real.log (1/A)) (Real.log A)))
  intro u hu
  have hPsiNZ : psi1 (Real.exp u) ≠ 0 := by
    intro hz
    apply hu
    simp only [sourceActualLogWindow, hz, mul_zero]
  obtain ⟨hLo,hHi⟩ := hPsi (Real.exp u) hPsiNZ
  exact ⟨by simpa only [Real.log_exp] using Real.log_le_log hInvPos hLo,
         by simpa only [Real.log_exp] using
           Real.log_le_log (Real.exp_pos u) hHi⟩
noncomputable def sourceActualLogWindowSchwartz
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (source_actual_log_window_hasCompactSupport A psi1 hA hSupport)
    (source_actual_log_window_contDiff psi1 hSmooth)

theorem source_actual_log_window_fourier_inversion
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    𝓕⁻ (𝓕 (sourceActualLogWindowSchwartz
      A psi1 hA hSmooth hSupport)) =
      sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport := by
  exact FourierTransform.fourierInv_fourier_eq _
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSchwartzFourierTail -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace Green64Analytic.CorrelationMellin

/-! Quantitative tail estimate for the real Fourier transform of
the ORIGINAL smooth logarithmic source cutoff, using its Schwartz
weighted L¹ integrability. Not a postulated Fourier approximation. -/
theorem source_actual_schwartz_fourier_tail_mass_bound
    (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 1 ≤ R) (k : ℕ) :
    (∫ ξ in {ξ : ℝ | R ≤ |ξ|}, ‖(𝓕 f) ξ‖) ≤
      (R^k)⁻¹ * (∫ ξ : ℝ, |ξ|^k * ‖(𝓕 f) ξ‖) := by
  let F : 𝓢(ℝ,ℂ) := 𝓕 f
  let S : Set ℝ := {ξ : ℝ | R ≤ |ξ|}
  have hS : MeasurableSet S := by
    exact (isClosed_le continuous_const continuous_abs).measurableSet
  have hWeight : Integrable (fun ξ : ℝ => |ξ|^k * ‖F ξ‖) volume := by
    simpa only [Real.norm_eq_abs] using F.integrable_pow_mul volume k
  have hNorm : Integrable (fun ξ : ℝ => ‖F ξ‖) volume :=
    F.integrable.norm
  have hRpos : 0 < R := by linarith
  have hPowPos : 0 < R^k := pow_pos hRpos k
  have hPoint : ∀ ξ ∈ S,
      ‖F ξ‖ ≤ (R^k)⁻¹ * (|ξ|^k * ‖F ξ‖) := by
    intro ξ hξ
    have hAbs : R ≤ |ξ| := hξ
    have hPower : R^k ≤ |ξ|^k :=
      pow_le_pow_left₀ (by linarith : 0 ≤ R) hAbs k
    have hProduct :
        R^k * ‖F ξ‖ ≤ |ξ|^k * ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right hPower (norm_nonneg _)
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hPowPos).mpr (by simpa only [mul_comm] using hProduct)
  have hIntegrableNorm : IntegrableOn (fun ξ : ℝ => ‖F ξ‖) S :=
    hNorm.integrableOn
  have hIntegrableBound : IntegrableOn (fun ξ : ℝ =>
      (R^k)⁻¹ * (|ξ|^k * ‖F ξ‖)) S :=
    (hWeight.const_mul _).integrableOn
  have hNonneg : ∀ ξ : ℝ, 0 ≤ |ξ|^k * ‖F ξ‖ := by
    intro ξ
    positivity
  have hTailSubset :
      (∫ ξ in S, |ξ|^k * ‖F ξ‖) ≤
      ∫ ξ : ℝ, |ξ|^k * ‖F ξ‖ := by
    have hUniv : IntegrableOn (fun ξ : ℝ => |ξ|^k * ‖F ξ‖)
        Set.univ := by simpa using hWeight
    have hMono := setIntegral_mono_set (s:=S) (t:=Set.univ)
      hUniv (Filter.Eventually.of_forall hNonneg)
      (Set.subset_univ S).eventuallySubset
    simpa only [setIntegral_univ] using hMono
  calc
    (∫ ξ in S, ‖F ξ‖) ≤
      ∫ ξ in S, (R^k)⁻¹ * (|ξ|^k * ‖F ξ‖) :=
        setIntegral_mono_on hIntegrableNorm hIntegrableBound hS hPoint
    _ = (R^k)⁻¹ * (∫ ξ in S, |ξ|^k * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ ≤ (R^k)⁻¹ * (∫ ξ : ℝ, |ξ|^k * ‖F ξ‖) :=
      mul_le_mul_of_nonneg_left hTailSubset (inv_nonneg.mpr (pow_nonneg hRpos.le _))
theorem source_actual_log_window_fourier_tail_mass_bound
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (R : ℝ) (hR : 1 ≤ R) (k : ℕ) :
    (∫ ξ in {ξ : ℝ | R ≤ |ξ|},
      ‖(𝓕 (sourceActualLogWindowSchwartz
          A psi1 hA hSmooth hSupport)) ξ‖) ≤
      (R^k)⁻¹ * (∫ ξ : ℝ,
        |ξ|^k * ‖(𝓕 (sourceActualLogWindowSchwartz
          A psi1 hA hSmooth hSupport)) ξ‖) :=
  source_actual_schwartz_fourier_tail_mass_bound
    (sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport) R hR k
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLogWindowTailSaving -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff
namespace Green64Analytic.CorrelationMellin

/-! For a FIXED original smooth compact cutoff psi1, its actual
Fourier L1 tail beyond |xi| >= L saves ANY prescribed log power.
The Fourier weight is derived from the exact Schwartz transform;
there is no free hTail parameter. Uniformity across L-dependent
cutoff families requires separate source derivative budgets. -/
theorem eventually_source_actual_fixed_log_window_fourier_tail_saving
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (D : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∫ ξ in {ξ : ℝ | L ≤ |ξ|},
        ‖(𝓕 (sourceActualLogWindowSchwartz
          A psi1 hA hSmooth hSupport)) ξ‖) ≤
        (L^D)⁻¹ := by
  let f : 𝓢(ℝ,ℂ) :=
    sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  let g : 𝓢(ℝ,ℂ) := 𝓕 f
  let K : ℝ := ∫ ξ : ℝ, |ξ|^(D+2) * ‖g ξ‖
  have hK : 0 ≤ K := by
    dsimp [K]
    apply integral_nonneg
    intro ξ
    positivity
  filter_upwards [eventually_ge_atTop (max 3 (K+1))]
    with L hL
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hL2 : K ≤ L^2 := by
    have hk' : K+1 ≤ L := (le_max_right _ _).trans hL
    nlinarith [sq_nonneg (L-3)]
  have hTimeTail :
      (∫ ξ in {ξ : ℝ | L ≤ |ξ|}, ‖g ξ‖) ≤
        (L^(D+2))⁻¹ * K := by
    exact source_actual_schwartz_fourier_tail_mass_bound
      f L hLone (D+2)
  have hPow : L^(D+2) = L^D*L^2 := by
    rw [pow_add]
  have hNumer : K*L^D ≤ L^(D+2) := by
    calc
      _ ≤ L^2*L^D :=
        mul_le_mul_of_nonneg_right hL2 (pow_nonneg hLpos.le _)
      _ = L^(D+2) := by rw [hPow]; ring
  have hFrac : K / L^(D+2) ≤ 1/L^D := by
    apply (div_le_div_iff₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr
    simpa only [one_mul] using hNumer
  have hNumerical : (L^(D+2))⁻¹*K ≤ (L^D)⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hFrac
  simpa only [f,g,K] using hTimeTail.trans hNumerical
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLowNumeric -/

section

namespace Green64Analytic.CorrelationMellin

/-! Complete quantitative source low-frequency bound: four real
coefficient/group-time budgets produce a fixed log-power saving
without assuming the desired mean-square as a hypothesis. -/

theorem source_actual_low_numeric_log_crush
    (L T Cs Cl C H : ℝ) (E D : ℕ)
    (hL : 3 ≤ L)
    (hT : 0 ≤ T) (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hTbudget : T ≤ L^E)
    (hCsbudget : Cs ≤ L^E)
    (hClbudget : Cl ≤ L^E)
    (hCbudget : C ≤ L^E)
    (hHbudget : H ≤ L^E) :
    2*T*((2*Cs)*(2*Cl)*
      ((L^(D+5*E+10))⁻¹*(2*(C*H))))^2 ≤
        (L^D)⁻¹ := by
  let A : ℝ := L^E
  let B : ℕ := D+5*E+10
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCsA : Cs ≤ A := hCsbudget
  have hClA : Cl ≤ A := hClbudget
  have hCA : C ≤ A := hCbudget
  have hHA : H ≤ A := hHbudget
  have hTA : T ≤ A := hTbudget
  have hP1 : Cs*Cl ≤ A*A :=
    mul_le_mul hCsA hClA hCl hA
  have hP2 : (Cs*Cl)*C ≤ (A*A)*A :=
    mul_le_mul hP1 hCA hC (mul_nonneg hA hA)
  have hP3 : ((Cs*Cl)*C)*H ≤ ((A*A)*A)*A :=
    mul_le_mul hP2 hHA hH (mul_nonneg (mul_nonneg hA hA) hA)
  have hProd : Cs*Cl*C*H ≤ A^4 := by
    convert hP3 using 1 <;> ring
  have hProd2 : (Cs*Cl*C*H)^2 ≤ A^8 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ Cs*Cl*C*H)
      (by positivity : 0 ≤ A^4)).mpr hProd
    simpa only [← pow_mul, Nat.reduceMul] using h
  have hTProd : T*(Cs*Cl*C*H)^2 ≤ A*A^8 :=
    mul_le_mul hTA hProd2 (sq_nonneg _) hA
  have hMain : 2*T*((2*Cs)*(2*Cl)*(2*(C*H)))^2 ≤
      128*A^9 := by
    calc
      _ = 128*(T*(Cs*Cl*C*H)^2) := by ring
      _ ≤ 128*(A*A^8) :=
        mul_le_mul_of_nonneg_left hTProd (by norm_num)
      _ = _ := by ring
  have h128 : (128:ℝ) ≤ L^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hL 5
    norm_num at h
    linarith
  have hA9 : A^9 = L^(9*E) := by
    dsimp [A]
    rw [←pow_mul]
    congr 1
    omega
  have hPowBound : L^(5+9*E+D) ≤ L^(2*B) :=
    pow_le_pow_right₀ hLone (by dsimp [B]; omega)
  have hNum : (128*A^9)*L^D ≤ (L^B)^2 := by
    calc
      _ ≤ L^5 * (L^(9*E)) * L^D := by
        rw [←hA9]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h128 (pow_nonneg hA 9))
          (pow_nonneg hLpos.le D)
      _ = L^(5+9*E+D) := by
        rw [←pow_add, ←pow_add]
      _ ≤ L^(2*B) := hPowBound
      _ = _ := by
        rw [←pow_mul]
        congr 1
        omega
  have hDen : 0 < (L^B)^2 := by positivity
  have hLpow : 0 < L^D := by positivity
  have hQuot :
      (128*A^9)/(L^B)^2 ≤ 1/(L^D) := by
    apply (div_le_div_iff₀ hDen hLpow).mpr
    simpa only [one_mul] using hNum
  have hSmall :
      ((L^B)⁻¹)^2 * (128*A^9) ≤ (L^D)⁻¹ := by
    simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_comm,
      mul_left_comm] using hQuot
  change 2*T*((2*Cs)*(2*Cl)*
      ((L^B)⁻¹*(2*(C*H))))^2 ≤ (L^D)⁻¹
  calc
    _ = ((L^B)⁻¹)^2 *
        (2*T*((2*Cs)*(2*Cl)*(2*(C*H)))^2) := by ring
    _ ≤ ((L^B)⁻¹)^2 * (128*A^9) :=
      mul_le_mul_of_nonneg_left hMain (sq_nonneg _)
    _ ≤ _ := hSmall
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUnifiedSavingNumerics -/

section

namespace Green64Analytic.CorrelationMellin

/-! Numeric conclusion for the original source three-way
full Mellin energy: reserve two additional log powers in every
component, then absorb all three into the requested power. -/
theorem source_actual_three_contributions_log_crush
    (L : ℝ) (D : ℕ) (hL : 3 ≤ L) :
    (L^(D+2))⁻¹ + (L^(D+2))⁻¹ + (L^(D+2))⁻¹ ≤
      (L^D)⁻¹ := by
  have hLpos : 0 < L := by linarith
  have hSquare : (3:ℝ) ≤ L^2 := by nlinarith [sq_nonneg (L-3)]
  have hPower : 3*L^D ≤ L^(D+2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hSquare
      (pow_nonneg hLpos.le D)]
  have hFrac : 3 / L^(D+2) ≤ 1 / L^D := by
    apply (div_le_div_iff₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr
    nlinarith [hPower]
  calc
    _ = 3 / L^(D+2) := by ring
    _ ≤ 1 / L^D := hFrac
    _ = (L^D)⁻¹ := by ring
theorem source_actual_stronger_log_saving
    (L : ℝ) (D Dextra : ℕ)
    (hL : 3 ≤ L) (hD : D ≤ Dextra) :
    (L^Dextra)⁻¹ ≤ (L^D)⁻¹ := by
  have hLpos : 0 < L := by linarith
  apply (inv_le_inv₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr
  exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ L) hD
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUniformFreeScale -/

section

open Filter Asymptotics
namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- The literal original comparison lower scale exp(2L^c-O(1)) dominates
all small-prime and fixed major-arc log powers when b<c. -/
theorem eventually_source_actual_original_free_scale
    (b c Ccomp Carc K : ℝ) (hbc : b < c) (hc : 0 < c)
    (hC : 0 < Ccomp) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (P : ℕ) (Hprime : ℝ),
      (P:ℝ) ≤ Real.exp (L^b) → Real.exp (2*L^c-K) ≤ Hprime →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime := by
  let eps : ℝ := 1/(4*(1+|Carc|))
  have hEps : 0 < eps := by dsimp [eps]; positivity
  have hLog := (isLittleO_log_rpow_atTop hc).bound hEps
  have hRatio := (tendsto_rpow_neg_atTop (sub_pos.mpr hbc)).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4))
  have hConst := (tendsto_rpow_atTop hc).eventually
    (eventually_ge_atTop (4*(|Real.log (2*Ccomp)|+K)))
  filter_upwards [hLog,hRatio,hConst,eventually_ge_atTop (1:ℝ)] with
    L hLogL hRatioL hConstL hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hPow0 : 0 ≤ L^c := Real.rpow_nonneg hLp.le _
  have hLog' : Real.log L ≤ eps*L^c := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hLog0,abs_of_nonneg hPow0] using hLogL
  have hRatioEq : L^(-(c-b)) = L^b/L^c := by
    rw [show -(c-b)=b-c by ring,Real.rpow_sub hLp]
  rw [hRatioEq] at hRatioL
  have hShort : L^b ≤ L^c/4 := by
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hLp c)).mp hRatioL.le
    nlinarith
  have hPhase : (1+Carc)*Real.log L ≤ L^c/4 := by
    have hCarc := le_abs_self Carc
    have hCoefPos : 0 < 1+|Carc| := by positivity
    have hMult := mul_le_mul_of_nonneg_left hLog' hCoefPos.le
    have hId : (1+|Carc|)*eps = 1/4 := by dsimp [eps]; field_simp
    calc
      _ ≤ (1+|Carc|)*Real.log L := mul_le_mul_of_nonneg_right (by linarith) hLog0
      _ ≤ ((1+|Carc|)*eps)*L^c := by simpa only [mul_assoc] using hMult
      _ = L^c/4 := by rw [hId]; ring
  have hTotal : Real.log (2*Ccomp)+(1+Carc)*Real.log L+L^b ≤ 2*L^c-K := by
    have ha := le_abs_self (Real.log (2*Ccomp))
    nlinarith
  intro P Hprime hP hH
  calc
    2*L*Ccomp*(P:ℝ)*L^Carc ≤ 2*L*Ccomp*Real.exp (L^b)*L^Carc := by gcongr
    _ = Real.exp (Real.log (2*Ccomp)+(1+Carc)*Real.log L+L^b) := by
      rw [show Real.log (2*Ccomp)+(1+Carc)*Real.log L+L^b =
        Real.log (2*Ccomp)+Real.log L+L^b+Real.log L*Carc by ring]
      rw [Real.exp_add,Real.exp_add,Real.exp_add,
        Real.exp_log (by positivity : 0 < 2*Ccomp),Real.exp_log hLp,
        Real.rpow_def_of_pos hLp Carc]
      ring
    _ ≤ Real.exp (2*L^c-K) := Real.exp_le_exp.mpr hTotal
    _ ≤ Hprime := hH
end Green64Analytic.CorrelationMellin

end

/-! ## SourceAllIntegerDivisorMajorant -/

section

/-! The unconditional all-integer inequality `tau(n)^2 <= d4(n)`.
This is stronger than the squarefree-only bound in the predecessor
and is exactly what the physical source R(t) coefficient norm needs.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_all_integer_divisor_square_le_fourfold
    (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card^2 ≤
      ((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) n := by
  classical
  have hf : (ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_sigma
  have hg : ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) *
      (ArithmeticFunction.sigma 0)).IsMultiplicative := hf.mul hf
  have hfactorF := hf.multiplicative_factorization
    (ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) hn
  have hfactorG := hg.multiplicative_factorization
    ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ)*
      (ArithmeticFunction.sigma 0)) hn
  have hProdPow :
      (n.factorization.prod (fun p k =>
        ArithmeticFunction.sigma 0 (p^k)))^2 =
      n.factorization.prod (fun p k =>
        (ArithmeticFunction.sigma 0 (p^k))^2) := by
    simp only [Finsupp.prod, Finset.prod_pow]
  have hProdLe :
      n.factorization.prod (fun p k =>
        (ArithmeticFunction.sigma 0 (p^k))^2) ≤
      n.factorization.prod (fun p k =>
        ((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) (p^k)) := by
    simp only [Finsupp.prod]
    apply Finset.prod_le_prod
    · intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors
        (by simpa only [Nat.support_factorization] using hp)
      exact source_sigma_square_prime_pow_le_fourfold p
        (n.factorization p) hpprime
  calc
    n.divisors.card^2 =
        (ArithmeticFunction.sigma 0 n)^2 := by
          rw [ArithmeticFunction.sigma_zero_apply]
    _ = (n.factorization.prod (fun p k =>
        ArithmeticFunction.sigma 0 (p^k)))^2 := by rw [hfactorF]
    _ = n.factorization.prod (fun p k =>
        (ArithmeticFunction.sigma 0 (p^k))^2) := hProdPow
    _ ≤ n.factorization.prod (fun p k =>
        ((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) (p^k)) := hProdLe
    _ = ((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) n :=
      hfactorG.symm
end Green64Analytic.CorrelationMellin

end

/-! ## SourceArcFourBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- Scalar assembly only. Its analytic premises are supplied by the original
FULL discrepancy theorem and the three separately proved error estimates. -/
theorem source_arc_four_budget434
    (energy low tail rep square cb K Z Cl Ct : ℝ)
    (hcb : 0 < cb) (hK : 0 ≤ K)
    (hLow : low ≤ Cl*Z) (hTail : tail ≤ Ct*Z)
    (hRep : rep ≤ Z) (hSquare : square ≤ Z)
    (hFull : cb^2*energy ≤ 2*(2*(K*(low+tail))+2*rep)+2*cb^2*square) :
    energy ≤ ((4*K*(Cl+Ct)+4+2*cb^2)/cb^2)*Z := by
  have hcb2 : 0 < cb^2 := sq_pos_of_pos hcb
  have hLT := mul_le_mul_of_nonneg_left (add_le_add hLow hTail)
    (by positivity : 0 ≤ 4*K)
  have hR := mul_le_mul_of_nonneg_left hRep (by norm_num : (0:ℝ) ≤ 4)
  have hS := mul_le_mul_of_nonneg_left hSquare (by positivity : 0 ≤ 2*cb^2)
  have hAll : cb^2*energy ≤ (4*K*(Cl+Ct)+4+2*cb^2)*Z := by
    nlinarith only [hFull,hLT,hR,hS]
  apply (mul_le_mul_iff_right₀ hcb2).mp
  calc
    cb^2*energy ≤ (4*K*(Cl+Ct)+4+2*cb^2)*Z := hAll
    _ = cb^2*(((4*K*(Cl+Ct)+4+2*cb^2)/cb^2)*Z) := by field_simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcScalarPower -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- Exact absorption of a fixed real log loss by a natural decay order. -/
theorem source_arc_rpow_nat_decay434 (L E : ℝ) (n A : ℕ)
    (hL : 1 ≤ L) (hOrder : E+(A:ℝ) ≤ (n:ℝ)) :
    L^E * (L^n)⁻¹ ≤ (L^A)⁻¹ := by
  have hLp : 0 < L := by linarith
  have hExp : E-(n:ℝ) ≤ -(A:ℝ) := by linarith
  calc
    _ = L^(E-(n:ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hLp, Real.rpow_neg hLp.le,
        Real.rpow_natCast]
    _ ≤ L^(-(A:ℝ)) := Real.rpow_le_rpow_of_exponent_le hL hExp
    _ = _ := by rw [Real.rpow_neg hLp.le, Real.rpow_natCast]

/-- Rearrange the original marked prefactor and the 64 tail powers. -/
theorem source_arc_tail_power_identity434 (L v Y C E : ℝ) (j : ℕ)
    (hL : 0 < L) :
    C*((1/v)*L^E)^2*Y*L^64*(L^(j-2))⁻¹ =
      C*(1/v)^2*Y*(L^(2*E+64)*(L^(j-2))⁻¹) := by
  have hPow : L^(2*E+64) = (L^E)^2 * L^(64:ℕ) := by
    rw [Real.rpow_add hL, show 2*E = E*2 by ring, Real.rpow_mul hL.le]
    norm_num
  rw [hPow]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCollisionArithmetic -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Literal arithmetic of a free auxiliary prime p in D_C=p*D.
When p divides the source w, it automatically divides the shifted
target w+k*p*D, including negative k. The converse is equally exact. -/
theorem source_auxiliary_shift_divisibility434
    (p n D : ℕ) (k : ℤ)
    (hpos : 0 < (n:ℤ)+k*(p:ℤ)*(D:ℤ)) :
    p ∣ ((n:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat ↔ p ∣ n := by
  have hMultiple : (p:ℤ) ∣ k*(p:ℤ)*(D:ℤ) := by
    refine ⟨k*(D:ℤ),?_⟩
    ring
  have hCast : (((n:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat:ℤ) =
      (n:ℤ)+k*(p:ℤ)*(D:ℤ) := Int.toNat_of_nonneg hpos.le
  constructor
  · intro hd
    have hz : (p:ℤ) ∣ (n:ℤ)+k*(p:ℤ)*(D:ℤ) := by
      have hx : (p:ℤ) ∣ (((n:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat:ℤ) := by
        exact_mod_cast hd
      simpa only [hCast] using hx
    have hn : (p:ℤ) ∣ (n:ℤ) := by
      have hh := dvd_sub hz hMultiple
      convert hh using 1 <;> ring
    exact_mod_cast hn
  · intro hd
    have hn : (p:ℤ) ∣ (n:ℤ) := by exact_mod_cast hd
    have hh := dvd_add hn hMultiple
    have hz : (p:ℤ) ∣ (((n:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat:ℤ) := by
      simpa only [hCast] using hh
    exact_mod_cast hz

/-- Exact signed linear scaling after charging an auxiliary collision.
No replacement of 2*k by k or of the original sign convention. -/
theorem source_auxiliary_signed_shift_scaling434
    (p y D : ℕ) (k : ℤ) :
    (((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ)) =
      (p:ℤ)*((y:ℤ)+k*(D:ℤ)) := by
  push_cast
  ring

/-- The post-charging positive endpoint remains the literal p-fold
image of y+kD under Int.toNat, with no spurious zero term. -/
theorem source_auxiliary_signed_toNat_scaling434
    (p y D : ℕ) (k : ℤ) (hp : 0 < p)
    (hpos : 0 < (y:ℤ)+k*(D:ℤ)) :
    (((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ)).toNat =
      p*((y:ℤ)+k*(D:ℤ)).toNat := by
  have hP : (0:ℤ) < p := by exact_mod_cast hp
  have hA : 0 ≤ ((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ) := by
    rw [source_auxiliary_signed_shift_scaling434]
    exact (mul_pos hP hpos).le
  have hCast : ((((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ)).toNat:ℤ) =
      ((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ) := Int.toNat_of_nonneg hA
  have hY : ((((y:ℤ)+k*(D:ℤ)).toNat:ℤ)) =
      (y:ℤ)+k*(D:ℤ) := Int.toNat_of_nonneg hpos.le
  have heq : ((((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ)).toNat:ℤ) =
      ((p*((y:ℤ)+k*(D:ℤ)).toNat:ℕ):ℤ) := by
    rw [hCast]
    simp only [Nat.cast_mul,hY]
    exact source_auxiliary_signed_shift_scaling434 p y D k
  exact_mod_cast heq
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCeilLogBudget -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 250000

/-- The physical support n ≤ ceil(A Y) has the CORRECT Y scale.
No dependence on the possibly huge bookkeeping cutoff N. -/
theorem source_original_ceil_support_scale434
    (A Y : ℝ) (hA : 1 ≤ A) (hY : 1 ≤ Y) :
    (Nat.ceil (A*Y):ℝ) ≤ 2*A*Y := by
  have hAY : 1 ≤ A*Y := by nlinarith
  have hNonneg : 0 ≤ A*Y := by linarith
  have hceil : (Nat.ceil (A*Y):ℝ) < A*Y+1 :=
    Nat.ceil_lt_add_one hNonneg
  nlinarith

/-- Quantitative change from the real source support ceiling to a
uniform O(Y) bound, including the true sixth divisor moment log^63. -/
theorem source_original_ceil_log_moment_scale434
    (A Y : ℝ) (hA : 1 ≤ A) (hY : 1 ≤ Y) :
    (Nat.ceil (A*Y):ℝ) *
      (1+Real.log (Nat.ceil (A*Y):ℝ))^63 ≤
      (2*A*Y)*(1+Real.log (2*A*Y))^63 := by
  have hM : 0 < (Nat.ceil (A*Y):ℝ) := by
    have ha : 0 < A*Y := by positivity
    have hm : 1 ≤ Nat.ceil (A*Y) :=
      (Nat.one_le_ceil_iff).mpr ha
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hm)
  have hMle : (Nat.ceil (A*Y):ℝ) ≤ 2*A*Y :=
    source_original_ceil_support_scale434 A Y hA hY
  have hLog := Real.log_le_log hM hMle
  have hMge : 1 ≤ (Nat.ceil (A*Y):ℝ) := by
    have hh : 1 ≤ A*Y := by nlinarith
    exact hh.trans (Nat.le_ceil _)
  have hLogNonneg : 0 ≤ Real.log (Nat.ceil (A*Y):ℝ) :=
    Real.log_nonneg hMge
  have hPow :
      (1+Real.log (Nat.ceil (A*Y):ℝ))^63 ≤
      (1+Real.log (2*A*Y))^63 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  exact (mul_le_mul hMle hPow (by positivity) (by positivity)).trans_eq
    (by ring)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCircleParseval -/

section

open MeasureTheory
open scoped BigOperators

noncomputable def sourceCircleFourierPoly
    (s : Finset ℤ) (a : ℤ → ℂ) : C(AddCircle (1:ℝ), ℂ) :=
  ∑ n ∈ s, a n • fourier n

theorem source_circle_fourier_parseval
    (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x : AddCircle (1:ℝ),
      ‖(sourceCircleFourierPoly s a) x‖^2
          ∂AddCircle.haarAddCircle) = ∑ n ∈ s, ‖a n‖^2 := by
  let F := sourceCircleFourierPoly s a
  let P := (ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) F
  have hmap : P = ∑ n ∈ s, a n • (fourierLp (T := 1) 2 n) := by
    simp [P, F, sourceCircleFourierPoly, map_sum, map_smul, fourierLp]
  have hInt : Integrable (fun x : AddCircle (1:ℝ) =>
      F x * (starRingEnd ℂ) (F x)) AddCircle.haarAddCircle := by
    have hc : Continuous (fun x : AddCircle (1:ℝ) =>
        F x * (starRingEnd ℂ) (F x)) :=
      F.continuous.mul (Complex.continuous_conj.comp F.continuous)
    simpa [IntegrableOn] using
      (hc.continuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle)
          isCompact_univ)
  have hnorm : ‖P‖^2 =
      ∫ x : AddCircle (1:ℝ), ‖F x‖^2 ∂AddCircle.haarAddCircle := by
    dsimp [P]
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      MeasureTheory.ContinuousMap.inner_toLp]
    rw [← integral_re hInt]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [← hnorm, hmap]
  exact source_fourierLp_finite_parseval s a

end

/-! ## SourceCircleArcEnergy -/

section

open MeasureTheory
open scoped BigOperators

/-- Every measurable rational or other arc on the normalized
frequency circle has Fourier energy ≤ the coefficient L² mass.
The proof is literal continuous Parseval, not a conditional
large-sieve or analytic discrepancy bound. -/
theorem source_circle_arc_energy_le_coeff_l2
    (s : Finset ℤ) (a : ℤ → ℂ) (A : Set (AddCircle (1:ℝ))) :
    (∫ x in A, ‖(sourceCircleFourierPoly s a) x‖^2
          ∂AddCircle.haarAddCircle) ≤
      ∑ n ∈ s, ‖a n‖^2 := by
  let F := sourceCircleFourierPoly s a
  let f : AddCircle (1:ℝ) → ℝ := fun x => ‖F x‖^2
  have hcontinuous : Continuous f := by
    exact (continuous_norm.comp F.continuous).pow 2
  have hInt : Integrable f AddCircle.haarAddCircle := by
    simpa [IntegrableOn] using
      (hcontinuous.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ)
  have hn : 0 ≤ᵐ[AddCircle.haarAddCircle.restrict (Set.univ)] f :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hsubset : A ⊆ (Set.univ : Set (AddCircle (1:ℝ))) :=
    Set.subset_univ _
  calc
    (∫ x in A, ‖F x‖^2 ∂AddCircle.haarAddCircle) ≤
        ∫ x in (Set.univ : Set (AddCircle (1:ℝ))),
          ‖F x‖^2 ∂AddCircle.haarAddCircle :=
      MeasureTheory.setIntegral_mono_set
        (by simpa [IntegrableOn, Measure.restrict_univ] using hInt)
        hn hsubset.eventuallyLE
    _ = ∑ n ∈ s, ‖a n‖^2 := by
      simpa only [Measure.restrict_univ, F] using
        source_circle_fourier_parseval s a

end

/-! ## SourceCompactBumpBase -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000
noncomputable section

/-- A genuine smooth nonnegative bump: inner radius 1/2, outer radius 1. -/
def sourceCompactBump434 : ContDiffBump (0 : ℝ) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

def sourceCompactBumpSchwartz434 : 𝓢(ℝ,ℂ) :=
  (sourceCompactBump434.hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp sourceCompactBump434.contDiff)

theorem source_compact_bump_support434 (x : ℝ)
    (hx : sourceCompactBumpSchwartz434 x ≠ 0) : |x| ≤ 1 := by
  have hx' : sourceCompactBump434 x ≠ 0 := by
    intro h
    apply hx
    change (sourceCompactBump434 x : ℂ) = 0
    exact_mod_cast h
  have hb : x ∈ Metric.ball (0 : ℝ) sourceCompactBump434.rOut := by
    rw [← sourceCompactBump434.support_eq]
    exact hx'
  have hlt : |x| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq, sourceCompactBump434] using hb
  exact hlt.le

/-- The chosen auxiliary kernel has strictly positive Fourier mass at zero. -/
theorem source_compact_bump_fourier_zero434 :
    (𝓕 (sourceCompactBumpSchwartz434 : ℝ → ℂ)) 0 =
      ((∫ x : ℝ, sourceCompactBump434 x : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, one_smul]
  exact (Complex.ofRealCLM.integral_comp_comm
    (sourceCompactBump434.integrable (μ := volume)))

theorem source_compact_bump_fourier_zero_pos434 :
    0 < ‖(𝓕 (sourceCompactBumpSchwartz434 : ℝ → ℂ)) 0‖ := by
  rw [source_compact_bump_fourier_zero434, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceCompactBump434.integral_pos (μ := volume))]
  exact sourceCompactBump434.integral_pos
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceHarmonicPhysicalWindow -/

section

open MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 6500000

/-- A fixed smooth physical cutoff equals one on [1/A,A] and vanishes
outside a fixed POSITIVE interval. It is independent of all frequencies. -/
theorem source_harmonic_physical_window434 (A : ℝ) (hA : 1 ≤ A) :
    ∃ psi : ℝ → ℂ, ContDiff ℝ ∞ psi ∧ HasCompactSupport psi ∧
      (∀ r, psi r ≠ 0 → 1/(4*A) ≤ r ∧ r ≤ 4*A) ∧
      (∀ r ∈ Set.Icc (1/A) A, psi r = 1) ∧ (∀ r, ‖psi r‖ ≤ 1) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hRec : 0 < 1/A := one_div_pos.mpr hAp
  have hRecone : 1/A ≤ 1 := (div_le_one hAp).mpr hA
  let b : ContDiffBump A := ⟨A-1/(2*A),A-1/(4*A),by
    have heq : 1/(2*A)=(1/A)/2 := by field_simp
    rw [heq]
    linarith,by
    have h1 : 1/(2*A)=(1/A)/2 := by field_simp
    have h2 : 1/(4*A)=(1/A)/4 := by field_simp
    rw [h1,h2]
    linarith⟩
  let psi : ℝ → ℂ := fun r => (b r:ℂ)
  refine ⟨psi,Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := fun y : ℝ => (y:ℂ)) (by simp),?_,?_,?_⟩
  · intro r hr
    have hb : b r ≠ 0 := by intro hz; apply hr; simp only [psi,hz,Complex.ofReal_zero]
    have hBall : r ∈ Metric.ball A b.rOut := by rw [←b.support_eq]; exact hb
    have hd : |r-A| < A-1/(4*A) := by
      simpa only [Metric.mem_ball,Real.dist_eq,b] using hBall
    have hh := abs_lt.mp hd
    constructor <;> linarith [one_div_pos.mpr (by positivity : 0 < 4*A)]
  · intro r hr
    have hbr : r ∈ Metric.closedBall A b.rIn := by
      simp only [Metric.mem_closedBall,Real.dist_eq,b,abs_le]
      have heq : 1/(2*A)=(1/A)/2 := by field_simp
      rw [heq]
      constructor <;> linarith [hr.1,hr.2]
    change (b r:ℂ) = 1
    rw [b.one_of_mem_closedBall hbr,Complex.ofReal_one]
  · intro r
    change ‖(b r:ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (b.nonneg)]
    exact b.le_one

/-- Dividing a genuine positive-support smooth profile by r is smooth
on the whole real line, including zero. No differentiability hole is assumed. -/
theorem source_harmonic_reciprocal_smooth434
    (psi : ℝ → ℂ) (a : ℝ) (ha : 0 < a) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ r, psi r ≠ 0 → a ≤ r) :
    ContDiff ℝ ∞ (fun r => psi r/(r:ℂ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r=0
  · subst r
    have heq : (fun r : ℝ => psi r/(r:ℂ)) =ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
      filter_upwards [gt_mem_nhds ha] with r hr
      have hz : psi r=0 := by
        by_contra hne
        exact (not_lt_of_ge (hSupport r hne)) hr
      simp only [hz,zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hi : ContDiffAt ℝ ∞ (fun u : ℝ => u⁻¹) r := contDiffAt_id.inv hr
    have hh : ContDiffAt ℝ ∞ (fun u : ℝ => u⁻¹ • psi u) r := hi.smul hSmooth.contDiffAt
    simpa only [Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using hh
end Green64Analytic.CorrelationSquare

end

