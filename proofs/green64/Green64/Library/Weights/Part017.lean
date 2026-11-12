module

public import Green64.Library.Weights.Part016
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Green64.Library.Weights.Part015
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Weights / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalHoeffdingRealParseval -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- ACTUAL real BIG-prime reciprocal-harmonic L2 Parseval,
for all centered/averaged coordinate Hoeffding components.
No abstract degree energy, no independence of observable f
and no source prime distinctness is introduced. -/
theorem source_original_big_actual_hoeffding_parseval434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (L : List (Fin M)) (hL : L.Nodup)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434 mu f =
      ∑ S ∈ L.toFinset.powerset,
        sourceOriginalBigActualEnergy434 mu
          (sourceOriginalHoeffdingList434
            (fun p => (mu p:ℂ)) S L f) := by
  have h := source_original_big_hoeffding_pairing_parseval434
    mu hmu L hL f
  simp_rw [source_original_big_pairing_is_actual_energy434] at h
  exact_mod_cast h

/-- Same equality specialized to actual source03 independent
reciprocal-prime BIG labels under the exact V=sum 1/p
normalization, WITHOUT an unproved Hoeffding Parseval axiom. -/
theorem source_original_harmonic_big_actual_hoeffding_parseval434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ) (V : ℝ)
    (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ))
    (L : List (Fin M)) (hL : L.Nodup)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V) f =
      ∑ S ∈ L.toFinset.powerset,
        sourceOriginalBigActualEnergy434
          (sourceOriginalHarmonicPrimeMu434 prime V)
          (sourceOriginalHoeffdingList434
            (fun p => (sourceOriginalHarmonicPrimeMu434 prime V p:ℂ))
            S L f) := by
  exact source_original_big_actual_hoeffding_parseval434
    (sourceOriginalHarmonicPrimeMu434 prime V)
    (source_original_harmonic_prime_normalized434
       prime V hV hEq) L hL f
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingModeCommutation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- Two distinct source TRUE BIG coordinate modes always
commute: E_i and centered D_i=I-E_i are projections with
the source's actual reciprocal-prime law, not artificial
tensor-factor scalar multipliers. -/
theorem source_original_hoeffding_modes_commute434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i j : Fin M) (hij : i ≠ j)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalHoeffdingMode434 mu S i
      (sourceOriginalHoeffdingMode434 mu S j f) x =
    sourceOriginalHoeffdingMode434 mu S j
      (sourceOriginalHoeffdingMode434 mu S i f) x := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [sourceOriginalHoeffdingMode434, if_pos hi, if_pos hj]
    change sourceOriginalBigCoordinateDiff434 mu i
      (sourceOriginalBigCoordinateDiff434 mu j f) x =
      sourceOriginalBigCoordinateDiff434 mu j
      (sourceOriginalBigCoordinateDiff434 mu i f) x
    change
      (f x - sourceOriginalCoordinateMean434 mu j f x) -
         sourceOriginalCoordinateMean434 mu i
            (sourceOriginalBigCoordinateDiff434 mu j f) x =
      (f x - sourceOriginalCoordinateMean434 mu i f x) -
         sourceOriginalCoordinateMean434 mu j
            (sourceOriginalBigCoordinateDiff434 mu i f) x
    rw [source_original_big_average_diff_commute434 mu i j hij f x]
    rw [source_original_big_average_diff_commute434 mu j i hij.symm f x]
    dsimp only [sourceOriginalBigCoordinateDiff434]
    rw [source_original_coordinate_means_commute434 mu i j hij f x]
    ring
  · simp only [sourceOriginalHoeffdingMode434, if_pos hi, if_neg hj]
    exact (source_original_big_average_diff_commute434
      mu j i hij.symm f x).symm
  · simp only [sourceOriginalHoeffdingMode434, if_neg hi, if_pos hj]
    exact source_original_big_average_diff_commute434
      mu i j hij f x
  · simp only [sourceOriginalHoeffdingMode434, if_neg hi, if_neg hj]
    exact source_original_coordinate_means_commute434 mu i j hij f x
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingListPermutation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The ACTUAL true source BIG multicoordinate Hoeffding mode
depends only on the processed coordinate set, not on the order
of the independent source prime resamplings; proven directly
from commutation of literal one-prime E_i and I-E_i. -/
theorem source_original_hoeffding_list_perm434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    {L K : List (Fin M)} (hperm : L.Perm K)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu S L f =
    sourceOriginalHoeffdingList434 mu S K f := by
  induction hperm generalizing f with
  | nil => rfl
  | @cons i L K h ih =>
    change sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i f) =
      sourceOriginalHoeffdingList434 mu S K
      (sourceOriginalHoeffdingMode434 mu S i f)
    exact ih _
  | @swap i j L =>
    change sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i
        (sourceOriginalHoeffdingMode434 mu S j f)) =
      sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S j
        (sourceOriginalHoeffdingMode434 mu S i f))
    by_cases hij : i = j
    · subst j
      rfl
    · have hmode : sourceOriginalHoeffdingMode434 mu S i
        (sourceOriginalHoeffdingMode434 mu S j f) =
        sourceOriginalHoeffdingMode434 mu S j
        (sourceOriginalHoeffdingMode434 mu S i f) := by
        funext x
        exact source_original_hoeffding_modes_commute434
          mu S i j hij f x
      rw [hmode]
  | @trans L K N h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ f).trans (ih₂ f)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingRelabel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original BIG coordinate-set relabeling by an independent
sampled endpoint permutation, retaining the true slot indices. -/
def sourceOriginalBigRelabelSlots434
    {M : ℕ} (σ : Equiv.Perm (Fin M))
    (S : Finset (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun j => σ j ∈ S)

theorem source_original_big_relabel_slots_mem434
    {M : ℕ} (σ : Equiv.Perm (Fin M))
    (S : Finset (Fin M)) (i : Fin M) :
    σ.symm i ∈ sourceOriginalBigRelabelSlots434 σ S ↔ i ∈ S := by
  simp [sourceOriginalBigRelabelSlots434]

/-- SOURCE covariance of the true one-slot centered/averaged
Hoeffding operator under independent BIG label permutations. -/
theorem source_original_hoeffding_mode_relabel434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (S : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (i : Fin M) (f : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalHoeffdingMode434 mu S i
       (fun y => f (fun j => y (σ j))) x =
    sourceOriginalHoeffdingMode434 mu
       (sourceOriginalBigRelabelSlots434 σ S)
       (σ.symm i) f (fun j => x (σ j)) := by
  have hmem := source_original_big_relabel_slots_mem434 σ S i
  have hE := source_original_big_coordinate_permutation_covariant434
      mu σ i f x
  by_cases hi : i ∈ S
  · have ht : σ.symm i ∈ sourceOriginalBigRelabelSlots434 σ S :=
      hmem.mpr hi
    simp only [sourceOriginalHoeffdingMode434,
      if_pos hi, if_pos ht, sourceOriginalBigCoordinateDiff434]
    rw [hE]
  · have ht : σ.symm i ∉ sourceOriginalBigRelabelSlots434 σ S :=
      fun h => hi (hmem.mp h)
    simpa only [sourceOriginalHoeffdingMode434,
      if_neg hi, if_neg ht] using hE

/-- Covariance of the ACTUAL entire finite ordered Hoeffding
projection under simultaneous permutation of its original
BIG slots and centered-coordinate subset. -/
theorem source_original_hoeffding_list_relabel434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (S : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (L : List (Fin M)) (f : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalHoeffdingList434 mu S L
      (fun y => f (fun j => y (σ j))) x =
    sourceOriginalHoeffdingList434 mu
      (sourceOriginalBigRelabelSlots434 σ S)
      (L.map σ.symm) f (fun j => x (σ j)) := by
  induction L generalizing f with
  | nil => rfl
  | cons i L ih =>
    change sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i
        (fun y => f (fun j => y (σ j)))) x =
      sourceOriginalHoeffdingList434 mu
        (sourceOriginalBigRelabelSlots434 σ S)
        (L.map σ.symm)
        (sourceOriginalHoeffdingMode434 mu
          (sourceOriginalBigRelabelSlots434 σ S)
          (σ.symm i) f) (fun j => x (σ j))
    have hmode : sourceOriginalHoeffdingMode434 mu S i
        (fun y => f (fun j => y (σ j))) =
        (fun y => sourceOriginalHoeffdingMode434 mu
          (sourceOriginalBigRelabelSlots434 σ S)
          (σ.symm i) f (fun j => y (σ j))) := by
      funext y
      exact source_original_hoeffding_mode_relabel434
        mu S σ i f y
    rw [hmode]
    exact ih _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingOrbitEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- The true source BIG slot permutation is a bijection of
the full list of labelled BIG coordinates, including the
canonical source enumeration of ALL physical slots.
No coordinate is dropped, counted twice or independently
randomly resampled. -/
theorem source_original_big_univ_list_perm434
    {M : ℕ} (σ : Equiv.Perm (Fin M)) :
    ((Finset.univ : Finset (Fin M)).toList.map σ.symm).Perm
      (Finset.univ : Finset (Fin M)).toList := by
  classical
  let L : List (Fin M) := (Finset.univ : Finset (Fin M)).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hmap : (L.map σ.symm).Nodup := by
    apply (List.nodup_map_iff_inj_on hL).2
    intro a ha b hb heq
    exact σ.symm.injective heq
  have hset : (L.map σ.symm).toFinset = L.toFinset := by
    ext j
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · intro hj
      exact Finset.mem_toList.mpr (Finset.mem_univ j)
    · intro hj
      exact ⟨σ j, Finset.mem_toList.mpr (Finset.mem_univ _),
        σ.symm_apply_apply j⟩
  have hp := (List.toFinset_eq_iff_perm_dedup).mp hset
  simpa only [List.Nodup.dedup hmap, List.Nodup.dedup hL] using hp

/-- ACTUAL finite BIG Hoeffding component covariance for
the FULL physical slot family. The original iid reciprocal
prime mass, all numerical prime multiplicities, and arbitrary
nonseparable complex source tests are retained. -/
theorem source_original_big_full_hoeffding_relabel434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (S : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalHoeffdingList434 mu S
      (Finset.univ : Finset (Fin M)).toList
      (fun y => f (fun j => y (σ j))) x =
    sourceOriginalHoeffdingList434 mu
      (sourceOriginalBigRelabelSlots434 σ S)
      (Finset.univ : Finset (Fin M)).toList
      f (fun j => x (σ j)) := by
  rw [source_original_hoeffding_list_relabel434]
  have hp := source_original_big_univ_list_perm434 σ
  exact congrFun (source_original_hoeffding_list_perm434
    mu (sourceOriginalBigRelabelSlots434 σ S) hp f) _

/-- An original FULLY symmetric BIG tuple observable has
exactly equal physical weighted L² energies in its
Hoeffding component S and the permuted subset σ^{-1}(S).
This supplies the missing true orbit-symmetry bridge to
C31 degree-cardinal energy counting. -/
theorem source_original_big_symmetric_hoeffding_orbit_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (S : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (f : (Fin M → P) → ℂ)
    (hf : ∀ x : Fin M → P, f (fun j => x (σ j)) = f x) :
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) S
        (Finset.univ : Finset (Fin M)).toList f) =
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ))
        (sourceOriginalBigRelabelSlots434 σ S)
        (Finset.univ : Finset (Fin M)).toList f) := by
  let T := sourceOriginalBigRelabelSlots434 σ S
  have hcov (x : Fin M → P) :
      sourceOriginalHoeffdingList434 (fun p => (mu p:ℂ)) S
         (Finset.univ : Finset (Fin M)).toList f x =
      sourceOriginalHoeffdingList434 (fun p => (mu p:ℂ))
         T (Finset.univ : Finset (Fin M)).toList
         f (fun j => x (σ j)) := by
    have h := source_original_big_full_hoeffding_relabel434
      (fun p => (mu p:ℂ)) S σ f x
    have heq : (fun y : Fin M → P => f (fun j => y (σ j))) = f := by
      funext y
      exact hf y
    rw [heq] at h
    exact h
  calc
    _ = sourceOriginalBigActualEnergy434 mu
      (fun x => sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) T
        (Finset.univ : Finset (Fin M)).toList f
        (fun j => x (σ j))) := by
      unfold sourceOriginalBigActualEnergy434
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcov x]
    _ = _ := source_original_big_actual_energy_permutation434
      mu σ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingCardinalOrbit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Every two same-cardinality sets of the ORIGINAL BIG
indexed prime slots differ by a genuine permutation.
The permutation is constructed from an equivalence of the
actual marked subtypes, not assumed as an orbit axiom. -/
theorem source_original_big_subset_cardinal_permutation434
    {M : ℕ} (S T : Finset (Fin M)) (hcard : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin M),
       sourceOriginalBigRelabelSlots434 σ S = T := by
  classical
  let e : ↥T ≃ ↥S := Finset.equivOfCardEq hcard.symm
  let σ : Equiv.Perm (Fin M) := Equiv.extendSubtype e
  refine ⟨σ, ?_⟩
  ext j
  simp only [sourceOriginalBigRelabelSlots434, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    exact (Equiv.extendSubtype_not_mem e j hn) h
  · intro h
    exact Equiv.extendSubtype_mem e j h

/-- ORIGINAL BIG harmonic-probability symmetric test: the
ACTUAL weighted L2 Hoeffding components of equal cardinality
have IDENTICAL energies. This is exactly the orbit equality
missing from the source03 J-uniform all-probe survivor bound.
Neither the Hoeffding degree-energy model nor permutation
exchangeability is assumed: both are consequences of the
physical reciprocal-prime product law in C32–C33. -/
theorem source_original_big_symmetric_same_cardinal_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (S T : Finset (Fin M)) (hcard : S.card = T.card)
    (f : (Fin M → P) → ℂ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin M))
       (x : Fin M → P),
       f (fun j => x (σ j)) = f x) :
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) S
        (Finset.univ : Finset (Fin M)).toList f) =
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) T
        (Finset.univ : Finset (Fin M)).toList f) := by
  obtain ⟨σ,hσ⟩ :=
    source_original_big_subset_cardinal_permutation434 S T hcard
  have he := source_original_big_symmetric_hoeffding_orbit_energy434
    mu S σ f (hsymm σ)
  simpa only [hσ] using he
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingDegreeOrbit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The exact ACTUAL weighted BIG harmonic total energy on
the full degree-j Hoeffding orbit is choose(M,j) times
the energy of any representative source BIG subset S with
|S|=j. This is the missing non-abstract source degree
energy multiplicity, proved from TRUE coordinate permutation
covariance (not merely assumed exchangeability). -/
theorem source_original_hoeffding_orbit_cardinal_mass434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (S : Finset (Fin M))
    (f : (Fin M → P) → ℂ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin M)) (x : Fin M → P),
       f (fun j => x (σ j)) = f x) :
    (∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard S.card,
       sourceOriginalBigActualEnergy434 mu
         (sourceOriginalHoeffdingList434
          (fun p => (mu p:ℂ)) T
          (Finset.univ : Finset (Fin M)).toList f)) =
    (M.choose S.card : ℝ) *
       sourceOriginalBigActualEnergy434 mu
         (sourceOriginalHoeffdingList434
          (fun p => (mu p:ℂ)) S
          (Finset.univ : Finset (Fin M)).toList f) := by
  let E : Finset (Fin M) → ℝ := fun T =>
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) T
        (Finset.univ : Finset (Fin M)).toList f)
  have heq (T : Finset (Fin M))
      (hT : T ∈ (Finset.univ : Finset (Fin M)).powersetCard S.card) :
      E T = E S := by
    have hcard : T.card = S.card :=
      (Finset.mem_powersetCard.mp hT).2
    exact source_original_big_symmetric_same_cardinal_energy434
      mu T S hcard f hsymm
  calc
    _ = ∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard S.card,
          E S := by
         apply Finset.sum_congr rfl
         intro T hT
         exact heq T hT
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingSurvivorCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11500000

/-- Actual source BIG Efron-Stein survivor subsets at
degree j: every prescribed PROBE slot belongs to S,
and all excluded trailing slots are absent.
The definition is on TRUE labelled physical coordinates. -/
def sourceOriginalHoeffdingSurvivorSets434
    {M : ℕ} (probes trailing : Finset (Fin M)) (j : ℕ) :
    Finset (Finset (Fin M)) :=
  ((Finset.univ : Finset (Fin M)).powersetCard j).filter
    (fun S => probes ⊆ S ∧ Disjoint S trailing)

/-- The REAL number of physical j-subsets containing all
probe slots and no trailing slots is at most
choose(M-m-ell,j-m), with genuine disjoint marked sets
and NO lower bound on j. No invented uniform component
degrees or replacement with asymptotic entropy counts. -/
theorem source_original_hoeffding_survivor_count_le434
    {M : ℕ} (probes trailing : Finset (Fin M)) (j : ℕ)
    (hdisj : Disjoint probes trailing) :
    (sourceOriginalHoeffdingSurvivorSets434
      probes trailing j).card ≤
    (M-(probes.card+trailing.card)).choose (j-probes.card) := by
  classical
  let W : Finset (Fin M) :=
    (Finset.univ : Finset (Fin M)) \ (probes ∪ trailing)
  let F := sourceOriginalHoeffdingSurvivorSets434
    probes trailing j
  have hcardW : W.card = M-(probes.card+trailing.card) := by
    dsimp [W]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisj]
  have hmap : Set.MapsTo (fun S : Finset (Fin M) => S \ probes)
        (F : Set (Finset (Fin M)))
        ((W.powersetCard (j-probes.card)) : Set (Finset (Fin M))) := by
    intro S hS
    have hs := Finset.mem_filter.mp hS
    have hdeg := Finset.mem_powersetCard.mp hs.1
    obtain ⟨hProbe,hTrailing⟩ := hs.2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro i hi
      have his := (Finset.mem_sdiff.mp hi).1
      have hnp := (Finset.mem_sdiff.mp hi).2
      have hnt : i ∉ trailing := by
        intro hit
        exact (Finset.disjoint_left.mp hTrailing) his hit
      simp only [W, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun h => (Finset.mem_union.mp h).elim hnp hnt
    · rw [Finset.card_sdiff_of_subset hProbe, hdeg.2]
  have hinj : Set.InjOn (fun S : Finset (Fin M) => S \ probes)
       (F : Set (Finset (Fin M))) := by
    intro S hS T hT hEq
    have hs := (Finset.mem_filter.mp hS).2.1
    have ht := (Finset.mem_filter.mp hT).2.1
    have hu := Finset.sdiff_union_of_subset hs
    have hv := Finset.sdiff_union_of_subset ht
    change S \ probes = T \ probes at hEq
    calc
      S = (S \ probes) ∪ probes := hu.symm
      _ = (T \ probes) ∪ probes := by rw [hEq]
      _ = T := hv
  have hcard := Finset.card_le_card_of_injOn _ hmap hinj
  rw [Finset.card_powersetCard, hcardW] at hcard
  simpa only [F] using hcard
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingPhysicalSurvivor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Actual source BIG probe/last-ell symmetry: for any
disjoint sets of truly marked slots, the number of
Hoeffding j-components containing every probe but no
excluded trailing slot, times choose(m+ell,m), is bounded
by the total number of j-components.
The proof uses a REAL injection of survivor subsets,
not a probabilistic counting hypothesis. -/
theorem source_original_hoeffding_survivor_sharp_card434
    {M : ℕ} (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing) (j : ℕ) :
    (sourceOriginalHoeffdingSurvivorSets434
       probes trailing j).card *
      (probes.card+trailing.card).choose probes.card ≤
      M.choose j := by
  have hM : probes.card+trailing.card ≤ M := by
    have hc := Finset.card_le_card
      (Finset.subset_univ (probes ∪ trailing))
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  by_cases hmj : probes.card ≤ j
  · have hc := source_original_hoeffding_survivor_count_le434
      probes trailing j hdisj
    have hp := Nat.mul_le_mul_right
      ((probes.card+trailing.card).choose probes.card) hc
    have hv := source_original_hoeffding_vandermonde_sharp434
      M probes.card trailing.card j hM hmj
    nlinarith [hp,hv]
  · have hnone : sourceOriginalHoeffdingSurvivorSets434
        probes trailing j = ∅ := by
      by_contra hne
      have hNE := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨S,hs⟩ := hNE
      have hmem := Finset.mem_filter.mp hs
      have hp := hmem.2.1
      have hd := (Finset.mem_powersetCard.mp hmem.1).2
      have hc := Finset.card_le_card hp
      omega
    simp [hnone]

/-- Strong genuine finite-weighted L² energy suppression for
a single original source BIG symmetric group at fixed
Hoeffding degree j, now proved WITHOUT an abstract degree
energy model. Full normalized source reciprocal-prime masses
are the only measure assumption, and f can be nonseparable. -/
theorem source_original_hoeffding_physical_survivor_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (hmu : ∀ p, 0 ≤ mu p)
    (f : (Fin M → P) → ℂ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin M)) (x : Fin M → P),
       f (fun j => x (σ j)) = f x)
    (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing) (j : ℕ) :
    (∑ S ∈ sourceOriginalHoeffdingSurvivorSets434
      probes trailing j,
      sourceOriginalBigActualEnergy434 mu
        (sourceOriginalHoeffdingList434 (fun p => (mu p:ℂ))
          S (Finset.univ : Finset (Fin M)).toList f)) *
       (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
    (∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
      sourceOriginalBigActualEnergy434 mu
        (sourceOriginalHoeffdingList434 (fun p => (mu p:ℂ))
          S (Finset.univ : Finset (Fin M)).toList f)) := by
  classical
  let F := sourceOriginalHoeffdingSurvivorSets434
    probes trailing j
  let H : Finset (Fin M) → ℝ := fun S =>
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434 (fun p => (mu p:ℂ))
        S (Finset.univ : Finset (Fin M)).toList f)
  have hH (S : Finset (Fin M)) : 0 ≤ H S :=
    source_original_big_actual_energy_nonneg434 mu hmu _
  by_cases hF : F.Nonempty
  · obtain ⟨S,hS⟩ := hF
    have hSin : S ∈ (Finset.univ : Finset (Fin M)).powersetCard j :=
      (Finset.mem_filter.mp hS).1
    have hSj : S.card = j := (Finset.mem_powersetCard.mp hSin).2
    have hOrbit := source_original_hoeffding_orbit_cardinal_mass434
      mu S f hsymm
    rw [hSj] at hOrbit
    have hFsum : (∑ T ∈ F, H T) = (F.card:ℝ)*H S := by
      calc
        _ = ∑ T ∈ F, H S := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTj := (Finset.mem_powersetCard.mp
            (Finset.mem_filter.mp hT).1).2
          exact source_original_big_symmetric_same_cardinal_energy434
            mu T S (hTj.trans hSj.symm) f hsymm
        _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]
    have hcnt := source_original_hoeffding_survivor_sharp_card434
      probes trailing hdisj j
    have hreal :
        (F.card:ℝ) *
          (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
         (M.choose j:ℝ) := by
      exact_mod_cast hcnt
    have hmul := mul_le_mul_of_nonneg_right hreal (hH S)
    change (∑ T ∈ F, H T) *
      (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
      (∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
         H T)
    rw [hFsum,hOrbit]
    nlinarith [hmul]
  · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (∑ T ∈ F, H T) *
      (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
      (∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
         H T)
    simp only [hEmpty, Finset.sum_empty, zero_mul]
    apply Finset.sum_nonneg
    intro S hS
    exact hH S
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingPhysicalAllDegree -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- REAL source BIG survivor energy in all Hoeffding degrees:
the original designated probe slots are centered and the
excluded trailing labels are averaged. The sum uses the
literal true physical weighted L2 energies of H_S f and
does not introduce abstract E(j) degree-energy factors. -/
noncomputable def sourceOriginalPhysicalFullProbeEnergy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (probes trailing : Finset (Fin M))
    (f : (Fin M → P) → ℂ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin M)).powerset.filter
       (fun S => probes ⊆ S ∧ Disjoint S trailing),
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) S
        (Finset.univ : Finset (Fin M)).toList f)

/-- Source TRUE one-group full-probe Hoeffding survivor estimate
in the ACTUAL L2 harmonic BIG product measure for an arbitrary
PERMUTATION-INVARIANT global complex test f:
  choose(m+ell,m) * survivor energy <= full physical L2 energy.
This has no extra LARGE-J condition and does not require f to
factor across the individual prime coordinates. The ONLY
symmetry assumed is the actual permutation symmetry needed
for the original symmetrized ideal kernel. -/
theorem source_original_hoeffding_physical_all_degree_saving434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p)
    (hnorm : (∑ p : P, mu p) = 1)
    (f : (Fin M → P) → ℂ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin M)) (x : Fin M → P),
       f (fun j => x (σ j)) = f x)
    (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing) :
    sourceOriginalPhysicalFullProbeEnergy434 mu probes trailing f *
      (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
    sourceOriginalBigActualEnergy434 mu f := by
  let C : ℝ :=
    (((probes.card+trailing.card).choose probes.card:ℕ):ℝ)
  let H : Finset (Fin M) → ℝ := fun S =>
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingList434
        (fun p => (mu p:ℂ)) S
        (Finset.univ : Finset (Fin M)).toList f)
  have hdeg (j : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
       if probes ⊆ S ∧ Disjoint S trailing then H S else 0) * C ≤
    (∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard j, H S) := by
    rw [← Finset.sum_filter]
    exact source_original_hoeffding_physical_survivor_energy434
      mu hmu f hsymm probes trailing hdisj j
  have hgroup :
    (∑ j ∈ Finset.range (M+1),
       ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
          if probes ⊆ S ∧ Disjoint S trailing then H S else 0) * C ≤
    (∑ j ∈ Finset.range (M+1),
       ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
          H S) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact hdeg j
  have hSurv :
    sourceOriginalPhysicalFullProbeEnergy434 mu probes trailing f =
      ∑ S ∈ (Finset.univ : Finset (Fin M)).powerset,
        if probes ⊆ S ∧ Disjoint S trailing then H S else 0 := by
    dsimp only [sourceOriginalPhysicalFullProbeEnergy434]
    rw [Finset.sum_filter]
  have hAll :
    (∑ S ∈ (Finset.univ : Finset (Fin M)).powerset,
         H S) = sourceOriginalBigActualEnergy434 mu f := by
    have hh := source_original_big_actual_hoeffding_parseval434
      mu hnorm
      (Finset.univ : Finset (Fin M)).toList
      (Finset.nodup_toList _) f
    simpa only [Finset.toList_toFinset,H] using hh.symm
  rw [Finset.sum_powerset] at hSurv hAll
  simp only [Finset.card_univ, Fintype.card_fin] at hSurv hAll
  rw [← hSurv, hAll] at hgroup
  exact hgroup
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigSymmetrize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original iid BIG prime slot permutation symmetrizer,
with precisely uniform weight over all permutations of
the independently labelled active prime slots. Repeated
numerical prime values are preserved, not prohibited.
This is the canonical permutation averaging used in the
source03 symmetrized ideal-kernel comparison. -/
noncomputable def sourceOriginalBigSymmetrize434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (f : (Fin M → P) → ℂ)
    (x : Fin M → P) : ℂ :=
  ((Fintype.card (Equiv.Perm (Fin M)):ℂ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin M),
       f (fun j => x (σ j))

/-- A true permutation-averaged BIG test is invariant under
ALL source BIG coordinate permutations. No statistical
exchangeability of f is assumed: this is a literal finite
group-averaging identity. Thus it qualifies for the
ACTUAL source C33 Hoeffding full-probe energy theorem. -/
theorem source_original_big_symmetrize_invariant434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (f : (Fin M → P) → ℂ)
    (τ : Equiv.Perm (Fin M)) (x : Fin M → P) :
    sourceOriginalBigSymmetrize434 f (fun j => x (τ j)) =
    sourceOriginalBigSymmetrize434 f x := by
  unfold sourceOriginalBigSymmetrize434
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin M),
      f (fun j => x (τ (σ j)))) =
      ∑ σ : Equiv.Perm (Fin M),
        f (fun j => x ((τ*σ) j)) := by
          apply Finset.sum_congr rfl
          intro σ _
          simp only [Equiv.Perm.mul_apply]
    _ = _ := by
      exact Fintype.sum_equiv (Equiv.mulLeft τ)
        (fun σ : Equiv.Perm (Fin M) =>
          f (fun j => x ((τ*σ) j)))
        (fun ρ : Equiv.Perm (Fin M) =>
          f (fun j => x (ρ j)))
        (by intro σ; rfl)

/-- The original TRUE BIG symmetrized test satisfies the
one-group sharp Hoeffding physical survivor saving for
arbitrary unsymmetric initial complex source f, with
no direct symmetry hypothesis. The only premise is genuine
BIG source harmonic nonnegativity and normalization. -/
theorem source_original_symmetrized_big_full_probe_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p)
    (hnorm : (∑ p : P, mu p) = 1)
    (f : (Fin M → P) → ℂ)
    (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing) :
    sourceOriginalPhysicalFullProbeEnergy434 mu
      probes trailing (sourceOriginalBigSymmetrize434 f) *
      (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalBigSymmetrize434 f) := by
  exact source_original_hoeffding_physical_all_degree_saving434
    mu hmu hnorm (sourceOriginalBigSymmetrize434 f)
      (source_original_big_symmetrize_invariant434 f)
        probes trailing hdisj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHarmonicSymmetrizedSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- TRUE SOURCE03 BIG-prime harmonic probability
mu(p)=(1/p)/V for the FINITE labelled prime support.
The actual permutation symmetrizer obeys the SHARP
full-probe BIG survivor physical L2 bound; no abstract
group-degree energy or SW prime-character estimate is
postulated. The REAL BIG prime labels may repeat across
distinct indexed source slots. -/
theorem source_original_harmonic_symmetrized_full_probe434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ)
    (V : ℝ) (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ))
    (f : (Fin M → P) → ℂ)
    (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing) :
    sourceOriginalPhysicalFullProbeEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V)
      probes trailing (sourceOriginalBigSymmetrize434 f) *
      (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V)
      (sourceOriginalBigSymmetrize434 f) := by
  exact source_original_symmetrized_big_full_probe_energy434
    (sourceOriginalHarmonicPrimeMu434 prime V)
    (source_original_harmonic_prime_nonneg434 prime V hV)
    (source_original_harmonic_prime_normalized434 prime V hV hEq)
    f probes trailing hdisj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Literal original BIG source x=(x_g)_g with a genuinely
different prime support for each group g; same J+ell slots. -/
abbrev SourceOriginalJointBigState434
    {G : Type} (BP : G → Type) (M : ℕ) :=
  (g : G) → Fin M → BP g

/-- Original REAL product mass over independent BIG groups,
including the actual independent indexed slot masses within
each group. NO independence of the complex test f is assumed. -/
noncomputable def sourceOriginalJointBigMass434
    {G : Type} [Fintype G]
    (BP : G → Type) {M : ℕ}
    (mu : (g : G) → BP g → ℝ)
    (x : SourceOriginalJointBigState434 BP M) : ℝ :=
  ∏ g : G, sourceOriginalRealBigProductMass434 (mu g) (x g)

/-- The ACTUAL joint BIG-group real weighted squared L2
energy; for f, arbitrary correlations among ALL prime
groups and all slots are permitted. -/
noncomputable def sourceOriginalJointBigEnergy434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (f : SourceOriginalJointBigState434 BP M → ℂ) : ℝ :=
  ∑ x : SourceOriginalJointBigState434 BP M,
    sourceOriginalJointBigMass434 BP mu x * Complex.normSq (f x)

/-- The true source BIG group-g conditional fibre has all
OTHER groups held fixed, with all of their original labelled
prime configurations and weights unchanged. -/
noncomputable def sourceOriginalJointGroupSplit434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (M : ℕ) (g : G) :
    SourceOriginalJointBigState434 BP M ≃
      ((Fin M → BP g) ×
       ((h : {h : G // h ≠ g}) → Fin M → BP h.val)) :=
  Equiv.piSplitAt g (fun h => Fin M → BP h)

noncomputable def sourceOriginalJointRestMass434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (mu : (g : G) → BP g → ℝ) (g : G)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val) : ℝ :=
  ∏ h : {h : G // h ≠ g},
    sourceOriginalRealBigProductMass434 (mu h.val) (rest h)

/-- EXACT source BIG product-mass Fubini disintegration
for one physical group g and the other dependent groups.
No replacement prime space, no tensor condition on f. -/
theorem source_original_joint_big_mass_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (mu : (g : G) → BP g → ℝ) (g : G)
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointBigMass434 BP mu x =
      sourceOriginalRealBigProductMass434 (mu g) (x g) *
      sourceOriginalJointRestMass434 BP mu g
        (fun h => x h.val) := by
  let w : G → ℝ := fun h =>
    sourceOriginalRealBigProductMass434 (mu h) (x h)
  unfold sourceOriginalJointBigMass434
    sourceOriginalJointRestMass434
  change (∏ h : G, w h) = w g * ∏ h : {h : G // h ≠ g}, w h.val
  calc
    _ = w g * (∏ h ∈ (Finset.univ : Finset G).erase g, w h) :=
      (Finset.mul_prod_erase (Finset.univ : Finset G)
        w (Finset.mem_univ g)).symm
    _ = _ := by
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase g)
        (by intro h; simp) w
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact source BIG conditional observable at group g after
freezing ALL other genuine BIG group prime labels, including
their full correlations in the original f. -/
noncomputable def sourceOriginalJointBigConditionalTest434
    {G : Type} [DecidableEq G] (BP : G → Type)
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val) :
    (Fin M → BP g) → ℂ :=
  fun u => f ((sourceOriginalJointGroupSplit434 BP M g).symm
    (u,rest))

/-- REAL SOURCE BIG FUBINI: the exact jointly weighted L²
norm over all groups is the average of exact one-group
weighted L² norms of conditional FULL complex tests
f_(rest)(u), with all other source group prime labels
and original dependent prime supports preserved.
No tensor factorization of f across BIG groups, nor
same prime support between different groups, is assumed. -/
theorem source_original_joint_big_energy_conditional_fubini434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ) (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP mu f =
    ∑ rest :
       ((h : {h : G // h ≠ g}) → Fin M → BP h.val),
      sourceOriginalJointRestMass434 BP mu g rest *
      sourceOriginalBigActualEnergy434 (mu g)
       (sourceOriginalJointBigConditionalTest434 BP g f rest) := by
  let e := sourceOriginalJointGroupSplit434 BP M g
  have hmass (u : Fin M → BP g)
      (r : (h : {h : G // h ≠ g}) → Fin M → BP h.val) :
      sourceOriginalJointBigMass434 BP mu (e.symm (u,r)) =
      sourceOriginalRealBigProductMass434 (mu g) u *
      sourceOriginalJointRestMass434 BP mu g r := by
    rw [source_original_joint_big_mass_split434
      BP mu g (e.symm (u,r))]
    have he : e (e.symm (u,r)) = (u,r) := e.apply_symm_apply _
    have hfirst : (e.symm (u,r)) g = u := by
      exact congrArg Prod.fst he
    have hrest :
       (fun h : {h : G // h ≠ g} => (e.symm (u,r)) h.val) = r := by
      exact congrArg Prod.snd he
    rw [hfirst,hrest]
  unfold sourceOriginalJointBigEnergy434
  calc
    _ = ∑ t : (Fin M → BP g) ×
        ((h : {h : G // h ≠ g}) → Fin M → BP h.val),
      sourceOriginalJointBigMass434 BP mu (e.symm t) *
         Complex.normSq (f (e.symm t)) := by
          exact Fintype.sum_equiv e
            (fun x : SourceOriginalJointBigState434 BP M =>
              sourceOriginalJointBigMass434 BP mu x *
                Complex.normSq (f x))
            (fun t => sourceOriginalJointBigMass434 BP mu
                (e.symm t) * Complex.normSq (f (e.symm t)))
            (by intro x; simp)
    _ = ∑ u : Fin M → BP g,
        ∑ r : (h : {h : G // h ≠ g}) → Fin M → BP h.val,
          (sourceOriginalRealBigProductMass434 (mu g) u *
            sourceOriginalJointRestMass434 BP mu g r) *
          Complex.normSq (f (e.symm (u,r))) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro r _
          rw [hmass u r]
    _ = ∑ r : (h : {h : G // h ≠ g}) → Fin M → BP h.val,
        sourceOriginalJointRestMass434 BP mu g r *
          sourceOriginalBigActualEnergy434 (mu g)
             (sourceOriginalJointBigConditionalTest434 BP g f r) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          unfold sourceOriginalBigActualEnergy434
            sourceOriginalJointBigConditionalTest434
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          change (sourceOriginalRealBigProductMass434 (mu g) u *
             sourceOriginalJointRestMass434 BP mu g r) *
               Complex.normSq (f (e.symm (u,r))) =
            sourceOriginalJointRestMass434 BP mu g r *
            (sourceOriginalRealBigProductMass434 (mu g) u *
               Complex.normSq (f (e.symm (u,r))))
          ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingSelectedEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Actual BIG finite simultaneous surviving Hoeffding projector
on ANY designated set A of original coordinate subsets,
without pretending the complex observable f is separable. -/
noncomputable def sourceOriginalHoeffdingSelected434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (A : Finset (Finset (Fin M)))
    (f : (Fin M → P) → ℂ) : (Fin M → P) → ℂ :=
  fun x => ∑ S ∈ A,
    sourceOriginalHoeffdingList434 mu S
      (Finset.univ : Finset (Fin M)).toList f x

/-- For a genuine NORMALIZED source BIG prime law,
ANY distinct actual Hoeffding subset components remain
orthogonal; the full squared L² norm of an arbitrary
finite selected sum equals the sum of ACTUAL squared norms.
This is a physically correct orthogonal projection, not a
degree-energy model or independent-coordinate test restriction. -/
theorem source_original_hoeffding_selected_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (A : Finset (Finset (Fin M)))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalHoeffdingSelected434
        (fun p => (mu p:ℂ)) A f) =
    ∑ S ∈ A,
      sourceOriginalBigActualEnergy434 mu
        (sourceOriginalHoeffdingList434
          (fun p => (mu p:ℂ)) S
          (Finset.univ : Finset (Fin M)).toList f) := by
  let L := (Finset.univ : Finset (Fin M)).toList
  let H : Finset (Fin M) → (Fin M → P) → ℂ :=
    fun S => sourceOriginalHoeffdingList434
      (fun p => (mu p:ℂ)) S L f
  have hsub (S : Finset (Fin M)) : S ⊆ L.toFinset := by
    simp [L]
  have hor (S T : Finset (Fin M)) (hst : S ≠ T) :
      sourceOriginalBigWeightedPairing434 mu (H S) (H T) = 0 :=
    source_original_hoeffding_distinct_orthogonal434
      mu hmu S T L (Finset.nodup_toList _) (hsub S)
        (hsub T) hst f f
  have hpair :
      sourceOriginalBigWeightedPairing434 mu
        (fun x => ∑ S ∈ A, H S x)
        (fun x => ∑ T ∈ A, H T x) =
      ∑ S ∈ A, sourceOriginalBigWeightedPairing434 mu
        (H S) (H S) := by
    rw [source_original_big_pairing_double_sum434]
    apply Finset.sum_congr rfl
    intro S hS
    rw [← Finset.add_sum_erase A
      (fun T => sourceOriginalBigWeightedPairing434 mu
         (H S) (H T)) hS]
    have hzero : (∑ T ∈ A.erase S,
       sourceOriginalBigWeightedPairing434 mu (H S) (H T)) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      exact hor S T (Ne.symm (Finset.ne_of_mem_erase hT))
    rw [hzero]
    simp
  change sourceOriginalBigActualEnergy434 mu
    (fun x => ∑ S ∈ A, H S x) = _
  have hh := source_original_big_pairing_is_actual_energy434
    mu (fun x => ∑ S ∈ A, H S x)
  rw [hh] at hpair
  simp_rw [source_original_big_pairing_is_actual_energy434] at hpair
  exact_mod_cast hpair
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigProbeEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- The REAL physical joint source BIG survivor energy
on one designated group, with ALL other groups integrated
under their TRUE, possibly group-dependent reciprocal-prime
laws. The complex observable is allowed arbitrary correlations
across the entire family of source BIG groups. -/
noncomputable def sourceOriginalJointGroupSurvivorEnergy434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (g : G) (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ) : ℝ :=
  ∑ rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val,
    sourceOriginalJointRestMass434 BP mu g rest *
    sourceOriginalPhysicalFullProbeEnergy434
      (mu g) probes trailing
      (sourceOriginalJointBigConditionalTest434 BP g f rest)

/-- The actual reciprocal-prime product-mass distribution
of all other physical BIG groups is nonnegative; no
uniform or common label space assumption is introduced. -/
theorem source_original_joint_rest_mass_nonneg434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p) (g : G)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val) :
    0 ≤ sourceOriginalJointRestMass434 BP mu g rest := by
  unfold sourceOriginalJointRestMass434
  apply Finset.prod_nonneg
  intro h _
  unfold sourceOriginalRealBigProductMass434
  apply Finset.prod_nonneg
  intro i _
  exact hmu h.val (rest h i)

/-- ACTUAL multi-group source joint conditional BIG full-probe
energy saving with all other groups integrated under the
UNMODIFIED source harmonic product law. One group may have
arbitrary correlations with the other BIG groups in f. The
only symmetry needed is invariance of each one-group
conditional fibre under its original slot permutations.
No factorization of f across BIG groups is used. -/
theorem source_original_joint_big_group_physical_saving434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hnorm : ∀ g, (∑ p : BP g, mu g p) = 1)
    (g : G) (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ rest :
       ((h : {h : G // h ≠ g}) → Fin M → BP h.val),
       ∀ (σ : Equiv.Perm (Fin M)) (u : Fin M → BP g),
       sourceOriginalJointBigConditionalTest434 BP g f rest
         (fun j => u (σ j)) =
       sourceOriginalJointBigConditionalTest434 BP g f rest u) :
    sourceOriginalJointGroupSurvivorEnergy434
      BP mu g probes trailing f *
       (((probes.card+trailing.card).choose probes.card : ℕ):ℝ) ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  let C : ℝ :=
    (((probes.card+trailing.card).choose probes.card : ℕ):ℝ)
  have hpoint (rest :
        ((h : {h : G // h ≠ g}) → Fin M → BP h.val)) :
      sourceOriginalPhysicalFullProbeEnergy434 (mu g)
          probes trailing
          (sourceOriginalJointBigConditionalTest434 BP g f rest) * C ≤
      sourceOriginalBigActualEnergy434 (mu g)
        (sourceOriginalJointBigConditionalTest434 BP g f rest) :=
    source_original_hoeffding_physical_all_degree_saving434
      (mu g) (hmu g) (hnorm g)
      (sourceOriginalJointBigConditionalTest434 BP g f rest)
      (hsymm rest) probes trailing hdisj
  have hsum :
      ∑ rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val,
        (sourceOriginalJointRestMass434 BP mu g rest *
          sourceOriginalPhysicalFullProbeEnergy434 (mu g)
            probes trailing
            (sourceOriginalJointBigConditionalTest434 BP g f rest)) * C ≤
      ∑ rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val,
        sourceOriginalJointRestMass434 BP mu g rest *
          sourceOriginalBigActualEnergy434 (mu g)
            (sourceOriginalJointBigConditionalTest434 BP g f rest) := by
    apply Finset.sum_le_sum
    intro rest _
    have hr := mul_le_mul_of_nonneg_left
      (hpoint rest) (source_original_joint_rest_mass_nonneg434
        BP mu hmu g rest)
    nlinarith [hr]
  unfold sourceOriginalJointGroupSurvivorEnergy434
  rw [Finset.sum_mul]
  rw [source_original_joint_big_energy_conditional_fubini434]
  exact hsum
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigSymmetrize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- Physical relabeling symmetrization on ONE original BIG
group inside an entire DEPENDENT source-group family.
It is defined by actual independent group coordinate
resampling. The input f may arbitrarily couple EVERY
other original BIG group and every original BIG prime slot. -/
noncomputable def sourceOriginalJointBigGroupSymmetrize434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    SourceOriginalJointBigState434 BP M → ℂ :=
  fun x => sourceOriginalBigSymmetrize434
    (fun u => f (Function.update x g u)) (x g)

/-- Replace the selected original group's list of prime
labels while freezing all OTHER physical group labels.
This identity is exact for dependent prime support types. -/
theorem source_original_joint_big_group_update_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) {M : ℕ} (g : G)
    (u v : Fin M → BP g)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val) :
    Function.update
      ((sourceOriginalJointGroupSplit434 BP M g).symm (u,rest))
       g v =
    ((sourceOriginalJointGroupSplit434 BP M g).symm (v,rest)) := by
  let e := sourceOriginalJointGroupSplit434 BP M g
  apply e.injective
  rw [show e ((Function.update (e.symm (u,rest)) g v)) =
        (v,rest) from ?_]
  exact (e.apply_symm_apply (v,rest)).symm
  have he := e.apply_symm_apply (u,rest)
  apply Prod.ext
  · change (Function.update (e.symm (u,rest)) g v) g = v
    simp
  · funext h
    change (Function.update (e.symm (u,rest)) g v) h.val = rest h
    have hne : h.val ≠ g := h.property
    simp only [Function.update, dif_neg hne]
    exact congrFun (congrArg Prod.snd he) h

/-- EXACT conditional fibre realization of the groupwise
symmetrizer: after freezing other BIG groups, no replacement
symmetry is assumed; the source conditional complex
observable IS the literal symmetrization of its fibre. -/
theorem source_original_joint_big_symmetrize_fibre434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val)
    (u : Fin M → BP g) :
    sourceOriginalJointBigConditionalTest434 BP g
      (sourceOriginalJointBigGroupSymmetrize434 BP g f)
      rest u =
    sourceOriginalBigSymmetrize434
      (sourceOriginalJointBigConditionalTest434 BP g f rest) u := by
  let e := sourceOriginalJointGroupSplit434 BP M g
  unfold sourceOriginalJointBigConditionalTest434
    sourceOriginalJointBigGroupSymmetrize434
  change sourceOriginalBigSymmetrize434
      (fun v => f (Function.update (e.symm (u,rest)) g v))
      ((e.symm (u,rest)) g) =
    sourceOriginalBigSymmetrize434
      (fun v => f (e.symm (v,rest))) u
  have hfst : (e.symm (u,rest)) g = u := by
    exact congrArg Prod.fst (e.apply_symm_apply (u,rest))
  rw [hfst]
  congr 1
  funext v
  rw [source_original_joint_big_group_update_split434 BP g u v rest]

/-- At every FIXED configuration of the OTHER genuine BIG
groups, the selected group's physical conditional test
becomes automatically permutation invariant, even if the
unprocessed source f was fully coupled across groups. -/
theorem source_original_joint_big_symmetrize_fibre_invariant434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val)
    (σ : Equiv.Perm (Fin M)) (u : Fin M → BP g) :
    sourceOriginalJointBigConditionalTest434 BP g
      (sourceOriginalJointBigGroupSymmetrize434 BP g f)
        rest (fun j => u (σ j)) =
    sourceOriginalJointBigConditionalTest434 BP g
      (sourceOriginalJointBigGroupSymmetrize434 BP g f)
        rest u := by
  rw [source_original_joint_big_symmetrize_fibre434,
      source_original_joint_big_symmetrize_fibre434]
  exact source_original_big_symmetrize_invariant434
    (sourceOriginalJointBigConditionalTest434 BP g f rest) σ u

/-- True conditional tensor-free BIG probe suppression for a
source multi-BIG group function explicitly symmetrized
in group g. Entire OTHER-GROUP correlation stays intact.
No input symmetry assumption is needed. -/
theorem source_original_joint_symmetrized_group_physical_saving434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hnorm : ∀ g, (∑ p : BP g, mu g p) = 1)
    (g : G) (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointGroupSurvivorEnergy434 BP mu g
      probes trailing
      (sourceOriginalJointBigGroupSymmetrize434 BP g f) *
       (((probes.card+trailing.card).choose probes.card:ℕ):ℝ) ≤
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointBigGroupSymmetrize434 BP g f) := by
  exact source_original_joint_big_group_physical_saving434
    BP mu hmu hnorm g probes trailing hdisj
      (sourceOriginalJointBigGroupSymmetrize434 BP g f)
    (source_original_joint_big_symmetrize_fibre_invariant434 BP g f)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigSurvivorProjector -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- TRUE ORIGINAL source group-g surviving Hoeffding operator
on a JOINT multi-BIG-group source tuple. Its subgroup
coordinate probes are evaluated in the full arbitrary f,
with ALL other source BIG groups frozen at their actual
prime-labelled configurations. No factorization of f. -/
noncomputable def sourceOriginalJointGroupSurvivorProjector434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (g : G) (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    SourceOriginalJointBigState434 BP M → ℂ :=
  fun x =>
    sourceOriginalHoeffdingSelected434
      (fun p => (mu g p : ℂ))
      ((Finset.univ : Finset (Fin M)).powerset.filter
        (fun S => probes ⊆ S ∧ Disjoint S trailing))
      (fun u => f (Function.update x g u)) (x g)

/-- The group-g surviving Hoeffding operator on the
ACTUAL full dependent BIG tuple restricts EXACTLY to
the original one-group selected physical orthogonal
projector after conditioning on all OTHER groups.
No independent output test or extra measure is inserted. -/
theorem source_original_joint_survivor_fibre434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (g : G) (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val)
    (u : Fin M → BP g) :
    sourceOriginalJointBigConditionalTest434 BP g
      (sourceOriginalJointGroupSurvivorProjector434
         BP mu g probes trailing f) rest u =
    sourceOriginalHoeffdingSelected434
      (fun p => (mu g p : ℂ))
      ((Finset.univ : Finset (Fin M)).powerset.filter
        (fun S => probes ⊆ S ∧ Disjoint S trailing))
      (sourceOriginalJointBigConditionalTest434 BP g f rest) u := by
  let e := sourceOriginalJointGroupSplit434 BP M g
  unfold sourceOriginalJointBigConditionalTest434
    sourceOriginalJointGroupSurvivorProjector434
  change sourceOriginalHoeffdingSelected434
      (fun p => (mu g p : ℂ))
      ((Finset.univ : Finset (Fin M)).powerset.filter
        (fun S => probes ⊆ S ∧ Disjoint S trailing))
      (fun v => f (Function.update (e.symm (u,rest)) g v))
        ((e.symm (u,rest)) g) =
    sourceOriginalHoeffdingSelected434
      (fun p => (mu g p : ℂ))
      ((Finset.univ : Finset (Fin M)).powerset.filter
        (fun S => probes ⊆ S ∧ Disjoint S trailing))
      (fun v => f (e.symm (v,rest))) u
  have hfst : (e.symm (u,rest)) g = u :=
    congrArg Prod.fst (e.apply_symm_apply (u,rest))
  rw [hfst]
  congr 1
  funext v
  rw [source_original_joint_big_group_update_split434 BP g u v rest]

/-- Genuine multi-group physical L² energy of the source
survivor projector equals exactly the conditional group
survivor ENERGY, with all other group-dependent prime
masses integrated and f completely nonseparable. -/
theorem source_original_joint_survivor_energy_identity434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (hnorm : ∀ g, (∑ p : BP g, mu g p) = 1)
    (g : G) (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointGroupSurvivorProjector434
         BP mu g probes trailing f) =
    sourceOriginalJointGroupSurvivorEnergy434
      BP mu g probes trailing f := by
  rw [source_original_joint_big_energy_conditional_fubini434]
  unfold sourceOriginalJointGroupSurvivorEnergy434
  apply Finset.sum_congr rfl
  intro rest _
  have hfibre :
      sourceOriginalJointBigConditionalTest434 BP g
        (sourceOriginalJointGroupSurvivorProjector434
          BP mu g probes trailing f) rest =
      sourceOriginalHoeffdingSelected434
        (fun p => (mu g p : ℂ))
        ((Finset.univ : Finset (Fin M)).powerset.filter
          (fun S => probes ⊆ S ∧ Disjoint S trailing))
        (sourceOriginalJointBigConditionalTest434 BP g f rest) := by
    funext u
    exact source_original_joint_survivor_fibre434
      BP mu g probes trailing f rest u
  rw [hfibre]
  congr 1
  have hsel := source_original_hoeffding_selected_energy434
    (mu g) (hnorm g)
    ((Finset.univ : Finset (Fin M)).powerset.filter
      (fun S => probes ⊆ S ∧ Disjoint S trailing))
    (sourceOriginalJointBigConditionalTest434 BP g f rest)
  rw [hsel]
  rfl

/-- Source one-BIG-group physical L² operator inequality,
with TRUE dependent multi-group prime law and genuine
jointly correlated complex f:
   C_g ||Survivor_g f||²_joint <= ||f||²_joint.
It uses only actual conditional permutation symmetry
of f in group g; no factorization of f across groups. -/
theorem source_original_joint_survivor_projector_contraction434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hnorm : ∀ g, (∑ p : BP g, mu g p) = 1)
    (g : G) (probes trailing : Finset (Fin M))
    (hdisj : Disjoint probes trailing)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ rest :
       ((h : {h : G // h ≠ g}) → Fin M → BP h.val),
       ∀ (σ : Equiv.Perm (Fin M)) (u : Fin M → BP g),
       sourceOriginalJointBigConditionalTest434 BP g f rest
         (fun j => u (σ j)) =
       sourceOriginalJointBigConditionalTest434 BP g f rest u) :
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointGroupSurvivorProjector434
        BP mu g probes trailing f) *
       (((probes.card+trailing.card).choose probes.card : ℕ):ℝ) ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  rw [source_original_joint_survivor_energy_identity434
    BP mu hnorm g probes trailing f]
  exact source_original_joint_big_group_physical_saving434
    BP mu hmu hnorm g probes trailing hdisj f hsymm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigSymmetryPreserve -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- Relabel actual ORIGINAL joint BIG source prime slots
in just one designated group, leaving all other group-dependent
prime supports, marks and probability masses unchanged. -/
noncomputable def sourceOriginalJointGroupRelabel434
    {G : Type} [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (h : G) (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    SourceOriginalJointBigState434 BP M :=
  Function.update x h (fun i => x h (σ i))

/-- A simultaneous physical BIG endpoint relabel at h,
then an independently sampled update at DISTINCT group g,
coincides exactly with the opposite order. All BIG group
types may be different. This is the critical source
no-accidental-cross-group-mixing identity. -/
theorem source_original_joint_update_relabel_commute434
    {G : Type} [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (g h : G) (hgh : g ≠ h)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M)
    (u : Fin M → BP g) :
    Function.update (sourceOriginalJointGroupRelabel434 BP h σ x)
       g u =
    sourceOriginalJointGroupRelabel434 BP h σ
       (Function.update x g u) := by
  unfold sourceOriginalJointGroupRelabel434
  have hh : (Function.update x g u) h = x h := by
    simp [Function.update, Ne.symm hgh]
  rw [hh]
  exact (Function.update_comm hgh
    u (fun i => x h (σ i)) x).symm

/-- A genuine conditional source g-Hoeffding probe projector
preserves global physical slot-permutation symmetry in
EVERY DIFFERENT group h, even when f couples all BIG groups.
No factorization of the original source K_nu or ideal test. -/
theorem source_original_joint_survivor_preserves_other_symmetry434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ a, Fintype (BP a)]
    [∀ a, DecidableEq (BP a)]
    {M : ℕ} (mu : (a : G) → BP a → ℝ)
    (g h : G) (hgh : g ≠ h)
    (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin M))
       (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP h σ x) = f x)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointGroupSurvivorProjector434 BP mu g
        probes trailing f
        (sourceOriginalJointGroupRelabel434 BP h σ x) =
    sourceOriginalJointGroupSurvivorProjector434 BP mu g
        probes trailing f x := by
  unfold sourceOriginalJointGroupSurvivorProjector434
  have hgroup : (sourceOriginalJointGroupRelabel434 BP h σ x) g =
    x g := by
    unfold sourceOriginalJointGroupRelabel434
    simp [Function.update, hgh]
  rw [hgroup]
  congr 1
  funext u
  rw [source_original_joint_update_relabel_commute434
    BP g h hgh σ x u]
  exact hsym σ (Function.update x g u)

/-- Exact original group-g conditional symmetry is logically
equivalent to physical joint source invariance under group-g
coordinate relabeling. This removes the apparent extra
conditional-Hoeffding-symmetry premise in C34's contraction. -/
theorem source_original_joint_group_symmetry_to_fibres434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ a, Fintype (BP a)]
    [∀ a, DecidableEq (BP a)]
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin M))
       (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP g σ x) = f x)
    (rest : (h : {h : G // h ≠ g}) → Fin M → BP h.val)
    (σ : Equiv.Perm (Fin M))
    (u : Fin M → BP g) :
    sourceOriginalJointBigConditionalTest434 BP g f rest
      (fun j => u (σ j)) =
    sourceOriginalJointBigConditionalTest434 BP g f rest u := by
  let e := sourceOriginalJointGroupSplit434 BP M g
  change f (e.symm ((fun j => u (σ j)),rest)) = f (e.symm (u,rest))
  have heval : (e.symm (u,rest)) g = u :=
    congrArg Prod.fst (e.apply_symm_apply (u,rest))
  have hs : sourceOriginalJointGroupRelabel434 BP g σ
       (e.symm (u,rest)) = e.symm ((fun j => u (σ j)),rest) := by
    unfold sourceOriginalJointGroupRelabel434
    rw [heval]
    exact source_original_joint_big_group_update_split434
      BP g u (fun j => u (σ j)) rest
  rw [←hs]
  exact hsym σ (e.symm (u,rest))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigAllGroupPower -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14500000

/-- Apply each TRUE original source BIG-group all-probe
survivor orthogonal projector once, in the physical source
group order. All BIG prime supports and weights are indexed
by group, but the COMPLEX f can correlate all groups arbitrarily.
This is NOT a product of independent test functions. -/
noncomputable def sourceOriginalJointAllGroupSurvivor434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (probes trailing : G → Finset (Fin M)) :
    List G → (SourceOriginalJointBigState434 BP M → ℂ) →
      (SourceOriginalJointBigState434 BP M → ℂ)
  | [], f => f
  | g :: L, f =>
    sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing
      L (sourceOriginalJointGroupSurvivorProjector434
        BP mu g (probes g) (trailing g) f)

/-- Processing other physical BIG groups does not disrupt
source permutation symmetry of any UNPROCESSED group h.
Actual group-dependent marks are retained and the
orthogonal group-g projector uses the true source harmonic law. -/
theorem source_original_joint_all_survivor_symmetry_unprocessed434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (probes trailing : G → Finset (Fin M))
    (h : G) (L : List G) (hh : h ∉ L)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin M))
       (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP h σ x) = f x)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing
      L f (sourceOriginalJointGroupRelabel434 BP h σ x) =
    sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing
      L f x := by
  induction L generalizing f with
  | nil => exact hsymm σ x
  | cons g L ih =>
    have hg : g ≠ h := by
      intro he
      apply hh
      simp [he]
    have hh' : h ∉ L := by
      intro hhL
      exact hh (by simp [hhL])
    change
      sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing
        L (sourceOriginalJointGroupSurvivorProjector434
          BP mu g (probes g) (trailing g) f)
          (sourceOriginalJointGroupRelabel434 BP h σ x) =
      sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing
        L (sourceOriginalJointGroupSurvivorProjector434
          BP mu g (probes g) (trailing g) f) x
    apply ih hh'
    intro τ y
    exact source_original_joint_survivor_preserves_other_symmetry434
      BP mu g h hg (probes g) (trailing g) f hsymm τ y

/-- Exact binomial BIG group gain. -/
noncomputable def sourceOriginalJointProbeGain434
    {G : Type} {M : ℕ}
    (probes trailing : G → Finset (Fin M)) (g : G) : ℝ :=
  (((probes g).card + (trailing g).card).choose (probes g).card : ℕ)

/-- The REAL TRUE source BIG symmetric all-group physical
survivor operator has power-saving factor equal to the
PRODUCT of the sharp per-group binomial weights.
No test tensorization is assumed: f is any complex
jointly correlated physical source BIG observable invariant
under independent within-group BIG slot permutations.
The source group list must have no duplicates; each source
BIG group is projected only once. -/
theorem source_original_joint_all_group_physical_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hnorm : ∀ g, (∑ p : BP g, mu g p) = 1)
    (probes trailing : G → Finset (Fin M))
    (hdisj : ∀ g, Disjoint (probes g) (trailing g))
    (L : List G) (hL : L.Nodup)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ (g : G), g ∈ L →
       ∀ (σ : Equiv.Perm (Fin M))
         (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP g σ x) = f x) :
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointAllGroupSurvivor434
        BP mu probes trailing L f) *
      (L.map (sourceOriginalJointProbeGain434 probes trailing)).prod ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  induction L generalizing f with
  | nil =>
    simp [sourceOriginalJointAllGroupSurvivor434]
  | cons g L ih =>
    obtain ⟨hgnot,hLTail⟩ := List.nodup_cons.mp hL
    let F : SourceOriginalJointBigState434 BP M → ℂ :=
      sourceOriginalJointGroupSurvivorProjector434
        BP mu g (probes g) (trailing g) f
    have hrest :
        ∀ (h : G), h ∈ L →
          ∀ (σ : Equiv.Perm (Fin M))
            (x : SourceOriginalJointBigState434 BP M),
          F (sourceOriginalJointGroupRelabel434 BP h σ x) = F x := by
      intro h hh σ x
      have hgh : g ≠ h := by
        intro he
        apply hgnot
        rw [he]
        exact hh
      exact source_original_joint_survivor_preserves_other_symmetry434
        BP mu g h hgh (probes g) (trailing g) f
        (hsymm h (by simp [hh])) σ x
    have hTail := ih hLTail F hrest
    have hfirstsym :
        ∀ σ x, f (sourceOriginalJointGroupRelabel434 BP g σ x) = f x :=
      hsymm g (by simp)
    have hSingle :=
      source_original_joint_survivor_projector_contraction434
        BP mu hmu hnorm g (probes g) (trailing g) (hdisj g)
        f (source_original_joint_group_symmetry_to_fibres434
             BP g f hfirstsym)
    change
      sourceOriginalJointBigEnergy434 BP mu
        (sourceOriginalJointAllGroupSurvivor434
          BP mu probes trailing L F) *
        (sourceOriginalJointProbeGain434 probes trailing g *
          (L.map (sourceOriginalJointProbeGain434 probes trailing)).prod)
        ≤ sourceOriginalJointBigEnergy434 BP mu f
    have hC : (0:ℝ) ≤ (((probes g).card +
       (trailing g).card).choose (probes g).card : ℕ) := by
      exact Nat.cast_nonneg _
    calc
      _ = (sourceOriginalJointBigEnergy434 BP mu
        (sourceOriginalJointAllGroupSurvivor434
          BP mu probes trailing L F) *
        (L.map (sourceOriginalJointProbeGain434 probes trailing)).prod) *
        (((probes g).card + (trailing g).card).choose
           (probes g).card : ℕ) := by
             dsimp only [sourceOriginalJointProbeGain434]
             ring
      _ ≤ sourceOriginalJointBigEnergy434 BP mu F *
        (((probes g).card+(trailing g).card).choose
            (probes g).card : ℕ) :=
          mul_le_mul_of_nonneg_right hTail hC
      _ ≤ _ := hSingle
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigHarmonicPower -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- ACTUAL source03 group-dependent harmonic prime law:
for each BIG group g, its own source prime support BP g,
literal prime label prime(g,p) and original normalizer V_g.
Different groups are not forced into a common prime space. -/
noncomputable def sourceOriginalJointHarmonicMu434
    {G : Type} (BP : G → Type)
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (g : G) (p : BP g) : ℝ :=
  sourceOriginalHarmonicPrimeMu434 (prime g) (V g) p

/-- For all original BIG group-dependent finite prime intervals,
the physical independent prime weights μ_g(p)=1/(p V_g)
are true PROBABILITIES (not uniform prime surrogates)
under source normalization V_g=Σ_{p∈BP(g)}1/p>0. -/
theorem source_original_joint_harmonic_normalized434
    {G : Type} (BP : G → Type)
    [∀ g, Fintype (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ)) :
    (∀ (g : G) (p : BP g),
       0 ≤ sourceOriginalJointHarmonicMu434 BP prime V g p) ∧
    (∀ g, ∑ p : BP g,
      sourceOriginalJointHarmonicMu434 BP prime V g p = 1) := by
  constructor
  · intro g p
    exact source_original_harmonic_prime_nonneg434
      (prime g) (V g) (hV g) p
  · intro g
    exact source_original_harmonic_prime_normalized434
      (prime g) (V g) (hV g) (hEq g)

/-- Source-real groupwise harmonic full-probe squared-L²
operator suppression, simultaneous over ANY designated
list of distinct BIG groups, with arbitrary correlations
between all original BIG prime groups in f.
The only symmetry premise is the actual separate within-group
permutation symmetry of f, appropriate to the source ideal
symmetrization. All prime supports and V_g remain original. -/
theorem source_original_joint_harmonic_all_group_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ}
    (probes trailing : G → Finset (Fin M))
    (hdisj : ∀ g, Disjoint (probes g) (trailing g))
    (L : List G) (hL : L.Nodup)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ (g : G), g ∈ L →
       ∀ (σ : Equiv.Perm (Fin M))
         (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP g σ x) = f x) :
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalJointAllGroupSurvivor434 BP
        (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing L f) *
      (L.map (sourceOriginalJointProbeGain434 probes trailing)).prod ≤
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V) f := by
  obtain ⟨hnonneg,hnorm⟩ :=
    source_original_joint_harmonic_normalized434 BP
      prime V hV hEq
  exact source_original_joint_all_group_physical_power434
    BP (sourceOriginalJointHarmonicMu434 BP prime V)
    hnonneg hnorm probes trailing hdisj L hL f hsymm

/-- True BIG-joint (dependent prime supports) L² energy
is nonnegative whenever all its original one-prime
source harmonic probability masses are nonnegative. -/
theorem source_original_joint_big_energy_nonneg434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    0 ≤ sourceOriginalJointBigEnergy434 BP mu f := by
  unfold sourceOriginalJointBigEnergy434
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · unfold sourceOriginalJointBigMass434
    apply Finset.prod_nonneg
    intro g _
    unfold sourceOriginalRealBigProductMass434
    apply Finset.prod_nonneg
    intro i _
    exact hmu g (x g i)
  · exact Complex.normSq_nonneg (f x)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBIGLawTotal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact normalization of the FULL original joint BIG
probability law over all group-dependent labelled prime
types and all M physical slots. This does not replace
group-dependent prime intervals by one uniform type.
It follows from the independently normalized one-prime
source laws by twice applying finite dependent Fubini. -/
theorem source_original_joint_BIG_law_total434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g, ∑ p : BP g, mu g p = 1) :
    (∑ x : SourceOriginalJointBigState434 BP M,
       sourceOriginalJointBigMass434 BP mu x) = 1 := by
  classical
  unfold sourceOriginalJointBigMass434
    sourceOriginalRealBigProductMass434
  have hgroup (g : G) :
      (∑ a : Fin M → BP g, ∏ i : Fin M, mu g (a i)) = 1 := by
    calc
      _ = ∏ i : Fin M, ∑ p : BP g, mu g p := by
        rw [Finset.prod_univ_sum]
        simp only [Fintype.piFinset_univ]
      _ = 1 := by simp [hmu g]
  calc
    _ = ∏ g : G, ∑ a : Fin M → BP g,
        ∏ i : Fin M, mu g (a i) := by
      rw [Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ]
    _ = 1 := by simp [hgroup]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalVariableBIGLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- REAL original unshared source03 labelled prime tuples have
VARIABLE t_g numbers of slots in each BIG group g.
The state space is dependent on g, including the actual
group-specific prime support, not a fake common slot count. -/
abbrev SourceOriginalVariableBIGState434
    {G : Type} (BP : G → Type) (t : G → ℕ) :=
  (g : G) → Fin (t g) → BP g

noncomputable def sourceOriginalVariableBIGMass434
    {G : Type} [Fintype G] (BP : G → Type)
    (t : G → ℕ)
    (mu : (g : G) → BP g → ℝ)
    (x : SourceOriginalVariableBIGState434 BP t) : ℝ :=
  ∏ g : G, ∏ i : Fin (t g), mu g (x g i)

/-- Source03 variable free-slot law has mass one.
No hypotheses on equal t_g, numeric distinctness of
primes, or equality of the group supports are imposed. -/
theorem source_original_variable_BIG_law_total434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (t : G → ℕ)
    (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g, ∑ p : BP g, mu g p = 1) :
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x) = 1 := by
  classical
  unfold sourceOriginalVariableBIGMass434
  have hGroup (g : G) :
      (∑ a : Fin (t g) → BP g,
        ∏ i : Fin (t g), mu g (a i)) = 1 := by
    calc
      _ = ∏ i : Fin (t g), ∑ p : BP g, mu g p := by
        rw [Finset.prod_univ_sum]
        simp only [Fintype.piFinset_univ]
      _ = 1 := by simp [hmu g]
  calc
    _ = ∏ g : G, ∑ a : Fin (t g) → BP g,
        ∏ i : Fin (t g), mu g (a i) := by
        rw [Finset.prod_univ_sum]
        simp only [Fintype.piFinset_univ]
    _ = 1 := by simp [hGroup]

/-- Explicit nonnegative FULL source03 variable-slot
probability mass, for every physical dependent state. -/
theorem source_original_variable_BIG_mass_nonneg434
    {G : Type} [Fintype G]
    (BP : G → Type) (t : G → ℕ)
    (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (x : SourceOriginalVariableBIGState434 BP t) :
    0 ≤ sourceOriginalVariableBIGMass434 BP t mu x := by
  unfold sourceOriginalVariableBIGMass434
  apply Finset.prod_nonneg
  intro g hg
  apply Finset.prod_nonneg
  intro i hi
  exact hmu g (x g i)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalVariableBIGFlattenedLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual SOURCE03 group-VARIABLE free-slot state space
is equivalently the dependent tuple indexed by its genuine
sigma type (g,free_slot), preserving all original prime
support types and slot multiplicities. -/
noncomputable def sourceOriginalVariableBIGFlattenEquiv434
    {G : Type} (BP : G → Type) (t : G → ℕ) :
    SourceOriginalVariableBIGState434 BP t ≃
      ((k : Σ g : G, Fin (t g)) → BP k.1) :=
  (Equiv.piCurry (fun g (i : Fin (t g)) => BP g)).symm

theorem source_original_variable_BIG_flatten_apply434
    {G : Type} (BP : G → Type) (t : G → ℕ)
    (x : SourceOriginalVariableBIGState434 BP t)
    (g : G) (i : Fin (t g)) :
    sourceOriginalVariableBIGFlattenEquiv434 BP t x ⟨g,i⟩ =
      x g i := rfl

/-- Exact equality of SOURCE03 variable-slot physical mass
and flat-sigma physical mass. All marked group prime labels
remain distinct INDEXED draws, with true group-dependent laws. -/
theorem source_original_variable_BIG_flatten_mass434
    {G : Type} [Fintype G]
    (BP : G → Type) (t : G → ℕ)
    (mu : ∀ g, BP g → ℝ)
    (x : SourceOriginalVariableBIGState434 BP t) :
    sourceOriginalVariableBIGMass434 BP t mu x =
      ∏ k : (Σ g : G, Fin (t g)),
        mu k.1 (sourceOriginalVariableBIGFlattenEquiv434 BP t x k) := by
  unfold sourceOriginalVariableBIGMass434
  exact (Fintype.prod_sigma'
    (fun g (i : Fin (t g)) => mu g (x g i))).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigLogSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- Exact joint BIG all-group probe gain becomes the s-th
power of a single source m,ell binomial, for the original
group count s, without imposing product structure on f. -/
theorem source_original_joint_uniform_probe_gain434
    {G : Type} {M : ℕ}
    (probes trailing : G → Finset (Fin M))
    (m ell : ℕ) (L : List G)
    (hcard : ∀ g ∈ L,
      (probes g).card = m ∧ (trailing g).card = ell) :
    (L.map (sourceOriginalJointProbeGain434 probes trailing)).prod =
       ((((m+ell).choose m:ℕ):ℝ)^L.length) := by
  induction L with
  | nil => simp
  | cons g L ih =>
    have hg := hcard g (by simp)
    have ht : ∀ h ∈ L,
        (probes h).card = m ∧ (trailing h).card = ell := by
      intro h hh
      exact hcard h (by simp [hh])
    simp only [List.map_cons, List.prod_cons,
      List.length_cons, pow_succ]
    rw [ih ht]
    unfold sourceOriginalJointProbeGain434
    rw [hg.1,hg.2]
    ring

/-- FULL physical independently indexed joint source BIG
harmonic product L² surviving operator LOG-POWER suppression:
for any desired A, BIG group count s ≥ c log L and fixed
original probe m satisfying A≤ c log(m+1), the actual full
weighted multi-group L² survivor energy is O(L^-A) times
the actual input energy. Crucially source f may correlate
all BIG groups arbitrarily. This is an exact proven
Hilbert projection estimate, not a hypothesis on the ideal
source03 kernel. Source Knu/primitive character comparison
and signed physical transference must still be identified. -/
theorem source_original_joint_harmonic_big_log_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ}
    (probes trailing : G → Finset (Fin M))
    (hdisj : ∀ g, Disjoint (probes g) (trailing g))
    (L : List G) (hL : L.Nodup)
    (m ell : ℕ)
    (hcard : ∀ g ∈ L,
      (probes g).card = m ∧ (trailing g).card = ell)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (L.length:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsymm : ∀ (g : G), g ∈ L →
       ∀ (σ : Equiv.Perm (Fin M))
         (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP g σ x) = f x) :
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalJointAllGroupSurvivor434 BP
        (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing L f) * LL^A ≤
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V) f := by
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let H := sourceOriginalJointAllGroupSurvivor434 BP
       mu probes trailing L f
  let C : ℝ := ((((m+ell).choose m:ℕ):ℝ))
  have hpow1 := source_original_hoeffding_log_power434
      LL A c m L.length hLL hc hm hcount hbudget
  have hchooseR : (((m+1:ℕ):ℝ)) ≤ C := by
    dsimp only [C]
    exact_mod_cast source_original_hoeffding_choose_probe_growth434
      m ell hell
  have hpow2 : (((m+1:ℕ):ℝ)^L.length) ≤ C^L.length := by
    gcongr
  have hpow : LL^A ≤ C^L.length := hpow1.trans hpow2
  have hbase := source_original_joint_harmonic_all_group_power434
      BP prime V hV hEq probes trailing hdisj
      L hL f hsymm
  have hgain := source_original_joint_uniform_probe_gain434
      probes trailing m ell L hcard
  rw [hgain] at hbase
  change sourceOriginalJointBigEnergy434 BP mu H *
      C^L.length ≤ sourceOriginalJointBigEnergy434 BP mu f at hbase
  obtain ⟨hnonneg,hnorm⟩ :=
    source_original_joint_harmonic_normalized434 BP prime V hV hEq
  have hEnergy : 0 ≤ sourceOriginalJointBigEnergy434 BP mu H :=
    source_original_joint_big_energy_nonneg434 BP mu hnonneg H
  change sourceOriginalJointBigEnergy434 BP mu H * LL^A ≤
    sourceOriginalJointBigEnergy434 BP mu f
  exact (mul_le_mul_of_nonneg_left hpow hEnergy).trans hbase
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointSymmetrizePreserve -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- A genuine source BIG group permutation before replacing
that very group's prime list is irrelevant to the replacement.
The other group-dependent prime coordinates are unchanged. -/
theorem source_original_joint_self_relabel_update434
    {G : Type} [DecidableEq G]
    (BP : G → Type) {M : ℕ}
    (g : G) (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M)
    (u : Fin M → BP g) :
    Function.update
      (sourceOriginalJointGroupRelabel434 BP g σ x) g u =
    Function.update x g u := by
  unfold sourceOriginalJointGroupRelabel434
  rw [Function.update_idem]

/-- The source group-g physical BIG symmetrizer creates actual
permutation-invariance in group g for ANY fully coupled f,
while retaining literal group-dependent primes and V_g. -/
theorem source_original_joint_group_symmetrize_invariant434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointBigGroupSymmetrize434 BP g f
      (sourceOriginalJointGroupRelabel434 BP g σ x) =
    sourceOriginalJointBigGroupSymmetrize434 BP g f x := by
  unfold sourceOriginalJointBigGroupSymmetrize434
  have hgroup :
      (sourceOriginalJointGroupRelabel434 BP g σ x) g =
      (fun i => x g (σ i)) := by
    unfold sourceOriginalJointGroupRelabel434
    simp
  rw [hgroup]
  have hfun :
      (fun u => f (Function.update
        (sourceOriginalJointGroupRelabel434 BP g σ x) g u)) =
      (fun u => f (Function.update x g u)) := by
    funext u
    rw [source_original_joint_self_relabel_update434
      BP g σ x u]
  rw [hfun]
  exact source_original_big_symmetrize_invariant434
    (fun u => f (Function.update x g u)) σ (x g)

/-- Physical source group-g permutation averaging does not
destroy separately symmetric joint tests in a different group h.
No independence of the original fully coupled f is assumed. -/
theorem source_original_joint_symmetrize_preserves_other434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ a, Fintype (BP a)]
    [∀ a, DecidableEq (BP a)]
    {M : ℕ} (g h : G) (hgh : g ≠ h)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin M))
       (x : SourceOriginalJointBigState434 BP M),
       f (sourceOriginalJointGroupRelabel434 BP h σ x) = f x)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointBigGroupSymmetrize434 BP g f
      (sourceOriginalJointGroupRelabel434 BP h σ x) =
    sourceOriginalJointBigGroupSymmetrize434 BP g f x := by
  unfold sourceOriginalJointBigGroupSymmetrize434
  have hgroup : (sourceOriginalJointGroupRelabel434 BP h σ x) g =
    x g := by
    unfold sourceOriginalJointGroupRelabel434
    simp [hgh]
  rw [hgroup]
  congr 1
  funext u
  rw [source_original_joint_update_relabel_commute434
    BP g h hgh σ x u]
  exact hsym σ (Function.update x g u)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointAllSymmetrize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- ACTUAL independently-permuted source BIG-group symmetrizer.
The all-group source test may be arbitrarily entangled across
groups; no tensor-product observable assumption is used. -/
noncomputable def sourceOriginalJointAllSymmetrize434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} :
    List G → (SourceOriginalJointBigState434 BP M → ℂ) →
      SourceOriginalJointBigState434 BP M → ℂ
  | [], f => f
  | g :: L, f =>
    sourceOriginalJointAllSymmetrize434 BP L
      (sourceOriginalJointBigGroupSymmetrize434 BP g f)

/-- Symmetrizing source BIG groups in L never destroys the
source's existing BIG slot symmetry in a different group h.
This is the exact physical algebra allowing all BIG group
symmetries to coexist for arbitrary coupled source tests. -/
theorem source_original_joint_all_symmetrize_preserves_external434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ a, Fintype (BP a)]
    [∀ a, DecidableEq (BP a)]
    {M : ℕ} (L : List G) (h : G) (hnot : h ∉ L)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin M))
      (x : SourceOriginalJointBigState434 BP M),
      f (sourceOriginalJointGroupRelabel434 BP h σ x) = f x)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointAllSymmetrize434 BP L f
      (sourceOriginalJointGroupRelabel434 BP h σ x) =
    sourceOriginalJointAllSymmetrize434 BP L f x := by
  induction L generalizing f with
  | nil =>
    exact hsym σ x
  | cons g L ih =>
    have hgh : g ≠ h := by
      intro he
      apply hnot
      simp [he]
    have hnot' : h ∉ L := by
      intro hh
      exact hnot (by simp [hh])
    change
      sourceOriginalJointAllSymmetrize434 BP L
        (sourceOriginalJointBigGroupSymmetrize434 BP g f)
          (sourceOriginalJointGroupRelabel434 BP h σ x) =
      sourceOriginalJointAllSymmetrize434 BP L
        (sourceOriginalJointBigGroupSymmetrize434 BP g f) x
    apply ih hnot'
    intro τ y
    exact source_original_joint_symmetrize_preserves_other434
      BP g h hgh f hsym τ y

/-- A TRUE sequential average over independent BIG source
endpoint permutations produces a globally source-permutation
symmetric test in EVERY designated group, from ANY arbitrary
complex joint BIG source f. No initial f-symmetry assumption. -/
theorem source_original_joint_all_symmetrize_invariant434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ a, Fintype (BP a)]
    [∀ a, DecidableEq (BP a)]
    {M : ℕ} (L : List G) (hL : L.Nodup)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (g : G) (hg : g ∈ L)
    (σ : Equiv.Perm (Fin M))
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalJointAllSymmetrize434 BP L f
      (sourceOriginalJointGroupRelabel434 BP g σ x) =
    sourceOriginalJointAllSymmetrize434 BP L f x := by
  induction L generalizing f with
  | nil =>
    simp at hg
  | cons h L ih =>
    obtain ⟨hnot,hLTail⟩ := List.nodup_cons.mp hL
    rcases List.mem_cons.mp hg with heq | hmem
    · subst h
      change
        sourceOriginalJointAllSymmetrize434 BP L
          (sourceOriginalJointBigGroupSymmetrize434 BP g f)
          (sourceOriginalJointGroupRelabel434 BP g σ x) =
        sourceOriginalJointAllSymmetrize434 BP L
          (sourceOriginalJointBigGroupSymmetrize434 BP g f) x
      apply source_original_joint_all_symmetrize_preserves_external434
        BP L g hnot
          (sourceOriginalJointBigGroupSymmetrize434 BP g f)
      exact source_original_joint_group_symmetrize_invariant434 BP g f
    · change
        sourceOriginalJointAllSymmetrize434 BP L
          (sourceOriginalJointBigGroupSymmetrize434 BP h f)
            (sourceOriginalJointGroupRelabel434 BP g σ x) =
        sourceOriginalJointAllSymmetrize434 BP L
          (sourceOriginalJointBigGroupSymmetrize434 BP h f) x
      exact ih hLTail
        (sourceOriginalJointBigGroupSymmetrize434 BP h f)
        hmem

/-- Direct source C34 true harmonic BIG L^-A estimate for the
PHYSICALLY symmetrized joint test, with completely arbitrary
unsymmetrized original complex f as input.
Its norm RHS is still ||Sym f||²; controlling ||Sym f||²
by ||f||² is a separate source-energy contraction proof. -/
theorem source_original_joint_symmetrized_harmonic_log_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ}
    (probes trailing : G → Finset (Fin M))
    (hdisj : ∀ g, Disjoint (probes g) (trailing g))
    (L : List G) (hL : L.Nodup)
    (m ell : ℕ)
    (hcard : ∀ g ∈ L,
      (probes g).card = m ∧ (trailing g).card = ell)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (L.length:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalJointAllGroupSurvivor434 BP
        (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing L
          (sourceOriginalJointAllSymmetrize434 BP L f)) *
        LL^A ≤
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalJointAllSymmetrize434 BP L f) := by
  exact source_original_joint_harmonic_big_log_power434
    BP prime V hV hEq probes trailing hdisj L hL m ell
    hcard LL A c hLL hc hm hell hcount hbudget
    (sourceOriginalJointAllSymmetrize434 BP L f)
    (fun g hg σ x =>
      source_original_joint_all_symmetrize_invariant434
        BP L hL f g hg σ x)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteComplexAverageNorm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Actual complex Cauchy–Schwarz squared-norm estimate for
an arbitrary FINITE collection of signed complex values:
no bound is assumed on the individual source comparison Knu.
This is the finite Hilbert fact required to prove contraction
of the literal BIG permutation average. -/
theorem source_original_finite_complex_sum_normSq_le_card434
    {I : Type} (S : Finset I) (z : I → ℂ) :
    Complex.normSq (∑ i ∈ S, z i) ≤
      (S.card:ℝ) * (∑ i ∈ S, Complex.normSq (z i)) := by
  have hre : (∑ i ∈ S, (z i).re)^2 ≤
      (S.card:ℝ) * (∑ i ∈ S, (z i).re ^ 2) :=
    sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => (z i).re)
  have him : (∑ i ∈ S, (z i).im)^2 ≤
      (S.card:ℝ) * (∑ i ∈ S, (z i).im ^ 2) :=
    sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => (z i).im)
  calc
    Complex.normSq (∑ i ∈ S, z i) =
      (∑ i ∈ S, (z i).re)^2 +
      (∑ i ∈ S, (z i).im)^2 := by
         simp only [Complex.normSq_apply, Complex.re_sum,
           Complex.im_sum, pow_two]
    _ ≤ (S.card:ℝ) * (∑ i ∈ S, (z i).re ^ 2) +
        (S.card:ℝ) * (∑ i ∈ S, (z i).im ^ 2) :=
      add_le_add hre him
    _ = (S.card:ℝ)*(∑ i ∈ S, Complex.normSq (z i)) := by
      rw [←mul_add, ←Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [Complex.normSq_apply,pow_two]

/-- TRUE finite complex average is a squared L2 contraction
relative to its OWN finite indexed input ensemble. Applies
to the group source symmetrizer even when numerical primes
repeat across ordered BIG slots. -/
theorem source_original_finite_complex_average_normSq434
    {I : Type} [Fintype I] [Nonempty I]
    (z : I → ℂ) :
    Complex.normSq ((Fintype.card I : ℂ)⁻¹ * ∑ i : I, z i) ≤
      (Fintype.card I : ℝ)⁻¹ *
        ∑ i : I, Complex.normSq (z i) := by
  let n : ℝ := (Fintype.card I : ℝ)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos (α := I)
  have hn2 : 0 ≤ (n⁻¹)^2 := sq_nonneg _
  have hsum := source_original_finite_complex_sum_normSq_le_card434
      (Finset.univ : Finset I) z
  simp only [Finset.card_univ] at hsum
  have hc : Complex.normSq ((Fintype.card I:ℂ)⁻¹) =
      (n⁻¹)^2 := by
    simp only [Complex.normSq_inv, Complex.normSq_natCast]
    dsimp only [n]
    rw [←pow_two, inv_pow]
  calc
    _ = (n⁻¹)^2 * Complex.normSq (∑ i : I, z i) := by
      rw [Complex.normSq_mul,hc]
    _ ≤ (n⁻¹)^2 * (n * ∑ i : I, Complex.normSq (z i)) :=
      mul_le_mul_of_nonneg_left hsum hn2
    _ = n⁻¹ * ∑ i : I, Complex.normSq (z i) := by
      field_simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigSymmetrizeEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Source REAL group BIG reciprocal-prime product mass is
nonnegative even with repeated numerical primes in independently
indexed source BIG slots. -/
theorem source_original_big_product_mass_nonneg434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p) (x : Fin M → P) :
    0 ≤ sourceOriginalRealBigProductMass434 mu x := by
  unfold sourceOriginalRealBigProductMass434
  apply Finset.prod_nonneg
  intro i _
  exact hmu (x i)

/-- Source physically averaged permutation operator on indexed
BIG primes is a GENUINE weighted complex Hilbert contraction.
No symmetry assumption on the input f, no factorization of f,
no distinctness of numeric prime labels, no SW theorem and
no abstract Jensen axiom. The normalizing denominator is the
TRUE finite number of all coordinate permutations. -/
theorem source_original_big_symmetrize_actual_energy_contract434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434 mu
      (sourceOriginalBigSymmetrize434 f) ≤
    sourceOriginalBigActualEnergy434 mu f := by
  let n : ℝ := (Fintype.card (Equiv.Perm (Fin M)):ℝ)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos (α := Equiv.Perm (Fin M))
  have hpoint (x : Fin M → P) :
      Complex.normSq (sourceOriginalBigSymmetrize434 f x) ≤
      n⁻¹ * (∑ σ : Equiv.Perm (Fin M),
        Complex.normSq (f (fun j => x (σ j)))) := by
    unfold sourceOriginalBigSymmetrize434
    exact source_original_finite_complex_average_normSq434
      (fun σ : Equiv.Perm (Fin M) => f (fun j => x (σ j)))
  have hsum :
      sourceOriginalBigActualEnergy434 mu
        (sourceOriginalBigSymmetrize434 f) ≤
      ∑ x : Fin M → P, sourceOriginalRealBigProductMass434 mu x *
        (n⁻¹ * (∑ σ : Equiv.Perm (Fin M),
          Complex.normSq (f (fun j => x (σ j))))) := by
    unfold sourceOriginalBigActualEnergy434
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hpoint x)
      (source_original_big_product_mass_nonneg434 mu hmu x)
  calc
    _ ≤ ∑ x : Fin M → P, sourceOriginalRealBigProductMass434 mu x *
        (n⁻¹ * (∑ σ : Equiv.Perm (Fin M),
          Complex.normSq (f (fun j => x (σ j))))) := hsum
    _ = n⁻¹ * ∑ σ : Equiv.Perm (Fin M),
        sourceOriginalBigActualEnergy434 mu
          (fun x => f (fun j => x (σ j))) := by
      unfold sourceOriginalBigActualEnergy434
      calc
        _ = n⁻¹ * ∑ x : Fin M → P,
              ∑ σ : Equiv.Perm (Fin M),
                sourceOriginalRealBigProductMass434 mu x *
                 Complex.normSq (f (fun j => x (σ j))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.mul_sum]
            ring
        _ = _ := by rw [Finset.sum_comm]
    _ = n⁻¹ * ∑ _σ : Equiv.Perm (Fin M),
          sourceOriginalBigActualEnergy434 mu f := by
      apply congrArg (fun y : ℝ => n⁻¹*y)
      apply Finset.sum_congr rfl
      intro σ _
      exact source_original_big_actual_energy_permutation434
        mu σ f
    _ = sourceOriginalBigActualEnergy434 mu f := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      change n⁻¹ * (n * sourceOriginalBigActualEnergy434 mu f) =
        sourceOriginalBigActualEnergy434 mu f
      field_simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalJointBigSymmetrizeContract -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A source physical independent within-group slot permutation
symmetrizer is a TRUE L² CONTRACTION on the JOINT BIG product
prime law with dependent group types and distinct V_g.
The arbitrary signed global source observable f may couple
all BIG groups, including logarithmic cells and primitive
character tests. No factorization, f-symmetry or abstract
operator norm premise is introduced. -/
theorem source_original_joint_single_symmetrizer_energy_contract434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (hmu : ∀ h p, 0 ≤ mu h p)
    (g : G)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointBigGroupSymmetrize434 BP g f) ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  rw [source_original_joint_big_energy_conditional_fubini434,
      source_original_joint_big_energy_conditional_fubini434]
  apply Finset.sum_le_sum
  intro rest _
  have hFibre :
      sourceOriginalJointBigConditionalTest434 BP g
        (sourceOriginalJointBigGroupSymmetrize434 BP g f)
        rest =
      sourceOriginalBigSymmetrize434
        (sourceOriginalJointBigConditionalTest434 BP g f rest) := by
    funext u
    exact source_original_joint_big_symmetrize_fibre434
      BP g f rest u
  rw [hFibre]
  have hh := source_original_big_symmetrize_actual_energy_contract434
    (mu g) (hmu g) (sourceOriginalJointBigConditionalTest434 BP g f rest)
  exact mul_le_mul_of_nonneg_left hh
    (source_original_joint_rest_mass_nonneg434 BP mu hmu g rest)

/-- The ACTUAL original BIG independently-permuted source
endpoint average over ALL named groups is a true weighted L²
CONTRACTION, even when the original complex f has arbitrary
global inter-group correlations. All source group-dependent
prime supports BP(g), reciprocal-prime weights and numerical
prime duplicates remain untouched. -/
theorem source_original_joint_all_symmetrize_energy_contract434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ h, Fintype (BP h)]
    [∀ h, DecidableEq (BP h)]
    {M : ℕ} (mu : (h : G) → BP h → ℝ)
    (hmu : ∀ h p, 0 ≤ mu h p)
    (L : List G)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointAllSymmetrize434 BP L f) ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  induction L generalizing f with
  | nil =>
    simp [sourceOriginalJointAllSymmetrize434]
  | cons g L ih =>
    change sourceOriginalJointBigEnergy434 BP mu
      (sourceOriginalJointAllSymmetrize434 BP L
        (sourceOriginalJointBigGroupSymmetrize434 BP g f)) ≤
      sourceOriginalJointBigEnergy434 BP mu f
    exact (ih (sourceOriginalJointBigGroupSymmetrize434 BP g f)).trans
      (source_original_joint_single_symmetrizer_energy_contract434
        BP mu hmu g f)

/-- Quantitative SOURCE03 BIG-group physical Hoeffding suppression
with the ORIGINAL unsymmetrized full complex input f on the RHS:
for s>=c log L and m chosen independently of J,L,
  L^A * ||P_all Sym_all(f)||² <= ||f||².
Nothing is assumed about source f being group-independent or
symmetric in its BIG prime slots; TRUE physical separately
permuted endpoint symmetrization is constructed and shown
contractive. This is a genuine FULL JOINT HILBERT theorem,
NOT yet the original signed source03 comparison-kernel bound. -/
theorem source_original_joint_unsymmetrized_harmonic_log_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ}
    (probes trailing : G → Finset (Fin M))
    (hdisj : ∀ g, Disjoint (probes g) (trailing g))
    (L : List G) (hL : L.Nodup)
    (m ell : ℕ)
    (hcard : ∀ g ∈ L,
      (probes g).card = m ∧ (trailing g).card = ell)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (L.length:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalJointAllGroupSurvivor434 BP
        (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing L
          (sourceOriginalJointAllSymmetrize434 BP L f)) *
        LL^A ≤
    sourceOriginalJointBigEnergy434 BP
      (sourceOriginalJointHarmonicMu434 BP prime V) f := by
  have hC := source_original_joint_symmetrized_harmonic_log_power434
    BP prime V hV hEq probes trailing hdisj L hL m ell
    hcard LL A c hLL hc hm hell hcount hbudget f
  obtain ⟨hpos,hnorm⟩ :=
    source_original_joint_harmonic_normalized434 BP prime V hV hEq
  have hSym := source_original_joint_all_symmetrize_energy_contract434
    BP (sourceOriginalJointHarmonicMu434 BP prime V)
    hpos L f
  exact hC.trans hSym
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeBigGroupFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Number of actually freed original SOURCE03 first-m positions
of a single BIG group g in a ν-block. Different marked
positions with equal numerical prime values are not conflated. -/
noncomputable def sourceOriginalProbeChosenGroupCount434
    {G : Type} [DecidableEq G] (m : ℕ)
    (A : Finset (G × Fin m)) (g : G) : ℕ :=
  Fintype.card {i : Fin m // (g,i) ∈ A}

/-- The actual source03 marked probe count in a group never
exceeds m, without assuming it as an external cap. -/
theorem source_original_probe_chosen_group_count_le434
    {G : Type} [DecidableEq G] (m : ℕ)
    (A : Finset (G × Fin m)) (g : G) :
    sourceOriginalProbeChosenGroupCount434 m A g ≤ m := by
  dsimp [sourceOriginalProbeChosenGroupCount434]
  simpa only [Fintype.card_fin] using
    (Fintype.card_le_of_injective
      (fun i : {i : Fin m // (g,i) ∈ A} => i.val)
      (by intro i j hij; exact Subtype.ext hij))

/-- EXACT original probe ν-block index identification, on the
chosen BIG groups only:
  (group g, enumerated chosen slot among g)
       ↔ (original marked position (g,i)∈A).
The enumeration by Fin k_g uses only the natural finite
equivalence of each group's TRUE chosen slots. Thus this
is a genuine bijection, rather than assuming the original
ν-pattern auxiliary product matches the generic C6 group
product. No small-group factors or invented marks. -/
noncomputable def sourceOriginalProbeGroupSigmaEquiv434
    {G : Type} [DecidableEq G]
    (m : ℕ) (block : Finset G)
    (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m) :
    (Σ g : block,
      Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) ≃
        {p : G × Fin m // p ∈ A} where
  toFun z := by
    have hj : Fin (Fintype.card
      {i : Fin m // (z.1.val,i) ∈ A}) := by
        simpa only [sourceOriginalProbeChosenGroupCount434] using z.2
    let f : {i : Fin m // (z.1.val,i) ∈ A} :=
      (Fintype.equivFin {i : Fin m // (z.1.val,i) ∈ A}).symm hj
    exact ⟨(z.1.val,f.val),f.property⟩
  invFun p := by
    have hg : p.val.1 ∈ block := by
      have hmem := hBlock p.property
      simpa [sourceOriginalProbeBlock434] using hmem
    let f : {i : Fin m // (p.val.1,i)∈A} :=
      ⟨p.val.2,p.property⟩
    have hj : Fin (sourceOriginalProbeChosenGroupCount434
        m A p.val.1) := by
      simpa only [sourceOriginalProbeChosenGroupCount434] using
        (Fintype.equivFin {i : Fin m // (p.val.1,i)∈A}) f
    exact ⟨⟨p.val.1,hg⟩, hj⟩
  left_inv z := by
    rcases z with ⟨g,j⟩
    dsimp only
    apply Sigma.ext (by apply Subtype.ext; rfl)
    simp [sourceOriginalProbeChosenGroupCount434] <;> rfl
  right_inv p := by
    apply Subtype.ext
    simp [sourceOriginalProbeChosenGroupCount434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeLogBudget -/

section

namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- SOURCE03's genuine designated-probe comparison family costs a
fixed power of L in cardinality. The exponent depends on fixed m
and C0 but NOT on the later freely chosen J. Assumes the genuine
source group-count bound s1+s2 <= C0*log L. -/
theorem source_original_probe_family_log_power_card434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (L C0 : ℝ) (hL : 1 ≤ L)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0 * Real.log L) :
    ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) ≤
      L ^ ((m:ℝ)*C0*Real.log 2) := by
  let N : ℕ := m*(blockA.card+blockB.card)
  have hCountNat := source_original_two_block_probe_pattern_card434
    blockA blockB m
  have hCount : 
      ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) ≤
      (2:ℝ)^N := by
    exact_mod_cast hCountNat
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : 0 ≤ Real.log (2:ℝ) :=
    Real.log_nonneg (by norm_num)
  have hArgCard : (N:ℝ) ≤ (m:ℝ)*(C0*Real.log L) := by
    have h := mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg m)
    simpa only [N,Nat.cast_mul] using h
  have hLogArg :
      Real.log (2:ℝ)*(N:ℝ) ≤
      Real.log L*((m:ℝ)*C0*Real.log 2) := by
    calc
      _ ≤ Real.log 2*((m:ℝ)*(C0*Real.log L)) :=
        mul_le_mul_of_nonneg_left hArgCard hlog2
      _ = _ := by ring
  have hPow : (2:ℝ)^N ≤ L^((m:ℝ)*C0*Real.log 2) := by
    calc
      _ = (2:ℝ)^(N:ℝ) := (Real.rpow_natCast 2 N).symm
      _ = Real.exp (Real.log 2*(N:ℝ)) :=
        Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2) _
      _ ≤ Real.exp (Real.log L*((m:ℝ)*C0*Real.log 2)) :=
        Real.exp_le_exp.mpr hLogArg
      _ = L^((m:ℝ)*C0*Real.log 2) :=
        (Real.rpow_def_of_pos hLpos _).symm
  exact hCount.trans hPow
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTwoPowerLog -/

section

namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The ENTIRE ambient designated-probe power-set count, not just
its subset of admissible nonempty paired patterns, is bounded by a
fixed power of the source large parameter L independently of J. -/
theorem source_original_probe_two_power_log_bound434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (L C0 : ℝ) (hL : 1 ≤ L)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0 * Real.log L) :
    (2:ℝ)^(m*(blockA.card+blockB.card)) ≤
      L^((m:ℝ)*C0*Real.log 2) := by
  let N : ℕ := m*(blockA.card+blockB.card)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : 0 ≤ Real.log (2:ℝ) :=
    Real.log_nonneg (by norm_num)
  have hArgCard : (N:ℝ) ≤ (m:ℝ)*(C0*Real.log L) := by
    have h := mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg m)
    simpa only [N,Nat.cast_mul] using h
  have hLogArg :
      Real.log (2:ℝ)*(N:ℝ) ≤
      Real.log L*((m:ℝ)*C0*Real.log 2) := by
    calc
      _ ≤ Real.log 2*((m:ℝ)*(C0*Real.log L)) :=
        mul_le_mul_of_nonneg_left hArgCard hlog2
      _ = _ := by ring
  calc
    _ = (2:ℝ)^(N:ℝ) := (Real.rpow_natCast 2 N).symm
    _ = Real.exp (Real.log 2*(N:ℝ)) :=
      Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2) _
    _ ≤ Real.exp (Real.log L*((m:ℝ)*C0*Real.log 2)) :=
      Real.exp_le_exp.mpr hLogArg
    _ = L^((m:ℝ)*C0*Real.log 2) :=
      (Real.rpow_def_of_pos hLpos _).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeFixedPowerBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Once the ORIGINAL source03 group count and the primitive-kernel
parameters have fixed logarithmic power bounds, the comparison
family PLUS THE RAW PATTERN (of absolute cost one) has a fixed
logarithmic power budget, with exponent INDEPENDENT OF J.
No separate hFamilyBudget assumption is used: the actual probe
enumeration and its kernel bound are the only inputs. -/
theorem source_original_probe_raw_plus_cost_fixed_power434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (L C0 xi : ℝ) (Cq Cxi : ℕ)
    (hL : 2 ≤ L) (hC0 : 0 ≤ C0) (hxi : 0 < xi)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤
      C0 * Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (cost : SourceOriginalProbePattern434 G m → ℝ)
    (hCost : (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      cost ν) ≤ (2 ^ (m*(blockA.card+blockB.card)):ℝ) *
        ((Q:ℝ)^4*(xi⁻¹)^2)) :
    1+(∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      cost ν) ≤
      L^((m:ℝ)*C0*Real.log 2 + ((4*Cq+2*Cxi:ℕ):ℝ)+1) := by
  let θ : ℝ := (m:ℝ)*C0*Real.log 2
  let N : ℕ := 4*Cq+2*Cxi
  let E : ℝ := θ+(N:ℝ)
  have hLp : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := hLp.le
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hθ : 0 ≤ θ := by
    dsimp only [θ]
    positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hP : (2:ℝ)^(m*(blockA.card+blockB.card)) ≤ L^θ := by
    exact source_original_probe_two_power_log_bound434
      blockA blockB m L C0 (by linarith) hGroups
  have hQ4 : (Q:ℝ)^4 ≤ (L^Cq)^4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4
  have hXi2 : (xi⁻¹)^2 ≤ (L^Cxi)^2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hXi 2
  have hKernel : (Q:ℝ)^4*(xi⁻¹)^2 ≤ L^N := by
    calc
      _ ≤ (L^Cq)^4*(L^Cxi)^2 := by
        exact mul_le_mul hQ4 hXi2 (sq_nonneg _)
          (pow_nonneg (pow_nonneg hLnonneg _) _)
      _ = L^(Cq*4+Cxi*2) := by rw [pow_add,pow_mul,pow_mul]
      _ = L^N := by
        congr 1
        dsimp [N]
        omega
  have hCostFixed :
      (2:ℝ)^(m*(blockA.card+blockB.card)) *
        ((Q:ℝ)^4*(xi⁻¹)^2) ≤ L^E := by
    calc
      _ ≤ L^θ*L^N := by
        apply mul_le_mul hP hKernel
        · positivity
        · positivity
      _ = L^E := by
        dsimp only [E]
        simpa only [Real.rpow_natCast] using
          (Real.rpow_add hLp θ (N:ℝ)).symm
  have hOne : 1 ≤ L^E := by
    rw [Real.rpow_def_of_pos hLp]
    have hh : 0 ≤ Real.log L*E := mul_nonneg hlogL hE
    have hh' := (Real.exp_le_exp.mpr hh)
    simpa only [Real.exp_zero] using hh'
  calc
    _ ≤ 1+(2:ℝ)^(m*(blockA.card+blockB.card)) *
        ((Q:ℝ)^4*(xi⁻¹)^2) := by linarith
    _ ≤ 1+L^E := by linarith [hCostFixed]
    _ ≤ 2*L^E := by linarith
    _ ≤ L*L^E := mul_le_mul_of_nonneg_right hL (by positivity)
    _ = L^(θ+(N:ℝ)+1) := by
      dsimp only [E]
      rw [Real.rpow_add hLp (θ+(N:ℝ)) 1,
        Real.rpow_add hLp θ (N:ℝ),Real.rpow_one]
      ring
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

