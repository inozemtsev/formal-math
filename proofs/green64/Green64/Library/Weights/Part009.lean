module

public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Weights.Part002

@[expose] public section

/-!
# Weights / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SmallPermutedEdge -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

abbrev SlotPerm := Equiv.Perm (Fin M)

/-- A source and a target list are INDEPENDENTLY permuted before the
pattern's shared source/target slots are compared. Reversal swaps both
permutations rather than pretending they are a single symmetrization. -/
def sameSharedPerm (shared : Finset (Fin M))
    (σ τ : SlotPerm M)
    (x z : SmallState modulus M) : Prop :=
  ∀ j ∈ shared,
    marks modulus M x (σ j) = marks modulus M z (τ j)

def edgeAllowedPerm (shared : Finset (Fin M))
    (step : ℤ) (σ τ : SlotPerm M)
    (x z : SmallState modulus M) : Prop :=
  residues modulus M z = translate modulus step (residues modulus M x) ∧
    sameSharedPerm modulus M shared σ τ x z

theorem edgeAllowedPerm_reverse
    (shared : Finset (Fin M))
    (step : ℤ) (σ τ : SlotPerm M)
    (x z : SmallState modulus M) :
    edgeAllowedPerm modulus M shared step σ τ x z ↔
      edgeAllowedPerm modulus M shared (-step) τ σ z x := by
  constructor
  · rintro ⟨hshift,hshared⟩
    constructor
    · rw [hshift,translate_neg]
    · intro j hj
      exact (hshared j hj).symm
  · rintro ⟨hshift,hshared⟩
    constructor
    · rw [hshift,translate_back]
    · intro j hj
      exact (hshared j hj).symm

/-- The oriented edge coefficient may depend on BOTH sampled endpoint
permutations. Reversed data conjugate that coefficient and transpose
the two permutation arguments, exactly as the published physical
source does. -/
def reversePermutationKernel (K : SlotPerm M → SlotPerm M → ℂ) :
    SlotPerm M → SlotPerm M → ℂ :=
  fun τ σ => star (K σ τ)

noncomputable def permutedKernel
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ)
    (K : SlotPerm M → SlotPerm M → ℂ)
    (σ τ : SlotPerm M)
    (x z : SmallState modulus M) : ℂ :=
  if edgeAllowedPerm modulus M shared step σ τ x z then
    K σ τ * (edgeScalar modulus M q V shared x z : ℂ)
  else 0

theorem permutedKernel_reverse
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ)
    (K : SlotPerm M → SlotPerm M → ℂ)
    (σ τ : SlotPerm M)
    (x z : SmallState modulus M) :
    permutedKernel modulus M q V shared step K σ τ x z =
      star (permutedKernel modulus M q V shared (-step)
        (reversePermutationKernel M K) τ σ z x) := by
  by_cases h : edgeAllowedPerm modulus M shared step σ τ x z
  · have hr := (edgeAllowedPerm_reverse modulus M shared step σ τ x z).mp h
    simp only [permutedKernel,h,hr,if_true,reversePermutationKernel,
      star_mul,star_star]
    rw [edgeScalar_symmetric modulus M q V shared z x]
    rw [Complex.star_def,Complex.conj_ofReal]
    ring
  · have hr : ¬ edgeAllowedPerm modulus M shared (-step) τ σ z x := by
      intro hh
      exact h ((edgeAllowedPerm_reverse modulus M shared step σ τ x z).mpr hh)
    simp [permutedKernel,h,hr]

/-- Source and target endpoint averaging each contribute a separate
factor 1/M!, not a single (M!)^-1. -/
noncomputable def permutationPairMass : ℝ :=
  1 / ((Nat.factorial M : ℝ)^2)

theorem permutationPairMass_positive :
    0 < permutationPairMass M := by
  unfold permutationPairMass
  positivity

noncomputable def averagedSmallKernel
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ)
    (K : SlotPerm M → SlotPerm M → ℂ)
    (x z : SmallState modulus M) : ℂ :=
  (permutationPairMass M : ℂ) *
    (∑ σ : SlotPerm M,
      ∑ τ : SlotPerm M,
        permutedKernel modulus M q V shared step K σ τ x z)

/-- **NONCONSTANT permutation-dependent source kernel** reversal:
independent source/target symmetrizations are preserved exactly
under swapping σ and τ. We do NOT cancel M! per term; the
independent average is necessary for the actual physical operator. -/
theorem averagedSmallKernel_reverse
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ)
    (K : SlotPerm M → SlotPerm M → ℂ)
    (x z : SmallState modulus M) :
    averagedSmallKernel modulus M q V shared step K x z =
      star (averagedSmallKernel modulus M q V shared (-step)
        (reversePermutationKernel M K) z x) := by
  unfold averagedSmallKernel
  rw [star_mul]
  have hnorm :
      star ((permutationPairMass M : ℝ) : ℂ) =
        ((permutationPairMass M : ℝ) : ℂ) := by
    rw [Complex.star_def,Complex.conj_ofReal]
  rw [hnorm]
  have hsum :
      (∑ σ : SlotPerm M, ∑ τ : SlotPerm M,
        permutedKernel modulus M q V shared step K σ τ x z) =
      star (∑ τ : SlotPerm M, ∑ σ : SlotPerm M,
        permutedKernel modulus M q V shared (-step)
          (reversePermutationKernel M K) τ σ z x) := by
    calc
      (∑ σ : SlotPerm M, ∑ τ : SlotPerm M,
        permutedKernel modulus M q V shared step K σ τ x z) =
      (∑ τ : SlotPerm M, ∑ σ : SlotPerm M,
        permutedKernel modulus M q V shared step K σ τ x z) :=
          Finset.sum_comm
      _ = (∑ τ : SlotPerm M, ∑ σ : SlotPerm M,
        star (permutedKernel modulus M q V shared (-step)
          (reversePermutationKernel M K) τ σ z x)) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            apply Finset.sum_congr rfl
            intro σ hσ
            exact permutedKernel_reverse modulus M q V shared step K σ τ x z
      _ = _ := by simp only [star_sum]
  rw [hsum]
  ring

/-- For a constant kernel the total normalized pair-permutation
average has total mass 1; this uses both independent M! choices. -/
theorem permutationPairMass_normalized :
    (permutationPairMass M : ℂ) *
      ((Fintype.card (SlotPerm M) : ℂ)^2) = 1 := by
  have hn : ((Nat.factorial M : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero M
  unfold permutationPairMass
  rw [Fintype.card_perm]
  simp only [Fintype.card_fin]
  norm_cast
  field_simp [hn]

end Green64SmallHaar

end

/-! ## GroupPermutedSmallEdge -/

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

/-- One source permutation per small group and one independent target
permutation per group: exactly the source E_i double symmetrization. -/
abbrev GroupPermFamily := (g : G) → SlotPerm M

def groupEdgeAllowedPerm
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (σ τ : GroupPermFamily (G := G) M)
    (x z : GroupState P modulus M) : Prop :=
  ∀ g, edgeAllowedPerm (modulus g) M (shared g) step
    (σ g) (τ g) (x g) (z g)

theorem groupEdgeAllowedPerm_reverse
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (σ τ : GroupPermFamily (G := G) M)
    (x z : GroupState P modulus M) :
    groupEdgeAllowedPerm P modulus M shared step σ τ x z ↔
    groupEdgeAllowedPerm P modulus M shared (-step) τ σ z x := by
  constructor
  · intro h g
    exact (edgeAllowedPerm_reverse (modulus g) M (shared g)
      step (σ g) (τ g) (x g) (z g)).mp (h g)
  · intro h g
    exact (edgeAllowedPerm_reverse (modulus g) M (shared g)
      step (σ g) (τ g) (x g) (z g)).mpr (h g)

/-- A globally pattern-dependent multiplier K may depend on BOTH
source and target group permutation families. Physical edge reversal
conjugates K and exchanges their roles. -/
def reverseGroupPermutationKernel
    (K : GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ) :
    GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ :=
  fun τ σ => star (K σ τ)

noncomputable def groupPermutedKernel
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ)
    (σ τ : GroupPermFamily (G := G) M)
    (x z : GroupState P modulus M) : ℂ :=
  if groupEdgeAllowedPerm P modulus M shared step σ τ x z then
    K σ τ * (groupEdgeScalar P modulus M q V shared x z : ℂ)
  else 0

theorem groupPermutedKernel_reverse
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ)
    (σ τ : GroupPermFamily (G := G) M)
    (x z : GroupState P modulus M) :
    groupPermutedKernel P modulus M q V shared step K σ τ x z =
      star (groupPermutedKernel P modulus M q V shared (-step)
        (reverseGroupPermutationKernel (G := G) M K) τ σ z x) := by
  by_cases h : groupEdgeAllowedPerm P modulus M shared step σ τ x z
  · have hr := (groupEdgeAllowedPerm_reverse P modulus M shared
      step σ τ x z).mp h
    simp only [groupPermutedKernel,h,hr,if_true,
      reverseGroupPermutationKernel,star_mul,star_star]
    rw [groupEdgeScalar_symmetric P modulus M q V shared z x]
    rw [Complex.star_def,Complex.conj_ofReal]
    ring
  · have hr : ¬ groupEdgeAllowedPerm P modulus M shared (-step) τ σ z x := by
      intro hh
      exact h ((groupEdgeAllowedPerm_reverse P modulus M shared
        step σ τ x z).mpr hh)
    simp [groupPermutedKernel,h,hr]

/-- The physical normalization has independent source AND target
permutation factors in EVERY small group, each (M!)^-2. -/
noncomputable def groupPermutationPairMass : ℝ :=
  ∏ g : G, permutationPairMass M

theorem groupPermutationPairMass_positive :
    0 < groupPermutationPairMass (G := G) M := by
  unfold groupPermutationPairMass
  apply Finset.prod_pos
  intro g hg
  exact permutationPairMass_positive M

/-- Normalized all-small-group independent source/target permutation
averaging does not introduce any extra cross-group M! factor. -/
theorem groupPermutationPairMass_normalized :
    (groupPermutationPairMass (G := G) M : ℂ) *
      ((Fintype.card (GroupPermFamily (G := G) M) : ℂ)^2) = 1 := by
  have hcard : Fintype.card (GroupPermFamily (G := G) M) =
      ∏ g : G, Fintype.card (SlotPerm M) := by
    exact Fintype.card_pi
  unfold groupPermutationPairMass
  rw [hcard]
  push_cast
  rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  simp only [permutationPairMass_normalized]
  simp

noncomputable def groupAveragedSmallKernel
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ)
    (x z : GroupState P modulus M) : ℂ :=
  (groupPermutationPairMass (G := G) M : ℂ) *
    (∑ σ : GroupPermFamily (G := G) M,
      ∑ τ : GroupPermFamily (G := G) M,
        groupPermutedKernel P modulus M q V shared step K σ τ x z)

/-- FULL finite all-small-group source E_i double symmetrization:
the averaged complex physical kernel with arbitrary dependence on
both independent permutation FAMILIES reverses exactly to the
conjugate, with no termwise factorial cancellation assumptions. -/
theorem groupAveragedSmallKernel_reverse
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (K : GroupPermFamily (G := G) M → GroupPermFamily (G := G) M → ℂ)
    (x z : GroupState P modulus M) :
    groupAveragedSmallKernel P modulus M q V shared step K x z =
      star (groupAveragedSmallKernel P modulus M q V shared (-step)
        (reverseGroupPermutationKernel (G := G) M K) z x) := by
  unfold groupAveragedSmallKernel
  rw [star_mul]
  have hm :
      star ((groupPermutationPairMass (G := G) M : ℝ) : ℂ) =
        ((groupPermutationPairMass (G := G) M : ℝ) : ℂ) := by
    rw [Complex.star_def,Complex.conj_ofReal]
  rw [hm]
  have hsum :
      (∑ σ : GroupPermFamily (G := G) M, ∑ τ : GroupPermFamily (G := G) M,
        groupPermutedKernel P modulus M q V shared step K σ τ x z) =
      star (∑ τ : GroupPermFamily (G := G) M, ∑ σ : GroupPermFamily (G := G) M,
        groupPermutedKernel P modulus M q V shared (-step)
          (reverseGroupPermutationKernel (G := G) M K) τ σ z x) := by
    calc
      (∑ σ : GroupPermFamily (G := G) M, ∑ τ : GroupPermFamily (G := G) M,
        groupPermutedKernel P modulus M q V shared step K σ τ x z) =
      (∑ τ : GroupPermFamily (G := G) M, ∑ σ : GroupPermFamily (G := G) M,
        groupPermutedKernel P modulus M q V shared step K σ τ x z) :=
          Finset.sum_comm
      _ = (∑ τ : GroupPermFamily (G := G) M, ∑ σ : GroupPermFamily (G := G) M,
        star (groupPermutedKernel P modulus M q V shared (-step)
          (reverseGroupPermutationKernel (G := G) M K) τ σ z x)) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            apply Finset.sum_congr rfl
            intro σ hσ
            exact groupPermutedKernel_reverse P modulus M q V
              shared step K σ τ x z
      _ = _ := by simp only [star_sum]
  rw [hsum]
  ring

end Green64SmallHaar

end

/-! ## PhysicalPermutationSourceAudit -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- A source pattern acts on the lists *between* independently
sampled endpoint permutations. This is the analogue of
SmallPermutedEdge.sameSharedPerm for numerical BIG labels. -/
def orientedBigSharedCopy {P : Type} {M : ℕ}
    (source target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) : Prop :=
  ∀ j ∈ shared, source (sigma j) = target (tau j)

/-- The existing PhysicalEdgeLegal field checks raw canonical
coordinates, and omits sigma/tau from its shared-copy test. -/
def rawBigSharedCopy {P : Type} {M : ℕ}
    (source target : Fin M → P)
    (shared : Finset (Fin M)) : Prop :=
  ∀ j ∈ shared, source j = target j

/-- Witness that raw source-list equality and source-ORIENTED
list equality differ for independently sampled permutations.
This already occurs with distinct labels at both endpoints. -/
theorem raw_and_oriented_shared_copy_not_equivalent :
    ∃ (source target : Fin 2 → Fin 2)
      (shared : Finset (Fin 2))
      (sigma tau : Equiv.Perm (Fin 2)),
      (∀ i : Fin 2, source i = i) ∧
      (∀ i : Fin 2, target i = i) ∧
      rawBigSharedCopy source target shared ∧
      ¬ orientedBigSharedCopy source target shared sigma tau := by
  refine ⟨id, id, {0}, Equiv.swap 0 1, Equiv.refl _, ?_, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro i; rfl
  · simp [rawBigSharedCopy]
  · simp [orientedBigSharedCopy]

end Green64FullPhysicalE

end

