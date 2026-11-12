module

public import Green64.Library.Correlation.Part005
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Weights.Part002
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part001

@[expose] public section

/-!
# Correlation / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryOriginalSmallGroupPhysicalPairing -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
  [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
  [∀ g p, NeZero (smallMod g p)]
variable (M : ℕ)

/-- The fully original SMALL Haar source-to-target physical
pairing over ALL groups, with two independently chosen permuted
SMALL slot families, the identical signed source integer step
for ALL groups, and arbitrary complex coefficients. Literal
SMALL group edge legality is disintegrated into one common
source shared-label tuple and one full translated Haar torus.
No independent-root replacement or unproved analytic bound. -/
theorem memory_original_small_group_physical_pairing
    (shared : SG → Finset (Fin M)) (step : ℤ)
    (σ τ : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (H : Green64SmallHaar.GroupState SP smallMod M →
        Green64SmallHaar.GroupState SP smallMod M → ℂ) :
    (∑ xs : Green64SmallHaar.GroupState SP smallMod M,
       ∑ zs : Green64SmallHaar.GroupState SP smallMod M,
         if Green64SmallHaar.groupEdgeAllowedPerm
            SP smallMod M shared step σ τ xs zs then
            H xs zs else 0) =
    ∑ d : (g : SG) → ↥(shared g) → SP g,
       ∑ y : Green64SmallHaar.GroupTorus SP smallMod,
         ∑ xs ∈ memoryOriginalSmallGroupPermutedFibre
           SP smallMod M shared σ d y,
           ∑ zs ∈ memoryOriginalSmallGroupPermutedFibre
             SP smallMod M shared τ d
               (Green64SmallHaar.groupTranslate
                 SP smallMod step y),
             H xs zs := by
  classical
  let a := memoryOriginalSmallGroupSharedLabels
    SP smallMod M shared σ
  let b := memoryOriginalSmallGroupSharedLabels
    SP smallMod M shared τ
  let r := memoryOriginalSmallGroupResidue SP smallMod M
  let tr := Green64SmallHaar.groupTranslate SP smallMod step
  have h := memory_finite_two_endpoint_conditioning
    a b r r tr H
  convert h using 1
  · apply Finset.sum_congr rfl
    intro xs _
    apply Finset.sum_congr rfl
    intro zs _
    have hc := memory_original_small_group_edge_conditional_iff
      SP smallMod M shared step σ τ xs zs
    by_cases he : Green64SmallHaar.groupEdgeAllowedPerm
       SP smallMod M shared step σ τ xs zs
    · simp [he, hc.mp he, a, b, r, tr]
    · have hn : ¬(a xs = b zs ∧ r zs = tr (r xs)) :=
        fun hh => he (hc.mpr hh)
      simp [he, hn, a, b, r, tr]
  · rfl
end Green64FullPhysicalE

end

end

/-! ## MemorySmallGroupConditioningWeight -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable (J ell : ℕ)

/-- Genuine product of original conditional SMALL mark fibres. -/
def memorySmallGroupConditionalFibre
    (shared : SG → Finset (Fin (J+ell)))
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    Finset (Green64SmallHaar.GroupState SP smallMod (J+ell)) :=
  Fintype.piFinset (fun g =>
    memorySmallConditionalFibre (smallMod g) (J+ell)
      (shared g) (d g) (y g))

theorem memory_small_group_fibre_card
    (shared : SG → Finset (Fin (J+ell)))
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    (memorySmallGroupConditionalFibre SP smallMod J ell shared d y).card =
    ∏ g : SG, (memorySmallConditionalFibre (smallMod g)
      (J+ell) (shared g) (d g) (y g)).card := by
  exact Fintype.card_piFinset _

/-- Tensor of the original SMALL conditioning q/V weights. -/
def memorySmallGroupConditionalRatio
    (q : ℝ) (Vs : SG → ℝ)
    (y : Green64SmallHaar.GroupTorus SP smallMod) : ℝ :=
  ∏ g : SG, memorySmallConditionalRatio (smallMod g) J ell
    q (Vs g) (y g)

def memorySmallGroupConditioningConstant
    (q : ℝ) (Vs : SG → ℝ) : ℝ :=
  ∏ g : SG, (ell.factorial:ℝ) /
    ((1-q)^(ell+1) * (Vs g)^ell)
/-- Exact output-fibre multiplicity and q damping across ALL SMALL
groups. The constant depends on ell, q, Vs and |SG|, not shared J. -/
theorem memory_small_group_conditional_fibre_weight
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g, (shared g).card = J)
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    memorySmallGroupConditionalRatio SP smallMod J ell q Vs y *
      ((memorySmallGroupConditionalFibre SP smallMod J ell shared d y).card : ℝ)
      ≤ memorySmallGroupConditioningConstant (SG := SG) ell q Vs := by
  have hprod (g : SG) :
      0 ≤ memorySmallConditionalRatio (smallMod g) J ell q (Vs g) (y g) := by
    unfold memorySmallConditionalRatio
    have hv : 0 < Vs g := hVs g
    positivity
  rw [memory_small_group_fibre_card]
  simp only [Nat.cast_prod]
  unfold memorySmallGroupConditionalRatio memorySmallGroupConditioningConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro g _
    exact mul_nonneg (hprod g) (Nat.cast_nonneg _)
  · intro g _
    exact memory_small_conditional_fibre_weight_bound
      (smallMod g) J ell q (Vs g) hq hq1 (hVs g)
      (shared g) (hshared g) (d g) (y g)
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallGroupEndpointHalf -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
  [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
  [∀ g p, NeZero (smallMod g p)]
variable (J ell : ℕ)

/-- True product SMALL Haar one-endpoint half-kernel for
the exact source row, with independent prime groups but
no independent output replacement. -/
noncomputable def memoryOriginalSmallGroupPhysicalEndpointHalf
    (q : ℝ) (Vs : SG → ℝ)
    (y : Green64SmallHaar.GroupTorus SP smallMod) : ℝ :=
  ∏ g : SG, memoryOriginalSmallPhysicalEndpointHalf
    (smallMod g) J ell q (Vs g) (y g)
/-- Squared physical SMALL source endpoint half equals EXACTLY
the already certified original P_d group conditional weight,
with no hidden multiplicity, Haar or factorial factor. -/
theorem memory_original_small_group_endpoint_half_sq
    (q : ℝ) (hq : 0 ≤ q)
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    (memoryOriginalSmallGroupPhysicalEndpointHalf
        SP smallMod J ell q Vs y)^2 =
    memorySmallGroupConditionalRatio SP smallMod J ell q Vs y := by
  unfold memoryOriginalSmallGroupPhysicalEndpointHalf
    memorySmallGroupConditionalRatio
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro g hg
  exact memory_original_small_physical_endpoint_half_sq
    (smallMod g) J ell q (Vs g) hq (hVs g) (y g)

/-- Original small GROUP physical E_i source edge scalar is
exactly a product of source and target half-kernels on the
ENTIRE Haar group torus. Holds for both independent sampled
endpoint permutations and all shared J slots. -/
theorem memory_original_small_group_edge_scalar_half_exact
    (q : ℝ) (hq : 0 ≤ q)
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g, (shared g).card = J)
    (x z : Green64SmallHaar.GroupState SP smallMod (J+ell)) :
    Green64SmallHaar.groupEdgeScalar SP smallMod (J+ell)
        q Vs shared x z =
    memoryOriginalSmallGroupPhysicalEndpointHalf
      SP smallMod J ell q Vs
      (fun g => Green64SmallHaar.residues (smallMod g)
         (J+ell) (x g)) *
    memoryOriginalSmallGroupPhysicalEndpointHalf
      SP smallMod J ell q Vs
      (fun g => Green64SmallHaar.residues (smallMod g)
         (J+ell) (z g)) := by
  unfold Green64SmallHaar.groupEdgeScalar
    memoryOriginalSmallGroupPhysicalEndpointHalf
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  exact memory_original_small_edge_scalar_half_exact
    (smallMod g) J ell q (Vs g) hq (hVs g)
    (shared g) (hshared g) (x g) (z g)
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallPhysicalKernelHalf -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
  [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
  [∀ g p, NeZero (smallMod g p)]
variable (J ell : ℕ)

/-- Full ORIGINAL group-SMALL oriented PHYSICAL signed kernel,
with the same two independent endpoint permutations and arbitrary
nonconstant global signed K, factors as two exact P_d endpoint
half-masses and the unchanged physical SMALL admissibility test.
No auxiliary output independence or norm hypothesis. -/
theorem memory_original_group_small_physical_kernel_half
    (q : ℝ) (hq : 0 ≤ q)
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g, (shared g).card = J)
    (step : ℤ)
    (K : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) →
         Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) → ℂ)
    (σ τ : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (xs zs : Green64SmallHaar.GroupState SP smallMod (J+ell)) :
    Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
      q Vs shared step K σ τ xs zs =
    if Green64SmallHaar.groupEdgeAllowedPerm SP smallMod
         (J+ell) shared step σ τ xs zs then
      K σ τ *
       (memoryOriginalSmallGroupPhysicalEndpointHalf
          SP smallMod J ell q Vs
          (memoryOriginalSmallGroupResidue
             SP smallMod (J+ell) xs) : ℂ) *
       (memoryOriginalSmallGroupPhysicalEndpointHalf
          SP smallMod J ell q Vs
          (memoryOriginalSmallGroupResidue
             SP smallMod (J+ell) zs) : ℂ)
    else 0 := by
  unfold Green64SmallHaar.groupPermutedKernel
  by_cases he : Green64SmallHaar.groupEdgeAllowedPerm
      SP smallMod (J+ell) shared step σ τ xs zs
  · simp only [if_pos he]
    rw [memory_original_small_group_edge_scalar_half_exact
      SP smallMod J ell q hq Vs hVs shared hshared xs zs]
    have hx :
        (fun g : SG => Green64SmallHaar.residues
            (smallMod g) (J+ell) (xs g)) =
        memoryOriginalSmallGroupResidue
          SP smallMod (J+ell) xs := rfl
    have hz :
        (fun g : SG => Green64SmallHaar.residues
            (smallMod g) (J+ell) (zs g)) =
        memoryOriginalSmallGroupResidue
          SP smallMod (J+ell) zs := rfl
    rw [hx, hz]
    push_cast
    ring
  · simp [he]
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallPhysicalBilinearP -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
    [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
    [∀ g p, NeZero (smallMod g p)]
variable (J ell : ℕ)

/-- TRUE original physical SMALL P_d map for an independently
sampled source endpoint permutation family: conditional sum
over genuine ordered mark states, multiplied by exactly
one square root of the original conditional ratio. -/
noncomputable def memoryOriginalSmallPermutedHalfMap
    (q : ℝ) (Vs : SG → ℝ)
    (shared : SG → Finset (Fin (J+ell)))
    (σ : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod)
    (w : Green64SmallHaar.GroupState SP smallMod (J+ell) → ℂ) : ℂ :=
  (memoryOriginalSmallGroupPhysicalEndpointHalf
      SP smallMod J ell q Vs y : ℂ) *
  (∑ xs ∈ memoryOriginalSmallGroupPermutedFibre
       SP smallMod (J+ell) shared σ d y, w xs)
/-- The exact ORIGINAL signed, independently double-permuted
SMALL physical E kernel bilinear pairing factors as two
physical P_d maps over a shared tuple d and full true Haar
residue y, with target translation by ORIGINAL signed step.
The original global K can be arbitrary nonconstant in σ,τ.
No independent BIG output or ideal operator is assumed. -/
theorem memory_original_small_source_bilinear_P_exact
    (q : ℝ) (hq : 0 ≤ q)
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g, (shared g).card = J)
    (step : ℤ)
    (K : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) →
         Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) → ℂ)
    (σ τ : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (u v : Green64SmallHaar.GroupState SP smallMod (J+ell) → ℂ) :
    (∑ xs : Green64SmallHaar.GroupState SP smallMod (J+ell),
       ∑ zs : Green64SmallHaar.GroupState SP smallMod (J+ell),
         Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
            q Vs shared step K σ τ xs zs *
         u xs * v zs) =
    K σ τ * (∑ d : (g : SG) → ↥(shared g) → SP g,
      ∑ y : Green64SmallHaar.GroupTorus SP smallMod,
        memoryOriginalSmallPermutedHalfMap
          SP smallMod J ell q Vs shared σ d y u *
        memoryOriginalSmallPermutedHalfMap
          SP smallMod J ell q Vs shared τ d
          (Green64SmallHaar.groupTranslate SP smallMod step y) v) := by
  let tr := Green64SmallHaar.groupTranslate SP smallMod step
  let S := memoryOriginalSmallGroupPermutedFibre SP smallMod
    (J+ell) shared σ
  let T := memoryOriginalSmallGroupPermutedFibre SP smallMod
    (J+ell) shared τ
  let A := memoryOriginalSmallGroupPhysicalEndpointHalf
    SP smallMod J ell q Vs
  have hchange (xs zs : Green64SmallHaar.GroupState
      SP smallMod (J+ell)) :
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
          q Vs shared step K σ τ xs zs * u xs * v zs =
      if Green64SmallHaar.groupEdgeAllowedPerm
          SP smallMod (J+ell) shared step σ τ xs zs then
        K σ τ *
          (Green64SmallHaar.groupEdgeScalar SP smallMod
            (J+ell) q Vs shared xs zs : ℂ) * u xs * v zs
      else 0 := by
    unfold Green64SmallHaar.groupPermutedKernel
    split_ifs <;> ring
  have hphysical := memory_original_small_group_physical_pairing
    SP smallMod (J+ell) shared step σ τ
    (fun xs zs =>
      K σ τ *
       (Green64SmallHaar.groupEdgeScalar SP smallMod (J+ell)
         q Vs shared xs zs : ℂ) * u xs * v zs)
  calc
    _ = (∑ xs : Green64SmallHaar.GroupState SP smallMod
          (J+ell),
      ∑ zs : Green64SmallHaar.GroupState SP smallMod
          (J+ell),
        if Green64SmallHaar.groupEdgeAllowedPerm SP smallMod
              (J+ell) shared step σ τ xs zs then
          K σ τ *
            (Green64SmallHaar.groupEdgeScalar SP smallMod
              (J+ell) q Vs shared xs zs : ℂ) * u xs * v zs
        else 0) := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro zs _
      exact hchange xs zs
    _ = (∑ d : (g : SG) → ↥(shared g) → SP g,
      ∑ y : Green64SmallHaar.GroupTorus SP smallMod,
        ∑ xs ∈ S d y,
        ∑ zs ∈ T d (tr y),
          K σ τ *
           (Green64SmallHaar.groupEdgeScalar SP smallMod
              (J+ell) q Vs shared xs zs : ℂ) * u xs * v zs) :=
          hphysical
    _ = (∑ d : (g : SG) → ↥(shared g) → SP g,
      ∑ y : Green64SmallHaar.GroupTorus SP smallMod,
        K σ τ *
        (A y * ∑ xs ∈ S d y, u xs) *
        (A (tr y) * ∑ zs ∈ T d (tr y), v zs)) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      have hr (xs : Green64SmallHaar.GroupState SP smallMod
              (J+ell)) (hx : xs ∈ S d y)
          (zs : Green64SmallHaar.GroupState SP smallMod
              (J+ell)) (hz : zs ∈ T d (tr y)) :
          Green64SmallHaar.groupEdgeScalar SP smallMod
            (J+ell) q Vs shared xs zs = A y * A (tr y) := by
        have hx0 : memoryOriginalSmallGroupResidue
            SP smallMod (J+ell) xs = y := by
          have hv : memoryOriginalSmallGroupSharedLabels
             SP smallMod (J+ell) shared σ xs = d ∧
             memoryOriginalSmallGroupResidue SP smallMod
                (J+ell) xs = y := by
            simpa only [S, memoryOriginalSmallGroupPermutedFibre,
              memoryFiniteConditionalFibre, Finset.mem_filter,
              Finset.mem_univ, true_and] using hx
          exact hv.2
        have hz0 : memoryOriginalSmallGroupResidue
            SP smallMod (J+ell) zs = tr y := by
          have hv : memoryOriginalSmallGroupSharedLabels
             SP smallMod (J+ell) shared τ zs = d ∧
             memoryOriginalSmallGroupResidue SP smallMod
                (J+ell) zs = tr y := by
            simpa only [T, memoryOriginalSmallGroupPermutedFibre,
              memoryFiniteConditionalFibre, Finset.mem_filter,
              Finset.mem_univ, true_and] using hz
          exact hv.2
        have hh := memory_original_small_group_edge_scalar_half_exact
           SP smallMod J ell q hq Vs hVs shared hshared xs zs
        have hxfun :
            (fun g : SG => Green64SmallHaar.residues
              (smallMod g) (J+ell) (xs g)) =
            memoryOriginalSmallGroupResidue SP smallMod (J+ell) xs := rfl
        have hzfun :
            (fun g : SG => Green64SmallHaar.residues
              (smallMod g) (J+ell) (zs g)) =
            memoryOriginalSmallGroupResidue SP smallMod (J+ell) zs := rfl
        rw [hxfun, hzfun, hx0, hz0] at hh
        exact hh
      calc
        _ = ∑ xs ∈ S d y, ∑ zs ∈ T d (tr y),
          K σ τ * ((A y : ℂ) * (A (tr y) : ℂ)) *
            u xs * v zs := by
          apply Finset.sum_congr rfl
          intro xs hx
          apply Finset.sum_congr rfl
          intro zs hz
          rw [hr xs hx zs hz]
          push_cast
          ring
        _ = _ := by
          exact memory_finite_original_two_endpoint_tensor
            (S d y) (T d (tr y)) u v (K σ τ) (A y) (A (tr y))
    _ = _ := by
      unfold memoryOriginalSmallPermutedHalfMap
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
end Green64FullPhysicalE

end

end

/-! ## PhysicalGhostBirthGroupFacts -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Every fresh OLD-free birth of a concrete physical G witness
is in its actual all-BIG-group numerical birth list. -/
theorem physical_G_fresh_group_mem
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (g : BG) (j : Fin ((c g).2.1.val)) :
    bigMod g (((c g).2.2 j).1) ∈
      physicalGhostFreshBirths SP smallMod BP bigMod M cap x c := by
  unfold physicalGhostFreshBirths
  apply List.mem_flatMap.mpr
  refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), ?_⟩
  apply List.mem_map.mpr
  exact ⟨(c g).2.2 j, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩

/-- One numerical Nodup test on the original all-group G birth
witness automatically enforces per-group ordered prime uniqueness,
without an extra local assumption or quotienting ghost batches. -/
theorem physical_G_fresh_group_nodup
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (seen : Finset ℕ)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod
       M cap x seen c)
    (g : BG) :
    ((List.ofFn ((c g).2.2)).map
      (fun a => bigMod g a.1)).Nodup := by
  exact (List.nodup_flatMap.mp hb.1).1 g
    (Finset.mem_toList.mpr (Finset.mem_univ g))

/-- The G_i global seen-prime condition rules out every OLD
numerical label from its genuine group-indexed fresh batch. -/
theorem physical_G_fresh_group_not_seen
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (seen : Finset ℕ)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod
       M cap x seen c)
    (g : BG) (j : Fin ((c g).2.1.val)) :
    bigMod g (((c g).2.2 j).1) ∉ seen := by
  intro hseen
  have hm := physical_G_fresh_group_mem
    SP smallMod BP bigMod M cap x c g j
  exact (Finset.disjoint_left.mp hb.2 hseen)
    (List.mem_toFinset.mpr hm)

end Green64FullPhysicalE

end

/-! ## PhysicalGhostActualPendingUnique -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- An actual NONZERO original physical G_i witness preserves
distinct pending prime labels once globally new ghost births
avoid the old seen set. The output Fock representative is the
one selected by the real source ghost coefficient. -/
theorem physical_nonzero_G_output_pending_unique
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0)
    (seen : Finset ℕ)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod
      M cap x seen c)
    (g : BG)
    (hOld : ((Green64Fock.fockToList ((x.2 g).2)).map
      (fun a => a.1)).Nodup)
    (hOldSeen : ∀ a ∈
      (Green64Fock.fockToList ((x.2 g).2)).map
        (fun z => z.1), bigMod g a ∈ seen) :
    ((Green64Fock.fockToList ((y.2 g).2)).map
      (fun z => z.1)).Nodup := by
  have hOutput :=
    (physical_nonzero_ghost_witness_is_operational
      SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c hterm).2 g
  have hFN := physical_G_fresh_group_nodup
    SP smallMod BP bigMod M cap x c seen hb g
  have hFP :
      ((List.ofFn ((c g).2.2)).map (fun a => a.1)).Nodup := by
    apply List.Nodup.of_map (bigMod g)
    simpa [List.map_map, Function.comp_def] using hFN
  have hSep :
      ∀ a ∈ (Green64Fock.fockToList ((x.2 g).2)).map
        (fun z => z.1),
      ∀ v ∈ (List.ofFn ((c g).2.2)).map (fun z => z.1),
      a ≠ v := by
    intro a ha v hv heq
    rcases List.mem_map.mp hv with ⟨atom,hatom,hav⟩
    rcases List.mem_ofFn.mp hatom with ⟨j,hj⟩
    have hn := physical_G_fresh_group_not_seen
      SP smallMod BP bigMod M cap x c seen hb g j
    have he : bigMod g (((c g).2.2 j).1) =
        bigMod g a := by
      apply congrArg (bigMod g)
      calc
        (((c g).2.2 j).1) = v := by
          rw [hj]
          exact hav
        _ = a := heq.symm
    exact hn (he ▸ hOldSeen a ha)
  have hAfter := original_ghost_afterGhost_prime_nodup
    (bigMod g)
    (Green64Fock.fockToList ((x.2 g).2))
    (c g).1.1 (c g).2.2 hOld hFP hSep
  rw [← hOutput]
  exact hAfter

end Green64FullPhysicalE

end

/-! ## PhysicalGhostActualConservation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- An actual G_i witness cannot manufacture OLD primes: any output
pending prime is either a surviving incoming OLD prime or a newly
born ghost prime from the physical birth tuple. -/
theorem original_ghost_output_prime_origin
    (old : List (Green64Fock.Atom P modulus))
    (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → Green64Fock.Atom P modulus)
    (v : P)
    (hv : v ∈ (Green64MemoryGhostOp.afterGhost old A fresh).map
      (fun a => a.1)) :
    v ∈ old.map (fun a => a.1) ∨
      ∃ j : Fin b, v = (fresh j).1 := by
  simp only [Green64MemoryGhostOp.afterGhost,
    List.map_append, List.mem_append] at hv
  rcases hv with hvOld | hvFresh
  · rcases List.mem_map.mp hvOld with ⟨atom, hatom, rfl⟩
    rcases List.mem_map.mp hatom with ⟨j,hj,rfl⟩
    left
    exact List.mem_map.mpr
      ⟨old.get j, List.get_mem old j, rfl⟩
  · rcases List.mem_map.mp hvFresh with ⟨atom,hatom,rfl⟩
    rcases List.mem_ofFn.mp hatom with ⟨j,rfl⟩
    exact Or.inr ⟨j,rfl⟩
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Full TRUE source G_i event: after a nonzero OLD-deletion+ghost
witness with the global birth marker, each BIG output active list
remains unique, every pending particle is unique, ACTIVE/PENDING
cannot collide, and both occupy old-or-new numerical birth sets.
These are the G conditions needed for literal source histories. -/
theorem physical_nonzero_G_full_output_unique
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0)
    (seen : Finset ℕ)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod
      M cap x seen c)
    (g : BG)
    (hSrc : Function.Injective ((x.2 g).1))
    (hOld : ((Green64Fock.fockToList ((x.2 g).2)).map
      (fun a => a.1)).Nodup)
    (hSep : ∀ (j : Fin M) (r : Fin ((x.2 g).2.1.val)),
      (x.2 g).1 j ≠ ((x.2 g).2.2 r).1)
    (hSeenActive : ∀ j : Fin M,
      bigMod g ((x.2 g).1 j) ∈ seen)
    (hSeenOld : ∀ v ∈
      (Green64Fock.fockToList ((x.2 g).2)).map
        (fun a => a.1), bigMod g v ∈ seen) :
    Function.Injective ((y.2 g).1) ∧
      ((Green64Fock.fockToList ((y.2 g).2)).map
        (fun a => a.1)).Nodup ∧
      (∀ j : Fin M, ∀ v : BP g,
        v ∈ (Green64Fock.fockToList ((y.2 g).2)).map
          (fun a => a.1) →
        (y.2 g).1 j ≠ v) ∧
      (∀ j : Fin M, bigMod g ((y.2 g).1 j) ∈ seen) ∧
      (∀ v ∈ (Green64Fock.fockToList ((y.2 g).2)).map
          (fun a => a.1),
        bigMod g v ∈ seen ∪
          (physicalGhostFreshBirths SP smallMod BP bigMod
            M cap x c).toFinset) := by
  have hw := physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod M cap q rho N i Vbig muBig x y c hterm
  have hsrcEq : (x.2 g).1 = (y.2 g).1 := hw.1.2 g
  have hout := hw.2 g
  have hPending := physical_nonzero_G_output_pending_unique
    SP smallMod BP bigMod M cap q rho N i Vbig muBig
    x y c hterm seen hb g hOld hSeenOld
  have horigin (v : BP g)
      (hv : v ∈ (Green64Fock.fockToList ((y.2 g).2)).map
        (fun a => a.1)) :
      v ∈ (Green64Fock.fockToList ((x.2 g).2)).map
          (fun a => a.1) ∨
      ∃ j : Fin ((c g).2.1.val), v = ((c g).2.2 j).1 := by
    rw [← hout] at hv
    exact original_ghost_output_prime_origin (bigMod g)
      (Green64Fock.fockToList ((x.2 g).2))
      (c g).1.1 (c g).2.2 v hv
  have hOldIndex (v : BP g)
      (hv : v ∈ (Green64Fock.fockToList ((x.2 g).2)).map
         (fun a => a.1)) :
      ∃ r : Fin ((x.2 g).2.1.val), v = ((x.2 g).2.2 r).1 := by
    rcases List.mem_map.mp hv with ⟨atom,hm,he⟩
    rcases List.mem_ofFn.mp (by
      simpa [Green64Fock.fockToList] using hm) with ⟨r,hr⟩
    refine ⟨r, ?_⟩
    rw [← hr] at he
    exact he.symm
  refine ⟨?_, hPending, ?_, ?_, ?_⟩
  · rw [← hsrcEq]
    exact hSrc
  · intro j v hv heq
    rcases horigin v hv with hprevious | ⟨r,rfl⟩
    · rcases hOldIndex v hprevious with ⟨r,hr⟩
      have he : (x.2 g).1 j = ((x.2 g).2.2 r).1 := by
        rw [← hsrcEq] at heq
        exact heq.trans hr
      exact (hSep j r) he
    · have hnum := physical_G_fresh_group_not_seen
        SP smallMod BP bigMod M cap x c seen hb g r
      apply hnum
      rw [← hsrcEq] at heq
      rw [← heq]
      exact hSeenActive j
  · intro j
    rw [← hsrcEq]
    exact hSeenActive j
  · intro v hv
    rcases horigin v hv with hprevious | ⟨r,rfl⟩
    · exact Finset.mem_union_left
        (physicalGhostFreshBirths SP smallMod BP bigMod
          M cap x c).toFinset (hSeenOld v hprevious)
    · apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      exact physical_G_fresh_group_mem
        SP smallMod BP bigMod M cap x c g r

end Green64FullPhysicalE

end

/-! ## PhysicalRealGTerminalVacuum -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The ACTUAL nonzero G_N physical witness ending in the Fock
vacuum has no new ghost birth in any BIG group and terminates
ALL OLD pending indices; this is derived from the operational
G coefficient, not an assumed final-lifespan boundary. -/
theorem real_nonzero_G_terminal_vacuum
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod
      M cap q rho N i Vbig muBig x y c ≠ 0)
    (hZero : ∀ g : BG,
      Green64Fock.fockMultiset ((y.2 g).2) = 0) :
    ∀ g : BG, (c g).1.1 = Finset.univ ∧ (c g).2.1.val = 0 := by
  intro g
  have hOp := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod M cap q rho N i Vbig muBig
    x y c hterm).2 g
  have hlen := congrArg Multiset.card (hZero g)
  have hList : Green64Fock.fockToList ((y.2 g).2) = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using hlen
  have hh : Green64MemoryGhostOp.afterGhost
      (Green64Fock.fockToList ((x.2 g).2))
      (c g).1.1 (c g).2.2 = [] := hOp.trans hList
  exact (original_ghost_empty_output_exact
    (Green64Fock.fockToList ((x.2 g).2))
    (c g).1.1 (c g).2.2).mp hh

end Green64FullPhysicalE

end

/-! ## PhysicalSourceBirthMarkedE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- At time zero the original big-active labels are FIRST births.
They are numerical prime values, not pending residues or
auxiliary factors, and repeat even within one group before filtering. -/
noncomputable def physicalInitialBirths
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :
    List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (Finset.univ : Finset (Fin (J + ell))).toList.map
      (fun i => bigMod g ((x.2 g).1 i)))
/-- The ONLY new physical E_i births are fresh target slots:
not shared slots, not OLD pending promotions, not stores,
not any auxiliary D free label. Respect the sampled independent
TARGET permutation when reading the numerical source prime. -/
noncomputable def physicalEFreshBirths
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (freshTargetSlots (J + ell)
      (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.tauBig g)
      ((z.2.2.bigChoice g).2.2.1)).toList.map
      (fun j =>
        bigMod g ((z.2.2.bigChoice g).1 (z.2.2.tauBig g j))))

/-- Global distinct-birth test against ALL earlier birth values;
it also excludes collisions WITHIN the current fresh batch.
It is a PATH indicator and is not part of the original E row. -/
def physicalFreshBatchEligible
    (seen : Finset ℕ)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) : Prop :=
  (physicalEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).Nodup ∧
    Disjoint seen
      (physicalEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset

/-- Decorated physical E branch with the REAL global set
of births seen before the transition. No information about
fresh births is lost by first grouping output multisets. -/
noncomputable def physicalBirthMarkedE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) : ℂ :=
  ∑ z ∈ legalSourcePhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    if physicalFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns
        seen z then
      sourcePhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x z *
      F (sourcePhysicalOutput SP smallMod BP bigMod J ell m cap
        patterns x orientation k z)
        (seen ∪ (physicalEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).toFinset)
    else 0
/-- Only the true new E fresh draws enter the seen-prime set.
A stored or promoted OLD particle is never counted a second time,
and auxiliary free D draws are never marked as births. -/
theorem physicalBirthMarkedE_no_new_fresh_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (hzero : ∀ z ∈ legalSourcePhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
      physicalEFreshBirths SP smallMod BP bigMod J ell m cap patterns z = []) :
    physicalBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k x seen F =
    fullSourcePhysicalE SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k x
      (fun y => F y seen) := by
  unfold physicalBirthMarkedE fullSourcePhysicalE
  apply Finset.sum_congr rfl
  intro z hz
  rw [hzero z hz]
  simp [physicalFreshBatchEligible,hzero z hz]

end Green64FullPhysicalE

end

/-! ## PhysicalGlobalBirthCondition -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Exact list/finite-set reformulation, valid even when old active or
pending prime VALUES repeat before the final distinctness filter. -/
theorem physical_list_nodup_append_iff_disjoint
    (a b : List ℕ) :
    (a ++ b).Nodup ↔
      a.Nodup ∧ b.Nodup ∧ Disjoint a.toFinset b.toFinset := by
  classical
  rw [List.nodup_append, Finset.disjoint_iff_ne]
  simp only [List.mem_toFinset]

/-- Two chronological REAL birth batches obey the pair of online
eligibility checks exactly when their complete concatenation does
not repeat a numerical prime. The order of the events matters. -/
theorem physical_two_batches_global_nodup
    (past ghosts newborn : List ℕ) (hpast : past.Nodup) :
    (ghosts.Nodup ∧ Disjoint past.toFinset ghosts.toFinset) ∧
      (newborn.Nodup ∧
        Disjoint (past.toFinset ∪ ghosts.toFinset) newborn.toFinset) ↔
      (past ++ ghosts ++ newborn).Nodup := by
  classical
  rw [physical_list_nodup_append_iff_disjoint]
  rw [physical_list_nodup_append_iff_disjoint]
  simp only [List.toFinset_append, hpast, true_and]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The ORIGINAL witness-level ghost G_i and fresh-active E_i
global birth marker is a single Nodup check on all chronological
numerical PRIME births, including the initial active list.
No auxiliary-D draw, store or OLD promotion enters either batch. -/
theorem physical_GE_witness_birth_marker_exact
    (past : List ℕ) (hpast : past.Nodup)
    (xG : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (gWitness : FullGhostWitness SP smallMod BP bigMod
      (J + ell) cap xG)
    (xE : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (eChoice : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns xE) :
    (physicalGhostBatchEligible SP smallMod BP bigMod
      (J + ell) cap xG past.toFinset gWitness ∧
     physicalFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns
      (past.toFinset ∪ (physicalGhostFreshBirths
        SP smallMod BP bigMod (J + ell) cap xG gWitness).toFinset)
      eChoice) ↔
    (past ++
      physicalGhostFreshBirths SP smallMod BP bigMod
        (J + ell) cap xG gWitness ++
      physicalEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns eChoice).Nodup := by
  classical
  simpa only [physicalGhostBatchEligible,
    physicalFreshBatchEligible] using
    (physical_two_batches_global_nodup past
      (physicalGhostFreshBirths SP smallMod BP bigMod
        (J + ell) cap xG gWitness)
      (physicalEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns eChoice) hpast)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedBirthMarkedE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exactly those fresh target labels in the pattern's unshared
slots not occupied by promoted OLD particles. These are the
only E_i numerical prime births and are read AFTER tau. -/
noncomputable def orientedEFreshBirths
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (orientedFresh (J + ell)
      (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1)).toList.map
      (fun j => bigMod g
        ((z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j))))

def orientedEFreshBatchEligible
    (seen : Finset ℕ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) : Prop :=
  (orientedEFreshBirths SP smallMod BP bigMod
    J ell m cap patterns z).Nodup ∧
  Disjoint seen
    (orientedEFreshBirths SP smallMod BP bigMod
      J ell m cap patterns z).toFinset

/-- The correct source-oriented physical E_i witness sum with its
one global distinct-birth marker. Auxiliary labels and OLD
stores/promotions do not count as new births. -/
noncomputable def physicalOrientedBirthMarkedE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    if orientedEFreshBatchEligible SP smallMod BP bigMod
        J ell m cap patterns seen z then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
        J ell m cap patterns x orientation k z)
        (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).toFinset)
    else 0

/-- The corrected source-permutation-aware E_i birth test is
equivalent to global chronological Nodup when appended to the
actual ghost G_i batch of the same visit. -/
theorem physical_oriented_GE_births_global_exact
    (past : List ℕ) (hpast : past.Nodup)
    (xG : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J + ell) cap xG)
    (xE : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns xE) :
    (physicalGhostBatchEligible SP smallMod BP bigMod
        (J + ell) cap xG past.toFinset c ∧
      orientedEFreshBatchEligible SP smallMod BP bigMod
        J ell m cap patterns
        (past.toFinset ∪ (physicalGhostFreshBirths SP smallMod
          BP bigMod (J + ell) cap xG c).toFinset) z) ↔
      (past ++ physicalGhostFreshBirths SP smallMod BP bigMod
        (J + ell) cap xG c ++
        orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).Nodup := by
  classical
  simpa only [physicalGhostBatchEligible,
    orientedEFreshBatchEligible] using
    (physical_two_batches_global_nodup past
      (physicalGhostFreshBirths SP smallMod BP bigMod
        (J + ell) cap xG c)
      (orientedEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns z) hpast)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedBirthTargetNodup -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- A genuine source-oriented BIG fresh slot appears exactly in the
one global numerical-prime birth list, BEFORE output Fock grouping. -/
theorem oriented_E_fresh_member_global_birth
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (g : BG) (j : Fin (J+ell))
    (hj : j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1)) :
    bigMod g ((z.2.2.1.bigChoice g).1
      (z.2.2.1.tauBig g j)) ∈
      orientedEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns z := by
  unfold orientedEFreshBirths
  apply List.mem_flatMap.mpr
  refine ⟨g, ?_, ?_⟩
  · exact Finset.mem_toList.mpr (Finset.mem_univ g)
  · apply List.mem_map.mpr
    exact ⟨j, Finset.mem_toList.mpr hj, rfl⟩

/-- Global numerical birth eligibility makes every independent
per-group fresh-integration tuple injective in its oriented slots.
This is not an additional per-group distinctness assumption. -/
theorem oriented_E_fresh_group_injective
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (seen : Finset ℕ)
    (hbatch : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z)
    (g : BG) :
    ∀ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1),
      ∀ l ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1),
      (z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j) =
        (z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g l) →
      j = l := by
  have hnodup :
      ((orientedFresh (J+ell)
          (sourceBigShared J ell m (patterns z.1) g)
          ((z.2.2.1.bigChoice g).2.2.1)).toList.map
            (fun j => bigMod g
              ((z.2.2.1.bigChoice g).1
                (z.2.2.1.tauBig g j)))).Nodup := by
    exact (List.nodup_flatMap.mp hbatch.1).1 g
      (Finset.mem_toList.mpr (Finset.mem_univ g))
  intro j hj l hl he
  exact List.inj_on_of_nodup_map hnodup
    (Finset.mem_toList.mpr hj)
    (Finset.mem_toList.mpr hl)
    (congrArg (bigMod g) he)

/-- If every old active/pending prime was already born, the actual
GLOBAL E fresh-birth eligibility excludes collision with either
pre-existing pool, not just with births in the same new batch. -/
theorem oriented_E_fresh_not_seen
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (seen : Finset ℕ)
    (hbatch : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z)
    (g : BG) (j : Fin (J+ell))
    (hj : j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1)) :
    bigMod g ((z.2.2.1.bigChoice g).1
      (z.2.2.1.tauBig g j)) ∉ seen := by
  intro hseen
  have hmem := oriented_E_fresh_member_global_birth
    SP smallMod BP bigMod J ell m cap patterns x z g j hj
  have hh := (Finset.disjoint_left.mp hbatch.2) hseen
  exact hh (List.mem_toFinset.mpr hmem)
/-- SOURCE-EXACT TARGET NODUP under the actual physical numerical
birth marker, not an independently assumed fresh-label condition.
A source active+OLD distinct state with all its primes in `seen`
remains target-active distinct after every legal oriented E edge. -/
theorem oriented_actual_E_target_injective
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)
    (seen : Finset ℕ)
    (hbatch : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z)
    (g : BG)
    (hSrc : Function.Injective ((x.2 g).1))
    (hOld : Function.Injective
      (fun r : Fin ((x.2 g).2.1.val) => ((x.2 g).2.2 r).1))
    (hSep : ∀ (j : Fin (J+ell))
      (r : Fin ((x.2 g).2.1.val)),
      (x.2 g).1 j ≠ ((x.2 g).2.2 r).1)
    (hSeenActive : ∀ j : Fin (J+ell),
      bigMod g ((x.2 g).1 j) ∈ seen)
    (hSeenOld : ∀ r : Fin ((x.2 g).2.1.val),
      bigMod g (((x.2 g).2.2 r).1) ∈ seen) :
    Function.Injective ((z.2.2.1.bigChoice g).1) := by
  apply oriented_legal_target_injective
    (bigMod g) (J+ell) (cap g)
    (x.2 g) ((z.2.2.1.bigChoice g).1)
    (sourceBigShared J ell m (patterns z.1) g)
    (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
    (sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 x
      z.2.2.1.sigmaBig z.2.2.2.1)
    (sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 x
      z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
    ((z.2.2.1.bigChoice g).2)
    (hlegal.2.2.2.1 g) hSrc hOld hSep
  · exact oriented_E_fresh_group_injective
      SP smallMod BP bigMod J ell m cap patterns
      x z seen hbatch g
  · intro j hj t he
    have hnot := oriented_E_fresh_not_seen
      SP smallMod BP bigMod J ell m cap patterns
      x z seen hbatch g j hj
    apply hnot
    rw [he]
    exact hSeenActive t
  · intro j hj r he
    have hnot := oriented_E_fresh_not_seen
      SP smallMod BP bigMod J ell m cap patterns
      x z seen hbatch g j hj
    apply hnot
    rw [he]
    exact hSeenOld r

end Green64FullPhysicalE

end

/-! ## PhysicalActualBirthGroupDisintegration -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original G_i ghost PRIME-identity set within a single BIG
group; duplicated atoms remain possible in the ambient Fock state,
but the actual birth marker controls repetitions on path support. -/
noncomputable def physicalGhostGroupBornSet
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (g : BG) : Finset (BP g) :=
  (Finset.univ : Finset (Fin ((c g).2.1.val))).image
    (fun j => ((c g).2.2 j).1)
/-- The actual GLOBAL source G_i birth batch is exactly the
disjoint-group union of the actual groupwise numerical ghost
birth integrations, BEFORE the distinct-birth filter. -/
theorem physicalGhostAllGroupNumbers_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) :
    (physicalGhostFreshBirths SP smallMod BP bigMod
      (J+ell) cap x c).toFinset =
    (Finset.univ : Finset BG).biUnion (fun g =>
      (physicalGhostGroupBornSet SP smallMod BP bigMod
         J ell cap x c g).image (bigMod g)) := by
  classical
  ext n
  constructor
  · intro hn
    have hnlist := List.mem_toFinset.mp hn
    unfold physicalGhostFreshBirths at hnlist
    rcases List.mem_flatMap.mp hnlist with ⟨g, _, hg⟩
    rcases List.mem_map.mp hg with ⟨a, ha, hnval⟩
    rcases List.mem_ofFn.mp ha with ⟨j,hj⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨((c g).2.2 j).1, ?_, ?_⟩
    · unfold physicalGhostGroupBornSet
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · rw [← hj] at hnval
      exact hnval
  · intro hn
    rcases Finset.mem_biUnion.mp hn with ⟨g, _, hg⟩
    rcases Finset.mem_image.mp hg with ⟨p, hp, hpn⟩
    rcases Finset.mem_image.mp hp with ⟨j, _, hjp⟩
    have hmem := physical_G_fresh_group_mem
      SP smallMod BP bigMod (J+ell) cap x c g j
    apply List.mem_toFinset.mpr
    have hnum : bigMod g (((c g).2.2 j).1) = n := by
      rw [hjp, hpn]
    exact hnum ▸ hmem

end Green64FullPhysicalE

end

/-! ## PhysicalActualEBirthGroupDisintegration -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The true globally recorded E fresh numerical births are
EXACTLY the union of the independent source-oriented per-group
fresh target integrations. OLD promotions and stores are not
births; equal numerical values are retained before global
birth-filtering. -/
theorem physicalEAllGroupNumbers_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    (orientedEFreshBirths SP smallMod BP bigMod
       J ell m cap patterns z).toFinset =
    (Finset.univ : Finset BG).biUnion (fun g =>
      (trueBigFreshValues (J+ell) ((z.2.2.1.bigChoice g).1)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1)
        (z.2.2.1.tauBig g)).image (bigMod g)) := by
  classical
  ext n
  constructor
  · intro hn
    have hlist := List.mem_toFinset.mp hn
    unfold orientedEFreshBirths at hlist
    rcases List.mem_flatMap.mp hlist with ⟨g, _, hg⟩
    rcases List.mem_map.mp hg with ⟨j, hj, hnum⟩
    have hj : j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1) :=
      Finset.mem_toList.mp hj
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨((z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j)),
      ?_, ?_⟩
    · unfold trueBigFreshValues
      exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
    · exact hnum
  · intro hn
    rcases Finset.mem_biUnion.mp hn with ⟨g, _, hg⟩
    rcases Finset.mem_image.mp hg with ⟨p, hp, hpn⟩
    rcases Finset.mem_image.mp hp with ⟨j, hj, hjp⟩
    have hmem := oriented_E_fresh_member_global_birth
      SP smallMod BP bigMod J ell m cap patterns x z g j hj
    apply List.mem_toFinset.mpr
    have hnum : bigMod g
      ((z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j)) = n := by
      rw [hjp, hpn]
    exact hnum ▸ hmem

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullOutputUniqueness -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Actual source E witness has one copy of each prime across its
entire output active + pending memory, provided all source active
and pending labels were born uniquely and the TRUE chronological
numerical birth marker is applied to new active draws. This
supplies the physical part of the literal source-history NODUP
and support invariant; no extra admissibility filter is invented. -/
theorem oriented_actual_E_full_output_unique
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)
    (seen : Finset ℕ)
    (hbatch : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z)
    (g : BG)
    (hSrc : Function.Injective ((x.2 g).1))
    (hOld : Function.Injective
      (fun r : Fin ((x.2 g).2.1.val) => ((x.2 g).2.2 r).1))
    (hSep : ∀ (j : Fin (J+ell))
      (r : Fin ((x.2 g).2.1.val)),
      (x.2 g).1 j ≠ ((x.2 g).2.2 r).1)
    (hSeenActive : ∀ j : Fin (J+ell),
      bigMod g ((x.2 g).1 j) ∈ seen)
    (hSeenOld : ∀ r : Fin ((x.2 g).2.1.val),
      bigMod g (((x.2 g).2.2 r).1) ∈ seen) :
    let b := z.2.2.1
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 x b.sigmaBig
      z.2.2.2.1 orientation k
    Function.Injective ((b.bigChoice g).1) ∧
      ((physicalPendingOutput (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.sigmaBig g) step (b.bigChoice g).2).map
        (fun a => a.1)).Nodup ∧
      (∀ j : Fin (J+ell), ∀ v : BP g,
        v ∈ (physicalPendingOutput (bigMod g) (J+ell) (cap g)
          (x.2 g) (b.sigmaBig g) step (b.bigChoice g).2).map
          (fun a => a.1) →
        (b.bigChoice g).1 j ≠ v) := by
  dsimp only
  have hnew (j : Fin (J+ell))
      (hj : j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1)) :
      bigMod g ((z.2.2.1.bigChoice g).1
        (z.2.2.1.tauBig g j)) ∉ seen :=
    oriented_E_fresh_not_seen
      SP smallMod BP bigMod J ell m cap patterns
      x z seen hbatch g j hj
  have hfActive :
      ∀ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1),
      ∀ i : Fin (J+ell),
        (z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j) ≠
          (x.2 g).1 i := by
    intro j hj i he
    apply hnew j hj
    rw [he]
    exact hSeenActive i
  have hfOld :
      ∀ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1),
      ∀ r : Fin ((x.2 g).2.1.val),
        (z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j) ≠
          ((x.2 g).2.2 r).1 := by
    intro j hj r he
    apply hnew j hj
    rw [he]
    exact hSeenOld r
  refine ⟨?_, ?_, ?_⟩
  · exact oriented_actual_E_target_injective
      SP smallMod BP bigMod J ell m cap patterns
      x orientation k z hlegal seen hbatch g
      hSrc hOld hSep hSeenActive hSeenOld
  · exact oriented_E_pending_prime_nodup
      (bigMod g) (J+ell) (cap g) (x.2 g)
      (z.2.2.1.sigmaBig g)
      (sourceOrientedStep SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
      (z.2.2.1.bigChoice g).2
      hSrc hOld hSep
  · exact oriented_E_target_pending_disjoint
      (bigMod g) (J+ell) (cap g) (x.2 g)
      (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
      (sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1)
      (sourceOrientedStep SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
      (z.2.2.1.bigChoice g).2 (hlegal.2.2.2.1 g)
      hSrc hOld hSep hfActive hfOld

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedSeenConservation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- This is the exact E part of source RowValid.ever_update:
each oriented target active label is an OLD shared/promoted prime
or one actual new fresh target birth; each pending output prime
is inherited from OLD Fock memory or stored input active.
Auxiliary draws of D and OLD promotions are not births. -/
theorem oriented_E_seen_conservation
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)
    (seen : Finset ℕ)
    (g : BG)
    (hSeenActive : ∀ j : Fin (J+ell),
      bigMod g ((x.2 g).1 j) ∈ seen)
    (hSeenOld : ∀ r : Fin ((x.2 g).2.1.val),
      bigMod g (((x.2 g).2.2 r).1) ∈ seen) :
    (∀ j : Fin (J+ell),
      bigMod g ((z.2.2.1.bigChoice g).1 j) ∈
        seen ∪ (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).toFinset) ∧
    (∀ v : BP g,
      v ∈ (physicalPendingOutput (bigMod g) (J+ell) (cap g)
        (x.2 g) (z.2.2.1.sigmaBig g)
        (sourceOrientedStep SP smallMod BP bigMod
          J ell m cap (patterns z.1) z.2.1 x
          z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
        (z.2.2.1.bigChoice g).2).map (fun a => a.1) →
      bigMod g v ∈ seen) := by
  have hbig := hlegal.2.2.2.1 g
  constructor
  · intro j
    let t : Fin (J+ell) := (z.2.2.1.tauBig g).symm j
    have hj : (z.2.2.1.tauBig g) t = j := by simp [t]
    rw [← hj]
    by_cases htS : t ∈ sourceBigShared J ell m (patterns z.1) g
    · apply Finset.mem_union_left
      rw [← hbig.shared_copy t htS]
      exact hSeenActive (z.2.2.1.sigmaBig g t)
    · by_cases htP : t ∈ ((z.2.2.1.bigChoice g).2.2.1)
      · apply Finset.mem_union_left
        rw [hbig.promoted_matches ⟨t,htP⟩]
        exact hSeenOld ((z.2.2.1.bigChoice g).2.2.2 ⟨t,htP⟩)
      · apply Finset.mem_union_right
        have hf : t ∈ orientedFresh (J+ell)
            (sourceBigShared J ell m (patterns z.1) g)
            ((z.2.2.1.bigChoice g).2.2.1) := by
          simp [orientedFresh,orientedUnshared,htS,htP]
        apply List.mem_toFinset.mpr
        exact oriented_E_fresh_member_global_birth
          SP smallMod BP bigMod J ell m cap patterns
          x z g t hf
  · intro v hv
    have hmem := (physical_E_pending_prime_mem_iff
      (bigMod g) (J+ell) (cap g)
      (x.2 g) (z.2.2.1.sigmaBig g)
      (sourceOrientedStep SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
      ((z.2.2.1.bigChoice g).2) v).mp hv
    rcases hmem with ⟨r,hr,hrv⟩ | ⟨t,ht,htv⟩
    · rw [hrv]
      exact hSeenOld r
    · rw [htv]
      exact hSeenActive (z.2.2.1.sigmaBig g t)

end Green64FullPhysicalE

end

/-! ## PhysicalOrbitHistoryInvariant -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The canonical physical pending VALUE multiset contains the
ORIGINAL numerical-prime residue atoms without deduplication. -/
noncomputable def physicalOutputPendingValues
    (y : FullPhysicalOutput SP smallMod BP bigMod M)
    (g : BG) : Multiset (BP g) :=
  ((y.2 g).2).map fun a => a.1
/-- The physically relevant per-group simple-particle locus on
the G/E symmetric Hilbert orbit, restricted to prime values whose
births have already been registered. This is a PROPERTY, not an
alteration of the original symmetric Fock measure. -/
def PhysicalGoodOrbit
    (y : FullPhysicalOutput SP smallMod BP bigMod M)
    (seen : Finset ℕ) : Prop :=
  ∀ g : BG,
    Function.Injective ((y.2 g).1) ∧
    (physicalOutputPendingValues SP smallMod BP bigMod M y g).Nodup ∧
    (∀ j : Fin M, ∀ v : BP g,
      v ∈ physicalOutputPendingValues SP smallMod BP bigMod M y g →
        ((y.2 g).1 j) ≠ v) ∧
    (∀ j : Fin M, bigMod g ((y.2 g).1 j) ∈ seen) ∧
    (∀ v ∈ physicalOutputPendingValues SP smallMod BP bigMod M y g,
      bigMod g v ∈ seen)

/-- True finite Fock orbit quotient forgets OLD sector ORDER only.
Its numerical-prime multiset is exactly the image of the original
indexed OLD coordinates, without an artificial prime dedup. -/
theorem physicalProjectionPendingValues_exact
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (g : BG) :
    physicalOutputPendingValues SP smallMod BP bigMod M
      (physicalFockProjection SP smallMod BP bigMod M cap x) g =
    ((Green64Fock.fockToList ((x.2 g).2)).map
      (fun a => a.1) : Multiset (BP g)) := by
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalGoodOrbitG -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The ORIGINAL raw source ghost G_i, on any NONZERO actual
OLD-index/fresh-birth witness, preserves the finite symmetric-Fock
prime-history invariant and updates the seen set ONLY at real
fresh ghost births. The proof invokes actual G witness coefficients,
not a surrogate Markov transition. -/
theorem actual_G_preserves_physical_good_orbit
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (seen : Finset ℕ)
    (hx : PhysicalGoodOrbit SP smallMod BP bigMod M
      (physicalFockProjection SP smallMod BP bigMod M cap x) seen)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod M cap
      x seen c) :
    PhysicalGoodOrbit SP smallMod BP bigMod M
      (physicalFockProjection SP smallMod BP bigMod M cap y)
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        M cap x c).toFinset) := by
  intro g
  have h := hx g
  have hOld :
      ((Green64Fock.fockToList ((x.2 g).2)).map
        (fun a => a.1)).Nodup := by
    have hp := h.2.1
    rw [physicalProjectionPendingValues_exact] at hp
    exact Multiset.coe_nodup.mp hp
  have hmemOld (r : Fin ((x.2 g).2.1.val)) :
      ((x.2 g).2.2 r).1 ∈
        (Green64Fock.fockToList ((x.2 g).2)).map
          (fun a => a.1) := by
    apply List.mem_map.mpr
    refine ⟨(x.2 g).2.2 r, ?_, rfl⟩
    simp [Green64Fock.fockToList]
  have hSep :
      ∀ (j : Fin M) (r : Fin ((x.2 g).2.1.val)),
        (x.2 g).1 j ≠ ((x.2 g).2.2 r).1 := by
    intro j r
    apply h.2.2.1 j _
    rw [physicalProjectionPendingValues_exact]
    exact Multiset.mem_coe.mpr (hmemOld r)
  have hSeenOld :
      ∀ v ∈ (Green64Fock.fockToList ((x.2 g).2)).map
          (fun a => a.1),
        bigMod g v ∈ seen := by
    intro v hv
    exact h.2.2.2.2 v
      (by rw [physicalProjectionPendingValues_exact]
          exact Multiset.mem_coe.mpr hv)
  have ho := physical_nonzero_G_full_output_unique
    SP smallMod BP bigMod M cap q rho N i Vbig muBig
    x y c hterm seen hb g h.1 hOld hSep
    h.2.2.2.1 hSeenOld
  refine ⟨ho.1, ?_, ?_, ?_, ?_⟩
  · rw [physicalProjectionPendingValues_exact]
    exact Multiset.coe_nodup.mpr ho.2.1
  · intro j v hv
    exact ho.2.2.1 j v
      (by rw [physicalProjectionPendingValues_exact] at hv
          exact Multiset.mem_coe.mp hv)
  · intro j
    exact Finset.mem_union_left _ (ho.2.2.2.1 j)
  · intro v hv
    exact ho.2.2.2.2 v
      (by rw [physicalProjectionPendingValues_exact] at hv
          exact Multiset.mem_coe.mp hv)

end Green64FullPhysicalE

end

/-! ## PhysicalFockOldIndexInjectivity -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (B : ℕ)

/-- A source symmetric pending sector whose prime VALUE multiset
is distinct determines a canonical injective map from every OLD
Fock index to its prime label. The sector remains ordered in the
raw G/E witness; we only derive injectivity from the symmetric
orbit's actual no-duplicate condition. -/
theorem sourceFock_old_prime_injective
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B)
    (h : ((Green64Fock.fockMultiset s).map
      (fun z => z.1)).Nodup) :
    Function.Injective (fun i : Fin s.1.val => (s.2 i).1) := by
  classical
  have hlist :
      ((List.ofFn s.2).map (fun z => z.1)).Nodup := by
    simpa [Green64Fock.fockMultiset,
      Multiset.map_coe, Multiset.coe_nodup] using h
  have hinj := List.nodup_iff_injective_get.mp hlist
  intro i j he
  let ii : Fin (((List.ofFn s.2).map (fun z => z.1)).length) :=
    ⟨i.val, by simp⟩
  let jj : Fin (((List.ofFn s.2).map (fun z => z.1)).length) :=
    ⟨j.val, by simp⟩
  have hh : ((List.ofFn s.2).map (fun z => z.1)).get ii =
      ((List.ofFn s.2).map (fun z => z.1)).get jj := by
    simpa [ii,jj] using he
  have hfin := hinj hh
  exact Fin.ext (by
    have hv := congrArg
      (fun a : Fin (((List.ofFn s.2).map (fun z => z.1)).length) =>
        a.val) hfin
    simpa [ii,jj] using hv)

end Green64FullPhysicalE

end

/-! ## PhysicalFockOldListInjective -/

section

open Classical

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (B : ℕ)

/-- The exact physical OLD Fock index injection is preserved when
one uses the source ordered-list representation fockToList.
The index sets have equal sizes but are NOT definitionally identical. -/
theorem sourceFock_old_list_prime_injective
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B)
    (h : ((Green64Fock.fockMultiset s).map
      (fun a => a.1)).Nodup) :
    Function.Injective (fun j : Fin (Green64Fock.fockToList s).length =>
      ((Green64Fock.fockToList s).get j).1) := by
  have hn : (Green64Fock.fockToList s).length = s.1.val := by
    simp [Green64Fock.fockToList]
  have hindex := sourceFock_old_prime_injective modulus B s h
  intro i j hij
  have hfin : Fin.cast hn i = Fin.cast hn j := by
    apply hindex
    have hi : (Green64Fock.fockToList s).get i =
        s.2 (Fin.cast hn i) := by
      exact List.get_ofFn s.2 i
    have hj : (Green64Fock.fockToList s).get j =
        s.2 (Fin.cast hn j) := by
      exact List.get_ofFn s.2 j
    exact (congrArg (fun a => a.1) hi).symm.trans
      (hij.trans (congrArg (fun a => a.1) hj))
  exact Fin.cast_injective hn hfin

end Green64FullPhysicalE

end

/-! ## PhysicalActualGValueOneStep -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- One actual NONZERO physical G_i witness obeys literal
value-level OLD set subtraction and fresh ghost birth union,
provided the real input physical Fock orbit has one copy of
each previously born prime. No abstract Markov assumption. -/
theorem nonzero_physical_G_value_set_update
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hTerm : physicalGBranchTerm SP smallMod BP bigMod
      M cap q rho N i Vbig muBig x y c ≠ 0)
    (g : BG)
    (hOld : ((Green64Fock.fockMultiset ((x.2 g).2)).map
      (fun z => z.1)).Nodup) :
    ((Green64Fock.fockToList ((y.2 g).2)).map
      (fun z => z.1)).toFinset =
      (((Green64Fock.fockToList ((x.2 g).2)).map
        (fun z => z.1)).toFinset \
        ((c g).1.1).image
          (fun j => ((Green64Fock.fockToList
            ((x.2 g).2)).get j).1)) ∪
      ((Finset.univ : Finset (Fin ((c g).2.1.val))).image
        (fun j => ((c g).2.2 j).1)) := by
  have hInjective := sourceFock_old_list_prime_injective
    (bigMod g) (cap g) ((x.2 g).2) hOld
  have hOperational :=
    (physical_nonzero_ghost_witness_is_operational
      SP smallMod BP bigMod M cap q rho N i
      Vbig muBig x y c hTerm).2 g
  rw [← hOperational]
  exact ghost_actual_value_support_injective
    (Green64Fock.fockToList ((x.2 g).2))
    (c g).1.1 (c g).2.2
    (fun a : Green64Fock.Atom (BP g) (bigMod g) => a.1)
    hInjective

end Green64FullPhysicalE

end

/-! ## PhysicalFockPrimeIndexSet -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The original finite Fock OLD indices enumerate exactly the
prime-value support of the physical pending list, without
assuming that repeated prime atoms are absent. -/
theorem bigFock_old_index_prime_support
    (x : BigState modulus M B) :
    ((Finset.univ : Finset (Fin x.2.1.val)).image
       (fun j => (x.2.2 j).1)) =
      (((Green64Fock.fockToList x.2).map (fun a => a.1)).toFinset) := by
  classical
  ext v
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr
      ⟨x.2.2 j, by simp [Green64Fock.fockToList], hj⟩
  · intro h
    rcases List.mem_map.mp (List.mem_toFinset.mp h) with
      ⟨a, ha, hv⟩
    have hm : a ∈ List.ofFn x.2.2 := by
      simpa [Green64Fock.fockToList] using ha
    rcases List.mem_ofFn.mp hm with ⟨j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [hj]
    exact hv

end Green64FullPhysicalE

end

/-! ## PhysicalBIGSourceSetSubsets -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Every OLD E promotion source prime is among actual source
pending Fock particles, even if the ambient Fock sector permits
repeated atoms: injectivity is not needed for this inclusion. -/
theorem trueBigPromotedValues_subset_OLD
    (x : BigState modulus M B) (c : BigEdgeChoice modulus M B x) :
    trueBigPromotedValues modulus M B x c ⊆
      (((Green64Fock.fockToList x.2).map (fun a => a.1)).toFinset) := by
  classical
  intro p hp
  have hindex := bigFock_old_index_prime_support modulus M B x
  rw [← hindex]
  rcases Finset.mem_image.mp hp with ⟨j, _, hj⟩
  exact Finset.mem_image.mpr
    ⟨c.2.2 j, Finset.mem_univ _, hj⟩

/-- Each stored source prime comes from one of the actual original
ordered active source labels, regardless of endpoint permutations. -/
theorem trueBigStoredValues_subset_active
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M))
    (c : BigEdgeChoice modulus M B x) :
    trueBigStoredValues modulus M B x sigma c ⊆
      (Finset.univ : Finset (Fin M)).image x.1 := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j, _, hj⟩
  exact Finset.mem_image.mpr
    ⟨sigma j, Finset.mem_univ _, hj⟩

/-- Every oriented shared source label is an actual source active
label; sampling the source permutation changes the slot, not
the source support. -/
theorem trueBigSharedValues_subset_active
    (x : BigState modulus M B)
    (shared : Finset (Fin M)) (sigma : Equiv.Perm (Fin M)) :
    trueBigSharedValues modulus M B x shared sigma ⊆
      (Finset.univ : Finset (Fin M)).image x.1 := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨j, _, hj⟩
  exact Finset.mem_image.mpr
    ⟨sigma j, Finset.mem_univ _, hj⟩

/-- On a source physical state with uniquely labelled active slots,
one cannot store a shared source slot. This is the actual
source-row condition K_i ⊆ A_i \ S_i. -/
theorem trueBigStored_disjoint_shared
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hleg : OrientedBigEdgeLegal modulus M B
      x target shared sigma tau D step c)
    (hinj : Function.Injective x.1) :
    Disjoint
      (trueBigStoredValues modulus M B x sigma c)
      (trueBigSharedValues modulus M B x shared sigma) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hshared
  rcases Finset.mem_image.mp hp with ⟨j, hj, hval⟩
  rcases Finset.mem_image.mp hshared with ⟨t, ht, heq⟩
  have hjt : j = t :=
    sigma.injective (hinj (hval.trans heq.symm))
  have hnot : j ∉ shared := by
    have h := hleg.stores_unshared hj
    simpa [orientedUnshared] using h
  exact hnot (hjt ▸ ht)

end Green64FullPhysicalE

end

/-! ## PhysicalGoodOrbitE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The original source E output in symmetric Fock coordinates
contains precisely the OLD-survivor+new-store prime LIST,
with every multiplicity visible. -/
theorem oriented_E_output_pending_values_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (g : BG) :
    physicalOutputPendingValues SP smallMod BP bigMod (J+ell)
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod
        J ell m cap patterns x orientation k z) g =
    ((physicalPendingOutput (bigMod g) (J+ell) (cap g) (x.2 g)
      (z.2.2.1.sigmaBig g)
      (sourceOrientedStep SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
      (z.2.2.1.bigChoice g).2).map (fun a => a.1) :
      Multiset (BP g)) := by
  simp [physicalOutputPendingValues, sourceOrientedPhysicalOutput,
    fullPhysicalBranchOutput, bigGroupBranchOutput,
    physicalBranchOutput, physicalPendingMultiset,
    Multiset.map_coe]

/-- The CORRECTED real E_i branch preserves the physical simple-
particle locus on the TRUE symmetric Fock quotient (including its
old active-mu and pending lambda sector masses). The actual global
birth marker provides all required fresh-vs-old exclusions. -/
theorem actual_oriented_E_preserves_physical_good_orbit
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (seen : Finset ℕ)
    (hx : PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod (J+ell)
        cap x) seen)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)
    (hb : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z) :
    PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod
        J ell m cap patterns x orientation k z)
      (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns z).toFinset) := by
  intro g
  have h := hx g
  have hOldInj :
      Function.Injective
        (fun r : Fin ((x.2 g).2.1.val) => ((x.2 g).2.2 r).1) := by
    apply sourceFock_old_prime_injective (bigMod g) (cap g)
    simpa [physicalOutputPendingValues,
      physicalFockProjection] using h.2.1
  have hSep :
      ∀ (j : Fin (J+ell)) (r : Fin ((x.2 g).2.1.val)),
      (x.2 g).1 j ≠ ((x.2 g).2.2 r).1 := by
    intro j r
    apply h.2.2.1 j _
    rw [physicalProjectionPendingValues_exact]
    apply Multiset.mem_coe.mpr
    apply List.mem_map.mpr
    refine ⟨(x.2 g).2.2 r, ?_, rfl⟩
    simp [Green64Fock.fockToList]
  have hSeenOld :
      ∀ r : Fin ((x.2 g).2.1.val),
        bigMod g (((x.2 g).2.2 r).1) ∈ seen := by
    intro r
    apply h.2.2.2.2
    rw [physicalProjectionPendingValues_exact]
    apply Multiset.mem_coe.mpr
    apply List.mem_map.mpr
    refine ⟨(x.2 g).2.2 r, ?_, rfl⟩
    simp [Green64Fock.fockToList]
  have hOut := oriented_actual_E_full_output_unique
    SP smallMod BP bigMod J ell m cap patterns
    x orientation k z hlegal seen hb g
    h.1 hOldInj hSep h.2.2.2.1 hSeenOld
  have hSeen := oriented_E_seen_conservation
    SP smallMod BP bigMod J ell m cap patterns
    x orientation k z hlegal seen g h.2.2.2.1 hSeenOld
  refine ⟨hOut.1, ?_, ?_, ?_, ?_⟩
  · rw [oriented_E_output_pending_values_exact]
    exact Multiset.coe_nodup.mpr hOut.2.1
  · intro j v hv
    rw [oriented_E_output_pending_values_exact] at hv
    exact hOut.2.2 j v (Multiset.mem_coe.mp hv)
  · exact hSeen.1
  · intro v hv
    rw [oriented_E_output_pending_values_exact] at hv
    exact Finset.mem_union_left _ (hSeen.2 v
      (Multiset.mem_coe.mp hv))

end Green64FullPhysicalE

end

/-! ## PhysicalGoodOrbitGE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- An ACTUAL joint G_i E_i source path cannot create a second
copy of an already born BIG prime, either among target active slots
or inside symmetric pending Fock memory. Its G witness is constrained
by the literal physical nonzero coefficient; E is one legal
source-oriented ν,aux,D,OLD/store/fresh witness; the intermediate
Fock representatives agree ONLY through their true multiset orbit. -/
theorem actual_full_GE_preserves_physical_good_orbit
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x yg xe : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns xe)
    (seen : Finset ℕ)
    (hx : PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) seen)
    (hG : physicalGBranchTerm SP smallMod BP bigMod
      (J+ell) cap q rho N i Vbig muBig x yg c ≠ 0)
    (hGbirth : physicalGhostBatchEligible SP smallMod BP bigMod
      (J+ell) cap x seen c)
    (hFiber : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap xe =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap yg)
    (hE : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns xe orientation k z)
    (hEbirth : orientedEFreshBatchEligible
      SP smallMod BP bigMod J ell m cap patterns
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap x c).toFinset) z) :
    PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod
        J ell m cap patterns xe orientation k z)
      ((seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap x c).toFinset) ∪
        (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).toFinset) := by
  have hGoodG := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig x yg c seen hx hG hGbirth
  have hGoodE : PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xe)
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap x c).toFinset) := by
    rw [hFiber]
    exact hGoodG
  exact actual_oriented_E_preserves_physical_good_orbit
    SP smallMod BP bigMod J ell m cap patterns xe
    orientation k z _ hGoodE hE hEbirth

end Green64FullPhysicalE

end

/-! ## PhysicalInitialVacuumGood -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The original physical root's GLOBAL Nodup test on its initial
ordered active PRIME VALUES makes each BIG group's active
label array injective. No injectivity of the abstract BP encoding
is postulated: it follows from the literal source birth test. -/
theorem original_initial_births_group_injective
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hInit : (physicalInitialBirths SP smallMod BP bigMod
      J ell cap x).Nodup) (g : BG) :
    Function.Injective ((x.2 g).1) := by
  have hLocal :
      (((Finset.univ : Finset (Fin (J+ell))).toList).map
        (fun j => bigMod g ((x.2 g).1 j))).Nodup := by
    have h := (List.nodup_flatMap.mp hInit).1
    exact h g (Finset.mem_toList.mpr (Finset.mem_univ g))
  intro j k he
  have hn := List.inj_on_of_nodup_map hLocal
    (Finset.mem_toList.mpr (Finset.mem_univ j))
    (Finset.mem_toList.mpr (Finset.mem_univ k))
    (congrArg (bigMod g) he)
  exact hn

/-- The same initial source Nodup certifies that every initial
ordered physical BIG label appears exactly in the initial seen set.
Free auxiliary draws of D do not contribute. -/
theorem original_initial_active_seen
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (g : BG) (j : Fin (J+ell)) :
    bigMod g ((x.2 g).1 j) ∈
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset := by
  apply List.mem_toFinset.mpr
  unfold physicalInitialBirths
  apply List.mem_flatMap.mpr
  refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), ?_⟩
  exact List.mem_map.mpr
    ⟨j, Finset.mem_toList.mpr (Finset.mem_univ j), rfl⟩
/-- A REAL physical initial vacuum, with global distinct-birth
indicator exactly as in physicalOrientedFiniteMarkedRoot, lies
in the GOOD symmetric physical Fock orbit. This is the base
case for the G/E path-history invariant; pending memory is empty
rather than assumed to contain an arbitrary set of old atoms. -/
theorem original_initial_vacuum_good_orbit
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hInit : (physicalInitialBirths SP smallMod BP bigMod
      J ell cap x).Nodup)
    (hVac : ∀ g : BG,
      Green64Fock.fockMultiset ((x.2 g).2) = 0) :
    PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset := by
  intro g
  have hm : physicalOutputPendingValues SP smallMod BP bigMod
      (J+ell) (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) g = 0 := by
    simp [physicalOutputPendingValues,physicalFockProjection,hVac g]
  refine ⟨original_initial_births_group_injective
      SP smallMod BP bigMod J ell cap x hInit g, ?_, ?_, ?_, ?_⟩
  · simp [hm]
  · intro j v hv
    simp [hm] at hv
  · exact original_initial_active_seen
      SP smallMod BP bigMod J ell cap x g
  · intro v hv
    simp [hm] at hv

end Green64FullPhysicalE

end

/-! ## PhysicalSourceFockClosure -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {U : Type} [Fintype U]

/-- Produce the actual finite j-sector Hilbert Fock representative
from an admissible pending-particle LIST, without removing any
repeated prime×residue atoms. -/
noncomputable def physicalFockOfList (B : ℕ)
    (xs : List U) (h : xs.length ≤ B) :
    Green64Fock.FockState U B :=
  ⟨⟨xs.length, by omega⟩, xs.get⟩

theorem physicalFockOfList_multiset
    (B : ℕ) (xs : List U) (h : xs.length ≤ B) :
    Green64Fock.fockMultiset (physicalFockOfList B xs h) =
      (xs : Multiset U) := by
  simp [Green64Fock.fockMultiset,physicalFockOfList]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
/-- Materialize a TRUE source-physical (small Haar, big active,
finite Fock) ordered output state for every original admissible E
branch, using the source cutoff proof rather than choosing an
unjustified arbitrary orbit representative. -/
noncomputable def physicalOutputWitness
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hz : SourcePhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z) :
    FullPhysicalState SP smallMod BP bigMod (J + ell) cap :=
  (z.2.2.smallTarget, fun g =>
    ((z.2.2.bigChoice g).1,
      physicalFockOfList (cap g)
        (physicalPendingOutput (bigMod g) (J + ell) (cap g)
          (x.2 g) (z.2.2.sigmaBig g)
          (sourcePhysicalStep SP smallMod BP bigMod J ell m cap
            (patterns z.1) z.2.1 x orientation k)
          ((z.2.2.bigChoice g).2))
        (hz.1 g).output_within_cutoff))

/-- Every actually source-admissible E_i output is present in
the true finite symmetric physical-Hilbert carrier. Hence
composition of finite genuine E and G does NOT escape to an
artificially enlarged, unreachable memory state. -/
theorem physicalOutputWitness_correct
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hz : SourcePhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z) :
    physicalFockProjection SP smallMod BP bigMod (J + ell) cap
      (physicalOutputWitness SP smallMod BP bigMod
        J ell m cap patterns x orientation k z hz) =
    sourcePhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k z := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · exact physicalFockOfList_multiset (cap g)
        (physicalPendingOutput (bigMod g) (J + ell) (cap g)
          (x.2 g) (z.2.2.sigmaBig g)
          (sourcePhysicalStep SP smallMod BP bigMod J ell m cap
            (patterns z.1) z.2.1 x orientation k)
          ((z.2.2.bigChoice g).2))
        (hz.1 g).output_within_cutoff
theorem sourcePhysicalE_reachable_in_symmetric_Fock
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) :
    fullSourcePhysicalSupport SP smallMod BP bigMod
      J ell m cap patterns x orientation k ⊆
    physicalFockOrbitSupport SP smallMod BP bigMod
      (J + ell) cap := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z,hz,hzy⟩
  have hlegal : SourcePhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z :=
    (Finset.mem_filter.mp hz).2
  apply Finset.mem_image.mpr
  refine ⟨physicalOutputWitness SP smallMod BP bigMod
      J ell m cap patterns x orientation k z hlegal,
      Finset.mem_univ _, ?_⟩
  rw [physicalOutputWitness_correct
    SP smallMod BP bigMod J ell m cap patterns
    x orientation k z hlegal]
  exact hzy

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEReachability -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Every *corrected* oriented source E branch has a genuine
ordered Hilbert state realizing its output multiset. The cutoff
witness is obtained directly from the new OrientedBigEdgeLegal,
not from the invalid old PhysicalEdgeLegal. -/
noncomputable def physicalOrientedOutputWitness
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z) :
    FullPhysicalState SP smallMod BP bigMod (J+ell) cap :=
  (z.2.2.1.smallTarget, fun g =>
    ((z.2.2.1.bigChoice g).1,
      physicalFockOfList (cap g)
        (physicalPendingOutput (bigMod g) (J+ell) (cap g)
          (x.2 g) (z.2.2.1.sigmaBig g)
          (sourceOrientedStep SP smallMod BP bigMod
            J ell m cap (patterns z.1) z.2.1 x
            z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
          ((z.2.2.1.bigChoice g).2))
        ((hz.2.2.2.1 g).output_within_cutoff)))

theorem physical_oriented_E_output_witness_correct
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (physicalOrientedOutputWitness SP smallMod BP bigMod
        J ell m cap patterns x orientation k z hz) =
    sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k z := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · exact physicalFockOfList_multiset (cap g)
        (physicalPendingOutput (bigMod g) (J+ell) (cap g)
          (x.2 g) (z.2.2.1.sigmaBig g)
          (sourceOrientedStep SP smallMod BP bigMod
            J ell m cap (patterns z.1) z.2.1 x
            z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
          ((z.2.2.1.bigChoice g).2))
        ((hz.2.2.2.1 g).output_within_cutoff)

/-- Original corrected oriented E is closed on the ACTUAL
finite symmetric Fock support. No impossible target states,
discarded witnesses, or fake quotient target type. -/
theorem physical_oriented_full_E_reachable_in_Fock
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ) :
    orientedEdgeSupport SP smallMod BP bigMod
      J ell m cap patterns x orientation k ⊆
    physicalFockOrbitSupport SP smallMod BP bigMod
      (J+ell) cap := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, hzy⟩
  have hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z :=
    (Finset.mem_filter.mp hz).2
  apply Finset.mem_image.mpr
  refine ⟨physicalOrientedOutputWitness SP smallMod BP bigMod
    J ell m cap patterns x orientation k z hlegal,
    Finset.mem_univ _, ?_⟩
  rw [physical_oriented_E_output_witness_correct
    SP smallMod BP bigMod J ell m cap patterns
    x orientation k z hlegal]
  exact hzy

end Green64FullPhysicalE

end

/-! ## PhysicalSourcePrimeCarrier -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]

/-- Source global prime label carrier: BIG group plus actual
finite prime-list element. The numerical value is not fabricated
by a bare abstract kernel; it is the original physical bigMod. -/
abbrev PhysicalSourcePrime := Sigma BP

def physicalSourcePrimeValue
    (x : PhysicalSourcePrime BP) : ℕ := bigMod x.1 x.2

def physicalSourcePrimeGroup
    (x : PhysicalSourcePrime BP) : BG := x.1

/-- The original disjoint BIG prime group condition amounts to
injectivity of the NATURAL numerical-prime map on this carrier.
This is an explicit source assumption, NOT derivable from the
abstract BP g types or mere NeZero(modulus). -/
theorem physical_source_prime_value_group_separation
    (hinj : Function.Injective
      (physicalSourcePrimeValue BP bigMod))
    (g h : BG) (p : BP g) (q : BP h)
    (heq : bigMod g p = bigMod h q) : g = h := by
  have hh : (⟨g,p⟩ : PhysicalSourcePrime BP) = ⟨h,q⟩ :=
    hinj heq
  exact congrArg Sigma.fst hh

/-- Within each actual BIG group the original numerical labeling
is injective whenever source prime families are globally disjoint. -/
theorem physical_source_prime_value_group_injective
    (hinj : Function.Injective
      (physicalSourcePrimeValue BP bigMod))
    (g : BG) :
    Function.Injective (bigMod g) := by
  intro p q heq
  have hh : (⟨g,p⟩ : PhysicalSourcePrime BP) = ⟨g,q⟩ :=
    hinj heq
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

/-- This is the exact numeric-primality field required by the
literal source row: the source explicitly assumes each actual
BIG group label denotes a genuine natural prime. -/
theorem physical_source_prime_values_are_primes
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (x : PhysicalSourcePrime BP) :
    Nat.Prime (physicalSourcePrimeValue BP bigMod x) :=
  hprime x.1 x.2

end Green64FullPhysicalE

end

/-! ## PhysicalSymmetricVisitG -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The full small Haar × big active × Fock weighted quotient
map for an arbitrary finite ordered physical-state function.
This is the real Hilbert orthogonal conditional expectation. -/
noncomputable def fullPhysicalOrbitAverage
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (h : FullPhysicalState SP smallMod BP bigMod M cap → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod M) : ℂ :=
  (∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod M cap))
       with physicalFockProjection SP smallMod BP bigMod M cap x = y,
       (fullPhysicalMass SP smallMod BP bigMod M cap
         Vsmall muBig x : ℂ) * h x) /
    (physicalOrbitMass SP smallMod BP bigMod M cap
      Vsmall muBig y : ℂ)
/-- Exact weighted Hilbert identity for all true finite physical
Fock orbits, including repeated equal particles; not a flat
counting average and not an assumed Markov operator. -/
theorem fullPhysicalOrbitAverage_pairing
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (F : FullPhysicalOutput SP smallMod BP bigMod M → ℂ)
    (h : FullPhysicalState SP smallMod BP bigMod M cap → ℂ) :
    physicalSymmetricInner SP smallMod BP bigMod M cap
      Vsmall muBig F
      (fullPhysicalOrbitAverage SP smallMod BP bigMod M cap
        Vsmall muBig h) =
    physicalOrderedInner SP smallMod BP bigMod M cap Vsmall muBig
      (fun x => F (physicalFockProjection SP smallMod BP bigMod M cap x)) h := by
  classical
  unfold physicalSymmetricInner physicalOrderedInner
  rw [Green64Fock.finite_sum_by_image
    (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod M cap))
    (physicalFockProjection SP smallMod BP bigMod M cap)
    (fun x => (fullPhysicalMass SP smallMod BP bigMod M cap
      Vsmall muBig x : ℂ) *
        star (F (physicalFockProjection SP smallMod BP bigMod M cap x)) *
        h x)]
  apply Finset.sum_congr rfl
  intro y hy
  have hpos : (physicalOrbitMass SP smallMod BP bigMod M cap
    Vsmall muBig y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (physicalOrbitMass_pos SP smallMod BP bigMod M cap
        Vsmall muBig hV hmu y hy))
  change (physicalOrbitMass SP smallMod BP bigMod M cap
      Vsmall muBig y : ℂ) * star (F y) *
    ((∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod M cap))
        with physicalFockProjection SP smallMod BP bigMod M cap x = y,
        (fullPhysicalMass SP smallMod BP bigMod M cap
          Vsmall muBig x : ℂ) * h x) /
      (physicalOrbitMass SP smallMod BP bigMod M cap
        Vsmall muBig y : ℂ)) = _
  have hsum :
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod M cap))
        with physicalFockProjection SP smallMod BP bigMod M cap x = y,
        (fullPhysicalMass SP smallMod BP bigMod M cap
          Vsmall muBig x : ℂ) *
          star (F (physicalFockProjection SP smallMod BP bigMod M cap x)) *
          h x) =
      star (F y) *
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod M cap))
        with physicalFockProjection SP smallMod BP bigMod M cap x = y,
        (fullPhysicalMass SP smallMod BP bigMod M cap
          Vsmall muBig x : ℂ) * h x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
    ring
  rw [hsum]
  field_simp

/-- SOURCE ghost G_i on the symmetric physical finite Hilbert
space, obtained from its actual per-group OLD-particle kernel
with ghost births at residue zero and the TRUE Fock weight.
Unlike a scalar proxy, this preserves the physical active/Haar
coordinates and uses the real source α,χ,γ. -/
noncomputable def physicalSymmetricVisitGRow
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP smallMod BP bigMod M → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod M) : ℂ :=
  fullPhysicalOrbitAverage SP smallMod BP bigMod M cap
    Vsmall muBig
    (physicalVisitGRow SP smallMod BP bigMod M cap
      q rho N i Vbig muBig
      (fun x => F (physicalFockProjection SP smallMod BP bigMod M cap x))) y

/-- Exact Hilbert pairing of the full all-big-group physical G_i
and its finite symmetric Fock orbit compression. -/
theorem physicalSymmetricVisitG_pairing
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (F H : FullPhysicalOutput SP smallMod BP bigMod M → ℂ) :
    physicalSymmetricInner SP smallMod BP bigMod M cap
      Vsmall muBig F
      (physicalSymmetricVisitGRow SP smallMod BP bigMod M cap
        q rho N i Vsmall Vbig muBig H) =
    physicalOrderedInner SP smallMod BP bigMod M cap Vsmall muBig
      (fun x => F (physicalFockProjection SP smallMod BP bigMod M cap x))
      (physicalVisitGRow SP smallMod BP bigMod M cap
        q rho N i Vbig muBig
        (fun x => H (physicalFockProjection SP smallMod BP bigMod M cap x))) :=
  fullPhysicalOrbitAverage_pairing SP smallMod BP bigMod M cap
    Vsmall muBig hV hmu F _

end Green64FullPhysicalE

end

/-! ## PhysicalFiniteRootMoment -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Literal source b_p = 1-(sum of all eta_i)/p, with boundary
eta_0 = eta_N = 1-sqrt(q) and internal eta_i=1-q. -/
noncomputable def physicalSourceBaseline
    (q : ℝ) (N : ℕ) (g : BG) (p : BP g) : ℝ :=
  1 - ((∑ i ∈ Finset.range (N + 1),
    sourceVisitEta q N i) / (bigMod g p : ℝ))

theorem physicalSourceBaseline_from_edge_visits
    (q : ℝ) (N : ℕ) (g : BG) (p : BP g) :
    physicalSourceBaseline BP bigMod q N g p =
      1 - (((∑ i ∈ Finset.range N, sourceVisitEta q N i) +
        sourceVisitEta q N N) / (bigMod g p : ℝ)) := by
  simp [physicalSourceBaseline, Finset.sum_range_succ]

/-- BIG prime law mu-tilde = 1/(V_g p b_p); auxiliary D draws
instead use original un-tilted mu_g = 1/(V_g p). -/
noncomputable def physicalSourceMuTilde
    (q : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (g : BG) (p : BP g) : ℝ :=
  1 / (Vbig g * (bigMod g p : ℝ) *
    physicalSourceBaseline BP bigMod q N g p)

/-- Original source prefactor: one b_p for every BIG potential
prime, no small-prime factor and no Fock factorial. -/
noncomputable def physicalSourceBaselineProduct (q : ℝ) (N : ℕ) : ℝ :=
  ∏ g : BG, ∏ p : BP g, physicalSourceBaseline BP bigMod q N g p

/-- Boundary 1_empty: pending memory is empty in all BIG groups;
small Haar and BIG ordered active labels are unrestricted. -/
noncomputable def physicalVacuum
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell)) : ℂ :=
  if ∀ g : BG, (y.2 g).2 = 0 then 1 else 0

/-- Source alternating A,A* sign at successive edges. -/
def physicalAlternatingSign (i : ℕ) : ℤ :=
  if Even i then 1 else -1

/-- G_i E_i G_(i+1)...G_N as explicit FINITE physical
symmetric-COMPRESSED row operations. Every E_i includes the
full pattern+D sum with the source power D^(i*zeta).
The original GLOBAL distinct-birth filter is not yet included;
nor has preservation of symmetry by raw G/E been established. -/
noncomputable def physicalFiniteGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ)
  | 0, start, F =>
      physicalSymmetricVisitGRow SP smallMod BP bigMod
        (J + ell) cap q rho N start Vsmall Vbig muBig F
  | remaining + 1, start, F =>
      physicalSymmetricVisitGRow SP smallMod BP bigMod
        (J + ell) cap q rho N start Vsmall Vbig muBig
        (fun y => physicalSymmetricSourceE SP smallMod BP bigMod
          cap J ell m patterns q rho Vsmall Vbig muBig
          Knu ((start : ℝ) * zeta) theta
          (physicalAlternatingSign start) k y
          (physicalFiniteGEChain q rho Vsmall Vbig muBig
            Knu zeta theta k N remaining (start + 1) F))

/-- Source finite compressed vacuum product with R pairs, N=2R,
the exact b_p prefactor and µtilde = 1/(V_g p b_p).
This is a verified finite scalar EXPRESSION, not a proof that
it equals the source independent-residue/lifespan sum: the global
distinct-birth indicator and symmetry-preservation bridges remain. -/
noncomputable def physicalFiniteCompressedRoot
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2 * R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
    physicalSymmetricInner SP smallMod BP bigMod (J + ell)
      cap Vsmall mu
      (physicalVacuum SP smallMod BP bigMod J ell)
      (physicalFiniteGEChain SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu
        Knu zeta theta k N N 0
        (physicalVacuum SP smallMod BP bigMod J ell))

end Green64FullPhysicalE

end

/-! ## PhysicalFiniteActualWitnessPath -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The COMPLETE physical finite-source witness path carrier:
actual ordered Fock representative BEFORE and AFTER each source
G_i, a potentially differently ordered representative as input
of each E_i, and the next actual physical state. Every witness
comes from the G_i OLD/fresh enumeration and corrected oriented
E_i ν,D,OLD/store/fresh carrier; no abstract Markov transition
or prematurely deduplicated prime-memory state is introduced. -/
structure PhysicalFiniteActualWitnessPath (q rho : ℝ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (k : ℤ) (N : ℕ) where
  before : ℕ → FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  afterG : ℕ → FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  beforeE : ℕ → FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  ghost : (i : ℕ) → FullGhostWitness SP smallMod BP bigMod
    (J+ell) cap (before i)
  edge : (i : ℕ) → FullOrientedSourceChoice SP smallMod BP bigMod
    J ell m cap patterns (beforeE i)
  seen : ℕ → Finset ℕ
  initial_births_nodup :
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap (before 0)).Nodup
  initial_vacuum : ∀ g : BG,
    Green64Fock.fockMultiset (((before 0).2 g).2) = 0
  initial_seen : seen 0 =
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap (before 0)).toFinset
  G_nonzero : ∀ i ≤ N,
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig
      (before i) (afterG i) (ghost i) ≠ 0
  G_birth_eligible : ∀ i ≤ N,
    physicalGhostBatchEligible SP smallMod BP bigMod
      (J+ell) cap (before i) (seen i) (ghost i)
  E_orbit_input : ∀ i < N,
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (beforeE i) =
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (afterG i)
  E_legal : ∀ i < N,
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns (beforeE i)
      (physicalAlternatingSign i) k (edge i)
  E_birth_eligible : ∀ i < N,
    orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns
      ((seen i) ∪ (physicalGhostFreshBirths
        SP smallMod BP bigMod (J+ell) cap
        (before i) (ghost i)).toFinset)
      (edge i)
  E_output : ∀ i < N,
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (before (i+1)) =
    sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns (beforeE i)
      (physicalAlternatingSign i) k (edge i)
  seen_update : ∀ i < N,
    seen (i+1) =
      (((seen i) ∪ (physicalGhostFreshBirths
        SP smallMod BP bigMod (J+ell) cap
        (before i) (ghost i)).toFinset) ∪
        (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns (edge i)).toFinset)
/-- ACTUAL PHYSICAL FINITE PATH INVARIANT for EVERY visit,
not just a local G or E edge: the original vacuum, entire
chronological OLD/fresh witness sequence, ν/free-D sampling,
true Fock multiset boundary glue and global seen-birth rule
force all BIG group active/pending labels to remain distinct,
active and pending to be disjoint, and all live primes to be
previously born at that exact visit. -/
theorem physical_finite_actual_path_good_every_visit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (i : ℕ) (hi : i ≤ N) :
    PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.before i)) (H.seen i) := by
  induction i with
  | zero =>
      rw [H.initial_seen]
      exact original_initial_vacuum_good_orbit
        SP smallMod BP bigMod J ell cap
        (H.before 0) H.initial_births_nodup H.initial_vacuum
  | succ i ih =>
      have hlt : i < N := Nat.lt_of_succ_le hi
      have hPrev := ih (Nat.le_of_lt hlt)
      have hNext := actual_full_GE_preserves_physical_good_orbit
        SP smallMod BP bigMod J ell m cap patterns
        q rho N i Vbig muBig
        (H.before i) (H.afterG i) (H.beforeE i)
        (H.ghost i) (physicalAlternatingSign i) k
        (H.edge i) (H.seen i) hPrev
        (H.G_nonzero i (Nat.le_of_lt hlt))
        (H.G_birth_eligible i (Nat.le_of_lt hlt))
        (H.E_orbit_input i hlt) (H.E_legal i hlt)
        (H.E_birth_eligible i hlt)
      rw [H.E_output i hlt, H.seen_update i hlt]
      exact hNext

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostSetTransition -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The ORIGINAL physical G witness enforces exact old-index
deletion and ghost births on the actual next Fock representative.
No Markov abstraction and no hypothesis about source row weights. -/
theorem actual_physical_path_big_G_value_support
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i ≤ N) (g : BG) :
    ((Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)).toFinset =
      (((Finset.univ : Finset
          (Fin (Green64Fock.fockToList
            (((H.before i).2 g).2)).length)) \
        ((H.ghost i g).1.1)).image
         (fun j => ((Green64Fock.fockToList
            (((H.before i).2 g).2)).get j).1)) ∪
      ((Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => ((H.ghost i g).2.2 j).1)) := by
  classical
  have hG := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i hi)).2 g
  rw [← hG]
  exact ghost_actual_value_support
    (Green64Fock.fockToList (((H.before i).2 g).2))
    ((H.ghost i g).1.1) ((H.ghost i g).2.2)
    (fun a : Green64Fock.Atom (BP g) (bigMod g) => a.1)

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostValueConservation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Actual BIG G witness: terminal OLD prime values are removed
once, nonterminated OLD values remain, and exactly the G ghost
birth values are added. Nodup comes from the genuine path invariant. -/
theorem actual_physical_path_big_G_value_conservation
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i ≤ N) (g : BG) :
    let old := Green64Fock.fockToList (((H.before i).2 g).2)
    let A := (H.ghost i g).1.1
    let fresh := (H.ghost i g).2.2
    ((Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)).toFinset =
      ((old.map (fun a => a.1)).toFinset \
        A.image (fun j => (old.get j).1)) ∪
      (Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => (fresh j).1) := by
  dsimp only
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi) g
  have hOldNodup :
      ((Green64Fock.fockMultiset (((H.before i).2 g).2)).map
        (fun z => z.1)).Nodup := hGood.2.1
  exact nonzero_physical_G_value_set_update
    SP smallMod BP bigMod (J+ell) cap q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i hi) g hOldNodup

end Green64FullPhysicalE

end

