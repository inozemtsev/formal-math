module

public import Green64.Library.Correlation.B26FrozenCleanPhysicalFourier
public import Green64.Library.Correlation.Part006
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Weights / B26CleanSmallCoherentPairing

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26CleanSmallCoherentPairing -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

abbrev SourceOriginalB26SharedTuple434 :=
  (g : SG) → ↥(sourceSmallShared J ell g) → SP g
abbrev SourceOriginalB26OldResidues434 :=
  (g : BG) → (i : Fin (sizes g)) → ZMod (bigMod g (prime g i))

local notation "Small" => Green64SmallHaar.GroupState SP smallMod (J+ell)
local notation "SmallTorus" => Green64SmallHaar.GroupTorus SP smallMod
local notation "SmallPerm" => Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bigMod sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns

/-- The actual SMALL shared product, expressed on the true P_d fibre. -/
def sourceOriginalB26SmallTupleD434 (d : Shared) : ℕ :=
  ∏ g : SG, ∏ i : ↥(sourceSmallShared J ell g), smallMod g (d g i)

private theorem actual_small_tuple_D434 (xs : Small) (ss : SmallPerm) :
    sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss =
      sourceOriginalB26SmallTupleD434 SP smallMod J ell
        (memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
          (sourceSmallShared J ell) ss xs) := by
  unfold sourceOriginalB26SmallSourceD434 sourceOriginalB26SmallTupleD434
  apply Finset.prod_congr rfl
  intro g _
  simpa only [Finset.univ_eq_attach, memoryOriginalSmallGroupSharedLabels,
    memoryOriginalSmallSharedLabels] using
    (Finset.prod_attach (sourceSmallShared J ell g)
      (fun i => smallMod g
        (Green64SmallHaar.marks (smallMod g) (J+ell) (xs g) (ss g i)))).symm

/-- Genuine B26 P_d applied to a physical endpoint test in an ordered OLD
sector. OLD residues remain variables; both independently sampled SMALL
permutations are used separately when the two endpoint maps are paired. -/
def sourceOriginalB26SmallLift434 (q : ℝ) (Vs : SG → ℝ)
    (ss : SmallPerm) (d : Shared) (U : Small → Active → Old → ℂ)
    (a : Active) (r : Torus) : ℂ :=
  memoryOriginalSmallPermutedHalfMap SP smallMod J ell q Vs
    (sourceSmallShared J ell) ss d r.1 (fun xs => U xs a r.2)

private theorem small_lift_star434 (q : ℝ) (Vs : SG → ℝ)
    (ss : SmallPerm) (d : Shared) (U : Small → Active → Old → ℂ)
    (a : Active) (r : Torus) :
    sourceOriginalB26SmallLift434 SP smallMod BP bigMod J ell sizes prime q Vs
      ss d (fun xs a t => (starRingEnd ℂ) (U xs a t)) a r =
    (starRingEnd ℂ) (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q Vs ss d U a r) := by
  simp [sourceOriginalB26SmallLift434, memoryOriginalSmallPermutedHalfMap]

private theorem shared_card434 (g : SG) :
    (sourceSmallShared J ell g).card = J := by
  let e : Fin J ≃ ↥(sourceSmallShared J ell g) :=
    { toFun := fun j => ⟨⟨j.val, by omega⟩, by simp [sourceSmallShared, j.isLt]⟩
      invFun := fun j => ⟨j.val.val, by
        simpa only [sourceSmallShared, Finset.mem_filter, Finset.mem_univ, true_and]
          using j.property⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; apply Subtype.ext; rfl }
  simpa using (Fintype.card_congr e).symm

/-- Joint moving fibre factorization. The output test v depends on the SAME
shared tuple that determines the displacement; no output independence is
assumed. This helper applies the existing exact B26 finite disintegration. -/
private theorem moving_small_P434
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (ss tt : SmallPerm) (step : Shared → ℤ) (W : Shared → ℂ)
    (u : Small → ℂ) (v : Shared → Small → ℂ) :
    (∑ xs : Small, ∑ ys : Small,
      W (memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
          (sourceSmallShared J ell) ss xs) *
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vs
        (sourceSmallShared J ell)
        (step (memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
          (sourceSmallShared J ell) ss xs)) (fun _ _ => 1) ss tt xs ys *
      u xs * v (memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
          (sourceSmallShared J ell) ss xs) ys) =
    ∑ d : Shared, ∑ y : SmallTorus,
      W d * memoryOriginalSmallPermutedHalfMap SP smallMod J ell q Vs
        (sourceSmallShared J ell) ss d y u *
      memoryOriginalSmallPermutedHalfMap SP smallMod J ell q Vs
        (sourceSmallShared J ell) tt d
        (Green64SmallHaar.groupTranslate SP smallMod (step d) y) (v d) := by
  classical
  let a := memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
    (sourceSmallShared J ell) ss
  let b := memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
    (sourceSmallShared J ell) tt
  let r := memoryOriginalSmallGroupResidue SP smallMod (J+ell)
  let tr := fun d => Green64SmallHaar.groupTranslate SP smallMod (step d)
  let A := memoryOriginalSmallGroupPhysicalEndpointHalf SP smallMod J ell q Vs
  let H := fun xs ys : Small =>
    W (a xs) * (Green64SmallHaar.groupEdgeScalar SP smallMod
      (J+ell) q Vs (sourceSmallShared J ell) xs ys : ℂ) * u xs * v (a xs) ys
  have hf := memory_finite_moving_step_two_endpoint_fibres a b r r tr H
  calc
    _ = ∑ xs : Small, ∑ ys : Small,
        if a xs = b ys ∧ r ys = tr (a xs) (r xs) then H xs ys else 0 := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      have hc := memory_original_small_group_edge_conditional_iff
        SP smallMod (J+ell) (sourceSmallShared J ell) (step (a xs)) ss tt xs ys
      change _ = if a xs = b ys ∧ r ys = tr (a xs) (r xs) then H xs ys else 0
      change W (a xs) * Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
          q Vs (sourceSmallShared J ell) (step (a xs)) (fun _ _ => 1) ss tt xs ys *
          u xs * v (a xs) ys = _
      have hc' : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
          (sourceSmallShared J ell) (step (a xs)) ss tt xs ys ↔
          a xs = b ys ∧ r ys = tr (a xs) (r xs) := hc
      unfold Green64SmallHaar.groupPermutedKernel
      by_cases he : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
          (sourceSmallShared J ell) (step (a xs)) ss tt xs ys
      · rw [if_pos he, if_pos (hc'.mp he)]
        simp only [one_mul, H]
      · rw [if_neg he, if_neg (fun hh => he (hc'.mpr hh))]
        ring
    _ = ∑ d : Shared, ∑ y : SmallTorus,
        ∑ xs ∈ memoryFiniteConditionalFibre a r d y,
          ∑ ys ∈ memoryFiniteConditionalFibre b r d (tr d y), H xs ys := by
      convert hf using 1
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      by_cases hh : a xs = b ys ∧ r ys = tr (a xs) (r xs) <;> simp [hh]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      calc
        _ = ∑ xs ∈ memoryFiniteConditionalFibre a r d y,
              ∑ ys ∈ memoryFiniteConditionalFibre b r d (tr d y),
                W d * ((A y : ℂ) * (A (tr d y) : ℂ)) * u xs * v d ys := by
          apply Finset.sum_congr rfl
          intro xs hx
          apply Finset.sum_congr rfl
          intro ys hy
          have hx' : a xs = d ∧ r xs = y := by
            simpa only [memoryFiniteConditionalFibre, Finset.mem_filter,
              Finset.mem_univ, true_and] using hx
          have hy' : b ys = d ∧ r ys = tr d y := by
            simpa only [memoryFiniteConditionalFibre, Finset.mem_filter,
              Finset.mem_univ, true_and] using hy
          have hh := memory_original_small_group_edge_scalar_half_exact SP smallMod
            J ell q hq Vs hVs (sourceSmallShared J ell)
            (fun g => shared_card434 J ell g) xs ys
          change Green64SmallHaar.groupEdgeScalar SP smallMod (J+ell) q Vs
            (sourceSmallShared J ell) xs ys = A (r xs) * A (r ys) at hh
          rw [hx'.2, hy'.2] at hh
          dsimp only [H]
          rw [hx'.1, hh, Complex.ofReal_mul]
        _ = W d * ((A y : ℂ) *
              ∑ xs ∈ memoryFiniteConditionalFibre a r d y, u xs) *
            ((A (tr d y) : ℂ) *
              ∑ ys ∈ memoryFiniteConditionalFibre b r d (tr d y), v d ys) :=
          memory_finite_original_two_endpoint_tensor _ _ u (v d) (W d) _ _
        _ = _ := rfl

/-- Literal original CLEAN source coefficient, with all original legality,
auxiliary bans, complex Knu and both endpoint permutation masses. The target
OLD test is evaluated at the actual original source displacement. -/
def sourceOriginalB26IndexedCleanFramePair434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (U F : Small → Active → Old → ℂ)
    (ss tt : SmallPerm) (a : Active) (t : Old) (h : Frame) (b : Active) : ℂ :=
  ∑ xs : Small, ∑ ys : Small,
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a t)
    let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns xs ys a (0,t) h b ss tt
    let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns h.1) h.2.1 x h.2.2.1 ss o k
    (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z
      then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x z else 0) *
    (starRingEnd ℂ) (U xs a t) *
    F ys b (fun g i => t g i + (step : ZMod (bigMod g (prime g i))))

private theorem physical_weight_as_big434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b =
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b := by
  unfold sourceOriginalB26FrozenPhysicalWeight434 sourceOriginalB26FrozenBigWeight434
  dsimp only
  rw [source_original_B26_FROZEN_PHYSICAL_coefficient434]

/-- Exact joint SMALL/OLD P_d factorization of a literal original CLEAN
frame. The OLD target translation is frozen only AFTER actual conditioning.
No absolute values, per-row saving, or independent output law enter. -/
theorem source_original_B26_MOVING_SMALL_CLEAN_FRAME_PAIR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (U F : Small → Active → Old → ℂ)
    (ss tt : SmallPerm) (a : Active) (t : Old) (h : Frame) (b : Active) :
    sourceOriginalB26IndexedCleanFramePair434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
      U F ss tt a t h b =
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    ∑ d : Shared, ∑ y : SmallTorus,
      (starRingEnd ℂ) (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a (y,t)) *
      sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K
        (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
        zeta theta o k a (y,t) h b *
      sourceOriginalB26SmallLift434 SP smallMod BP bigMod J ell sizes prime
        q Vs tt d F b ((y,t) + memoryFrozenResidueShift SP smallMod BP bigMod sizes prime
          (o*k*(sourceOriginalB26FrozenD434 BP bigMod J ell m
            (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
            (patterns h.1) h.2.1 a h.2.2.1 : ℤ))) := by
  let D := fun d : Shared => sourceOriginalB26FrozenD434 BP bigMod J ell m
    (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
    (patterns h.1) h.2.1 a h.2.2.1
  let step := fun d : Shared => o*k*(D d : ℤ)
  let W := fun d : Shared => sourceOriginalB26FrozenBigWeight434 BP bigMod
    J ell m patterns mu V K (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
    zeta theta o k a h b
  let u := fun xs : Small => (starRingEnd ℂ) (U xs a t)
  let v := fun (d : Shared) (ys : Small) =>
    F ys b (fun g i => t g i + (step d : ZMod (bigMod g (prime g i))))
  let labels := memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell)
    (sourceSmallShared J ell) ss
  have hp := moving_small_P434 SP smallMod J ell q hq Vs hVs ss tt step W u v
  calc
    _ = (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
        (∑ xs : Small, ∑ ys : Small,
          W (labels xs) * Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
            q Vs (sourceSmallShared J ell) (step (labels xs))
            (fun _ _ => 1) ss tt xs ys * u xs * v (labels xs) ys) := by
      unfold sourceOriginalB26IndexedCleanFramePair434
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      rw [source_original_B26_FROZEN_ORIGINAL_CLEAN_SUMMAND434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        xs ys a (0,t) h b ss tt,
        physical_weight_as_big434 SP smallMod BP bigMod J ell m cap sizes hsizes prime,
        actual_small_tuple_D434 SP smallMod J ell xs ss]
      have hs : sourceOrientedStep SP smallMod BP bigMod J ell m cap
          (patterns h.1) h.2.1
          (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
            sizes hsizes prime a t) h.2.2.1 ss o k = step (labels xs) := by
        change o*k*(sourceOriginalB26FrozenD434 BP bigMod J ell m
          (sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss)
          (patterns h.1) h.2.1 a h.2.2.1 : ℤ) = _
        rw [actual_small_tuple_D434 SP smallMod J ell xs ss]
      rw [hs]
      dsimp only [W, u, v, labels, step, D]
      ring
    _ = (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
        ∑ d : Shared, ∑ y : SmallTorus,
          W d * memoryOriginalSmallPermutedHalfMap SP smallMod J ell q Vs
            (sourceSmallShared J ell) ss d y u *
          memoryOriginalSmallPermutedHalfMap SP smallMod J ell q Vs
            (sourceSmallShared J ell) tt d
            (Green64SmallHaar.groupTranslate SP smallMod (step d) y) (v d) := by
      rw [hp]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      rw [physical_weight_as_big434 SP smallMod BP bigMod J ell m cap sizes hsizes prime]
      have hu := small_lift_star434 SP smallMod BP bigMod J ell sizes prime
        q Vs ss d U a (y,t)
      dsimp only [sourceOriginalB26SmallLift434] at hu ⊢
      rw [← hu]
      dsimp only [sourceOriginalB26SmallLift434, W, u, v, step, D,
        memoryFrozenResidueShift, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
      ring_nf
      rfl


private theorem sum_four_interchange434
    {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

/-- Exact original source mass in the ordered frozen OLD sector, including
SMALL Haar and V^(-M), BIG active prime masses, and every Fock 1/j!. -/
def sourceOriginalB26SectorMass434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (a : Active) : ℝ :=
  Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vs *
  bigGroupStateMass BP bigMod (J+ell) cap mu
    (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a 0)

theorem source_original_B26_SECTOR_PHYSICAL_MASS434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (xs : Small) (a : Active) (t : Old) :
    fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu
      (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a t) =
    sourceOriginalB26SectorMass434 SP smallMod BP bigMod J ell cap sizes hsizes prime
      Vs mu a := rfl

/-- Coherent original CLEAN pairing in one ordered OLD sector. All original
Nu/aux/BIG permutations, active outputs, and BOTH SMALL permutations are
summed with their original coefficients before taking any norm. -/
def sourceOriginalB26SectorCleanPair434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (U F : Small → Active → Old → ℂ) : ℂ :=
  ∑ ss : SmallPerm, ∑ tt : SmallPerm, ∑ a : Active, ∑ t : Old,
    (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu a : ℂ) *
      ∑ h : Frame, ∑ b : Active,
        sourceOriginalB26IndexedCleanFramePair434 SP smallMod BP bigMod
          J ell m cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          U F ss tt a t h b

private theorem coherent_small_at_source434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (U F : Small → Active → Old → ℂ)
    (ss tt : SmallPerm) (a : Active) (t : Old) :
    (∑ h : Frame, ∑ b : Active,
      sourceOriginalB26IndexedCleanFramePair434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        U F ss tt a t h b) =
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    ∑ d : Shared, ∑ y : SmallTorus,
      (starRingEnd ℂ) (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a (y,t)) *
      sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K
        (sourceOriginalB26SmallTupleD434 SP smallMod J ell d) zeta theta o k
        (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
          J ell sizes prime q Vs tt d F) a (y,t) := by
  simp_rw [source_original_B26_MOVING_SMALL_CLEAN_FRAME_PAIR434 SP smallMod
    BP bigMod J ell m cap sizes hsizes prime patterns mu V K q hq Vs hVs]
  simp only [← Finset.mul_sum]
  congr 1
  rw [sum_four_interchange434]
  unfold sourceOriginalB26FrozenPhysicalOp434
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Genuine P_d--coherent CLEAN--P_d factorization of the original weighted
sector pairing. The whole signed history sum remains INSIDE E_frozen.
No global birth-distinctness gate or DIRTY term is removed by this identity. -/
theorem source_original_B26_CLEAN_SMALL_COHERENT_PAIR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (U F : Small → Active → Old → ℂ) :
    sourceOriginalB26SectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F =
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    ∑ ss : SmallPerm, ∑ tt : SmallPerm, ∑ d : Shared, ∑ a : Active, ∑ r : Torus,
      (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu a : ℂ) *
      (starRingEnd ℂ) (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a r) *
      sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K
        (sourceOriginalB26SmallTupleD434 SP smallMod J ell d) zeta theta o k
        (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
          J ell sizes prime q Vs tt d F) a r := by
  unfold sourceOriginalB26SectorCleanPair434
  simp_rw [coherent_small_at_source434 SP smallMod BP bigMod J ell m cap
    sizes hsizes prime patterns mu V K q hq Vs hVs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  rw [sum_four_interchange434]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro t _
  ring


private theorem fourier_dual_coefficient434
    {G : Type} [Fintype G] [AddCommGroup G]
    (f : G → ℂ) (psi : AddChar G ℂ) :
    (∑ r : G, (starRingEnd ℂ) (f r) * psi r) =
      (Fintype.card G : ℂ) *
        (starRingEnd ℂ) ((AddChar.complexBasis G).repr f psi) := by
  have orth (phi : AddChar G ℂ) :
      (∑ r : G, (starRingEnd ℂ) (phi r) * psi r) =
        if phi = psi then (Fintype.card G : ℂ) else 0 := by
    have h := AddChar.wInner_cWeight_eq_boole phi psi
    have h' : (∑ r : G, (starRingEnd ℂ) (phi r) * psi r) /
        (Fintype.card G : ℂ) = if phi = psi then 1 else 0 := by
      simpa only [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
        RCLike.inner_apply, mul_comm] using h
    have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hh := (div_eq_iff hn).mp h'
    split_ifs at hh ⊢ <;> simpa using hh
  have he (r : G) : f r = ∑ phi : AddChar G ℂ,
      (AddChar.complexBasis G).repr f phi * phi r := by
    have h := congrFun ((AddChar.complexBasis G).sum_repr f) r
    simpa only [AddChar.complexBasis_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  calc
    _ = ∑ r : G, ∑ phi : AddChar G ℂ,
        (starRingEnd ℂ) ((AddChar.complexBasis G).repr f phi) *
          (starRingEnd ℂ) (phi r) * psi r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [he]
      simp only [map_sum, map_mul, Finset.sum_mul]
    _ = ∑ phi : AddChar G ℂ,
        (starRingEnd ℂ) ((AddChar.complexBasis G).repr f phi) *
          (∑ r : G, (starRingEnd ℂ) (phi r) * psi r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro phi _
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      simp_rw [orth]
      simp [mul_ite, mul_comm]

private theorem coherent_fourier_pair434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (U F : Active → Torus → ℂ) (a : Active) :
    (∑ r : Torus, (starRingEnd ℂ) (U a r) *
      sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k F a r) =
    (Fintype.card Torus : ℂ) * ∑ psi : AddChar Torus ℂ,
      (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr (U a) psi) *
      sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K dsmall zeta
        (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
          (2*Real.pi)) o k
        (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a := by
  simp_rw [source_original_B26_FROZEN_COHERENT_FOURIER434]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  let B := sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
    dsmall zeta
    (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
      (2*Real.pi)) o k (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a
  change (∑ r : Torus, (starRingEnd ℂ) (U a r) * (B * psi r)) = _
  calc
    _ = B * (∑ r : Torus, (starRingEnd ℂ) (U a r) * psi r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [fourier_dual_coefficient434]
      dsimp only [B]
      ring

/-- Exact ORIGINAL SMALL P_d pairing with the complete coherent Fourier
blocks. Cardinality is the original SMALL times indexed OLD torus size;
the sector mass still contains the genuine Haar, V and factorial factors.
Complex phases and BOTH endpoint tests remain present in this bilinear
identity. It asserts no smallness of any arithmetic block. -/
theorem source_original_B26_CLEAN_SMALL_PHYSICAL_FOURIER_PAIR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (U F : Small → Active → Old → ℂ) :
    sourceOriginalB26SectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F =
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    (Fintype.card Torus : ℂ) *
    ∑ ss : SmallPerm, ∑ tt : SmallPerm, ∑ d : Shared, ∑ a : Active,
      ∑ psi : AddChar Torus ℂ,
      (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu a : ℂ) *
      (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr
        (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
          J ell sizes prime q Vs ss d U a) psi) *
      sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
        (sourceOriginalB26SmallTupleD434 SP smallMod J ell d) zeta
        (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
          (2*Real.pi)) o k
        (fun b => (AddChar.complexBasis Torus).repr
          (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
            J ell sizes prime q Vs tt d F b) psi) a := by
  rw [source_original_B26_CLEAN_SMALL_COHERENT_PAIR434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns mu V K q hq Vs hVs]
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_assoc]
  rw [← Finset.mul_sum, coherent_fourier_pair434]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro psi _
  ring


private theorem empty_choice_unique434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (M B : ℕ) (x : BigState modulus M B)
    (c : BigEdgeChoice modulus M B x) (hs : c.1 = ∅) (hp : c.2.1 = ∅) :
    c = sourceOriginalB26EmptyCleanChoice434 modulus M B x := by
  rcases c with ⟨s,p,e⟩
  dsimp only at hs hp
  subst s
  subst p
  unfold sourceOriginalB26EmptyCleanChoice434
  congr 2
  ext i
  exact (Finset.notMem_empty _ i.property).elim

/-- Exhaustive parametrization, not merely an injection of selected clean
histories. The only injection from an empty promotion set is the original
empty choice; all actual CLEAN source choices occur exactly once. -/
def sourceOriginalB26CleanChoiceEquiv434
    (xs : Small) (a : Active) (t : Old) :
    (Frame × Active × Small × SmallPerm × SmallPerm) ≃
      {z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns
        (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
          sizes hsizes prime a t) //
       memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns
         (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
           sizes hsizes prime a t) z} where
  toFun p := ⟨sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns xs p.2.2.1 a (0,t) p.1 p.2.1
    p.2.2.2.1 p.2.2.2.2, by intro g; exact ⟨rfl,rfl⟩⟩
  invFun z := (⟨z.1.1, z.1.2.1, z.1.2.2.1.sigmaBig, z.1.2.2.1.tauBig⟩,
    (fun g => (z.1.2.2.1.bigChoice g).1), z.1.2.2.1.smallTarget,
    z.1.2.2.2.1, z.1.2.2.2.2)
  left_inv := by
    rintro ⟨⟨nu,aux,sigma,tau⟩,b,ys,ss,tt⟩
    rfl
  right_inv := by
    rintro ⟨⟨nu,aux,⟨sigma,tau,c,ys⟩,ss,tt⟩,hc⟩
    apply Subtype.ext
    have he : (fun g => ((c g).1,
        sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell) (cap g)
          (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
            sizes hsizes prime a t g))) = c := by
      funext g
      apply Prod.ext
      · rfl
      · exact (empty_choice_unique434 (bigMod g) (J+ell) (cap g) _ (c g).2
        (hc g).1 (hc g).2).symm
    exact congrArg (fun c =>
      (⟨nu,aux,⟨sigma,tau,c,ys⟩,ss,tt⟩ :
        FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns
          (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
            sizes hsizes prime a t))) he

/-- Literal ORIGINAL clean-choice sum equals the full frame/active/SMALL
parametrization used by the coherent pairing, for any complex summand. -/
theorem source_original_B26_CLEAN_CHOICES_EXHAUSTIVE434
    (xs : Small) (a : Active) (t : Old)
    (H : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns
      (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
        sizes hsizes prime a t) → ℂ) :
    (∑ z, if memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns
      (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
        sizes hsizes prime a t) z then H z else 0) =
    ∑ h : Frame, ∑ b : Active, ∑ ys : Small, ∑ ss : SmallPerm, ∑ tt : SmallPerm,
      H (sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns xs ys a (0,t) h b ss tt) := by
  let clean := memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns
    (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a t)
  change (∑ z, if clean z then H z else 0) = _
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := clean) (F := inferInstance) _ (by intro z; simp)]
  have he := (sourceOriginalB26CleanChoiceEquiv434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns xs a t).sum_comp (fun z => H z.1)
  simpa [Fintype.sum_prod_type, sourceOriginalB26CleanChoiceEquiv434, clean] using he.symm

/-- True output test pulled back from the original symmetric Fock carrier.
This does not select one representative of a repeated OLD multiset. -/
def sourceOriginalB26TargetPullback434
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (ys : Small) (b : Active) (t : Old) : ℂ :=
  F (ys, fun g => (b g, Green64Fock.fockMultiset
    ((sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime b t g).2)))

def sourceOriginalB26SourcePullback434
    (U : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (xs : Small) (a : Active) (t : Old) : ℂ :=
  U (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a t)

/-- The indexed CLEAN target is the LITERAL sourceOrientedPhysicalOutput,
including the original simultaneous translation of every OLD occurrence. -/
theorem source_original_B26_CLEAN_LITERAL_OUTPUT434
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (xs ys : Small) (a b : Active) (t : Old) (h : Frame) (ss tt : SmallPerm) (o k : ℤ) :
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a t)
    let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns xs ys a (0,t) h b ss tt
    let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns h.1) h.2.1 x h.2.2.1 ss o k
    F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z) =
      sourceOriginalB26TargetPullback434 SP smallMod BP bigMod J ell cap sizes hsizes prime
        F ys b (fun g i => t g i + (step : ZMod (bigMod g (prime g i)))) := by
  dsimp only
  unfold sourceOriginalB26TargetPullback434
  congr 1
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · exact source_original_B26_FROZEN_pending_output434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime a (0,t) h.2.2.1 _ g

/-- The full ORIGINAL unmarked CLEAN operator at one actual source state,
written on the exhaustive frame parameters and the genuine symmetric output.
The birth-distinctness predicate is not part of this local unmarked operator. -/
theorem source_original_B26_CLEAN_LITERAL_ROW434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (xs : Small) (a : Active) (t : Old) :
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a t)
    (∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns x o k,
      if memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z
      then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x z *
        F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z)
      else 0) =
    ∑ h : Frame, ∑ b : Active, ∑ ys : Small, ∑ ss : SmallPerm, ∑ tt : SmallPerm,
      let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns xs ys a (0,t) h b ss tt
      let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns h.1) h.2.1 x h.2.2.1 ss o k
      (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z
        then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q 1 Vs V mu K zeta theta o k x z else 0) *
      sourceOriginalB26TargetPullback434 SP smallMod BP bigMod J ell cap sizes hsizes prime
        F ys b (fun g i => t g i + (step : ZMod (bigMod g (prime g i)))) := by
  dsimp only
  let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
    sizes hsizes prime a t)
  let H := fun z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x =>
    (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z
      then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x z else 0) *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z)
  have he := source_original_B26_CLEAN_CHOICES_EXHAUSTIVE434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns xs a t H
  calc
    _ = ∑ z, if memorySourceCleanChoice SP smallMod BP bigMod
        J ell m cap patterns x z then H z else 0 := by
      unfold sourceOrientedPhysicalChoices
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [H]
      by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod
        J ell m cap patterns x o k z <;>
      by_cases hc : memorySourceCleanChoice SP smallMod BP bigMod
        J ell m cap patterns x z <;> dsimp only [x] at hl hc <;> simp [x, hl, hc]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro ys _
      apply Finset.sum_congr rfl
      intro ss _
      apply Finset.sum_congr rfl
      intro tt _
      dsimp only [H]
      rw [source_original_B26_CLEAN_LITERAL_OUTPUT434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns F xs ys a b t h ss tt o k]


private theorem sum_eight_reindex434
    {A B C D E F G H : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] [Fintype G] [Fintype H]
    (f : A → B → C → D → E → F → G → H → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f', ∑ g, ∑ h, f a b c d e f' g h) =
      ∑ g, ∑ h, ∑ a, ∑ b, ∑ d, ∑ e, ∑ c, ∑ f', f a b c d e f' g h := by
  let e : (G × H × A × B × D × E × C × F) ≃
      (A × B × C × D × E × F × G × H) :=
    { toFun := fun ⟨g,h,a,b,d,e,c,f⟩ => (a,b,c,d,e,f,g,h)
      invFun := fun ⟨a,b,c,d,e,f,g,h⟩ => (g,h,a,b,d,e,c,f)
      left_inv := by rintro ⟨g,h,a,b,d,e,c,f⟩; rfl
      right_inv := by rintro ⟨a,b,c,d,e,f,g,h⟩; rfl }
  have he := e.sum_comp (fun p =>
    f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)
  simpa [Fintype.sum_prod_type, e] using he.symm

/-- Literal full ORIGINAL unmarked CLEAN bilinear pairing in this ordered
OLD-prime sector, using original source choices, original legality, original
physical mass and original symmetric output. No reindexed proxy occurs in
this definition. The algebraic reference rho=1 has the previously proved
OLD endpoint multipliers outside it. -/
def sourceOriginalB26LiteralSectorCleanPair434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (U : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℂ :=
  ∑ a : Active, ∑ t : Old, ∑ xs : Small,
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a t)
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x : ℂ) *
      (starRingEnd ℂ) (U x) *
      ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns x o k,
        if memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z then
          sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
            q 1 Vs V mu K zeta theta o k x z *
          F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z)
        else 0

/-- Exhaustive equality with the literal original CLEAN operator pairing,
including the original Hilbert measure and actual symmetric output tests. -/
theorem source_original_B26_CLEAN_LITERAL_SECTOR_PAIR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (U : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    sourceOriginalB26LiteralSectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F =
    sourceOriginalB26SectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k
      (sourceOriginalB26SourcePullback434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime U)
      (sourceOriginalB26TargetPullback434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime F) := by
  unfold sourceOriginalB26LiteralSectorCleanPair434
  dsimp only
  simp_rw [source_original_B26_CLEAN_LITERAL_ROW434,
    source_original_B26_SECTOR_PHYSICAL_MASS434]
  unfold sourceOriginalB26SectorCleanPair434 sourceOriginalB26IndexedCleanFramePair434
  simp only [sourceOriginalB26SourcePullback434, Finset.mul_sum]
  rw [sum_eight_reindex434]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  ring

/-- Square root of the genuine SMALL source mark mass. Multiplying both
endpoint half maps by this factor moves V^(-M) out of the ambient measure,
producing exactly the source P_d joint normalization V^(-M-ell). -/
def sourceOriginalB26SmallMarkScale434 (Vs : SG → ℝ) : ℝ :=
  Real.sqrt (∏ g : SG, 1 / (Vs g)^(J+ell))

def sourceOriginalB26PhysicalSmallLift434
    (q : ℝ) (Vs : SG → ℝ) (ss : SmallPerm) (d : Shared)
    (U : Small → Active → Old → ℂ) (a : Active) (r : Torus) : ℂ :=
  (sourceOriginalB26SmallMarkScale434 (SG := SG) J ell Vs : ℂ) *
    sourceOriginalB26SmallLift434 SP smallMod BP bigMod J ell sizes prime q Vs ss d U a r

private theorem sector_mass_scale434
    (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (a : Active) (r : Torus) :
    sourceOriginalB26SectorMass434 SP smallMod BP bigMod J ell cap sizes hsizes prime
      Vs mu a =
    sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod J ell cap sizes hsizes prime
      mu a r * (sourceOriginalB26SmallMarkScale434 (SG := SG) J ell Vs)^2 := by
  have hn : 0 ≤ ∏ g : SG, 1 / (Vs g)^(J+ell) := by
    apply Finset.prod_nonneg
    intro g _
    have hv := hVs g
    positivity
  have hs : (sourceOriginalB26SmallMarkScale434 (SG := SG) J ell Vs)^2 =
      ∏ g : SG, 1 / (Vs g)^(J+ell) := Real.sq_sqrt hn
  have hm : Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vs =
      Green64SmallHaar.groupHaarMass SP smallMod *
      (sourceOriginalB26SmallMarkScale434 (SG := SG) J ell Vs)^2 := by
    rw [hs]
    simp only [Green64SmallHaar.groupStateMass, Green64SmallHaar.stateMass,
      Green64SmallHaar.groupHaarMass, Finset.prod_mul_distrib]
  change Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vs *
      bigGroupStateMass BP bigMod (J+ell) cap mu
        (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a 0) =
    (Green64SmallHaar.groupHaarMass SP smallMod *
      bigGroupStateMass BP bigMod (J+ell) cap mu
        (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a 0)) * _
  rw [hm]
  ring

/-- Exact source P_d normalization, not a norm comparison: moving the SMALL
source mark mass to the two endpoint maps preserves the physical signed
joint pairing. SMALL Haar and all BIG factorial-Fock weights stay in the
ambient mass. This matches the original transference P_d convention. -/
theorem source_original_B26_PHYSICAL_P_JOINT_NORMALIZATION434
    (q : ℝ) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (ss tt : SmallPerm) (d : Shared)
    (U F : Small → Active → Old → ℂ) (a b : Active) (r s : Torus) :
    (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu a : ℂ) *
      (starRingEnd ℂ) (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a r) *
      sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs tt d F b s =
    (sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime mu a r : ℂ) *
      (starRingEnd ℂ) (sourceOriginalB26PhysicalSmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a r) *
      sourceOriginalB26PhysicalSmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs tt d F b s := by
  rw [sector_mass_scale434 SP smallMod BP bigMod J ell cap sizes hsizes prime Vs hVs mu a r]
  unfold sourceOriginalB26PhysicalSmallLift434
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, map_mul, Complex.conj_ofReal]
  ring

/-- Final exact bridge for this iteration: the literal original unmarked
CLEAN bilinear pairing equals the coherent frequency pairing between the
actual source SMALL conditional maps. It applies to arbitrary original
endpoint tests, hence does not replace any endpoint parity projector.
Arithmetic smallness of these canonical blocks remains a separate task. -/
theorem source_original_B26_ORIGINAL_CLEAN_SMALL_FOURIER434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g, 0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ)
    (U : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    let PU := sourceOriginalB26SmallLift434 SP smallMod BP bigMod J ell sizes prime q Vs
      (U := sourceOriginalB26SourcePullback434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime U)
    let PF := sourceOriginalB26SmallLift434 SP smallMod BP bigMod J ell sizes prime q Vs
      (U := sourceOriginalB26TargetPullback434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime F)
    sourceOriginalB26LiteralSectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F =
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    (Fintype.card Torus : ℂ) *
    ∑ ss : SmallPerm, ∑ tt : SmallPerm, ∑ d : Shared, ∑ a : Active,
      ∑ psi : AddChar Torus ℂ,
      (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu a : ℂ) *
      (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr (PU ss d a) psi) *
      sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
        (sourceOriginalB26SmallTupleD434 SP smallMod J ell d) zeta
        (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
          (2*Real.pi)) o k
        (fun b => (AddChar.complexBasis Torus).repr (PF tt d b) psi) a := by
  dsimp only
  rw [source_original_B26_CLEAN_LITERAL_SECTOR_PAIR434]
  exact source_original_B26_CLEAN_SMALL_PHYSICAL_FOURIER_PAIR434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns mu V K q hq Vs hVs zeta theta o k _ _

set_option pp.fullNames true
end Green64FullPhysicalE

end

end

