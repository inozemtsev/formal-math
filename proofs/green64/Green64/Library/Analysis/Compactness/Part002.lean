module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Green64.Library.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
public import Green64.Library.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
public import Green64.Library.Analysis.Compactness.Part001
public import Green64.Library.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
public import Mathlib
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Analysis / Compactness / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich -/

section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceRellich : MeasurableSpace E := borel E
local instance instBorelSpaceRellich : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceRellich : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddRellich : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegRellich : MeasurableNeg E := by
  infer_instance
local instance instFactOneLeTwoSobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ### Supported `H¹` subspace -/

/-- The subspace of `H¹(volume)` whose `L²` component is (a.e.) supported in `K`.

We model “supported in `K`” as belonging to the closed range of the extension-by-zero map
`Lp(volume.restrict K) →ₗᵢ Lp(volume)`. -/
noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

/-- The inclusion `h1On K → L²(volume)` as a continuous linear map. -/
noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL

/-! ### Euclidean Rellich on fixed compact support -/

/-- Euclidean Rellich–Kondrachov compactness (Lebesgue): on a fixed compact support `K`, the
inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1OnToL2 {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    ‖h1ToL2 (μ := (volume : Measure E)) (E := E)‖
  have hCnonneg : 0 ≤ C := by
    exact norm_nonneg (h1ToL2 (μ := (volume : Measure E)) (E := E))
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      -- `h1On` inherits the ambient norm, so this is definitional.
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        simpa [T, h1OnToL2, C] using h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (deltaLoss := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_ofPred_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (deltaLoss := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          -- Unfold membership in the defining `comap` without
          -- letting `simp` use `x.property`
          -- (which would rewrite the goal to `True`).
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  -- Use the topological definition of `IsCompactOperator` to avoid expensive normed-space
  -- characterizations.
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

omit [CompleteSpace E] in
lemma isClosed_range_extendByZero (K : Set E) (hKm : MeasurableSet K) :
    IsClosed
      (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) :
        Set (E →₂[(volume : Measure E)] ℝ)) := by
  classical
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hcr : IsClosed (Set.range (fun u => e u)) :=
    (e.isometry.isClosedEmbedding).isClosed_range
  have hEq :
      (Set.range (fun u => e u)) =
        (LinearMap.range e.toLinearMap : Set (E →₂[(volume : Measure E)] ℝ)) := by
    ext y
    constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
  simpa [hEq] using hcr

theorem isCompactOperator_h1OnToL2_codRestrict_range_extendByZero {K : Set E} (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    IsCompactOperator
      (Set.codRestrict
        (h1OnToL2 (E := E) K hKm)
        (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
        (by
          intro x
          have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
            x.property
          dsimp [h1On] at hxmem
          -- Rewrite the codomain-restricted inclusion as `h1ToL2` on the underlying `H¹` element.
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          -- This is exactly the unfolded membership in
          -- the `comap`.
          exact hxmem)) := by
  -- First, use Euclidean Rellich compactness into `L²(volume)`.
  have hcomp : IsCompactOperator (h1OnToL2 (E := E) K hKm) :=
    isCompactOperator_h1OnToL2 (E := E) (K := K) hK hKm
  -- Now codomain-restrict using the closedness of the range.
  -- `hV` is definitional from the codomain restriction in the statement (unification fills it).
  exact
    IsCompactOperator.codRestrict (f := h1OnToL2 (E := E) K hKm) hcomp
      (V := LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
      (hV := by
        intro x
        have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
          x.property
        dsimp [h1On] at hxmem
        change
            ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                  (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞))
                      (s := K) hKm).toLinearMap)
        exact hxmem)
      (h_closed :=
        isClosed_range_extendByZero (E := E) K hKm)

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

/-! ## AggregatePrimeError -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Green64Analytic.LastPrimeErrors

/-- A uniform bound on the TOTAL actual last-prime PNT2 error.
Here q = product of the ordered natural-prime prefix, not an abstract
prime measure. Neither distinctness nor squarefreeness is assumed.

The q <= P, log(x/q) >= a conditions will come from a fixed
positive gap from the dependent-coordinate simplex boundary. -/
theorem finite_aggregate_PNT_error
    (G : Finset (List ℕ)) (x z a P C : ℝ)
    (hx : 0 ≤ x) (hz : 0 ≤ z + 1) (ha : 0 < a)
    (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hq : ∀ l ∈ G, 0 < (l.prod : ℝ))
    (hcap : ∀ l ∈ G, (l.prod : ℝ) ≤ P)
    (hlog : ∀ l ∈ G, a ≤ Real.log (x / (l.prod : ℝ))) :
    (∑ l ∈ G,
      (C * (x / (l.prod : ℝ)) / (Real.log (x / (l.prod : ℝ))) ^ 2 +
      (z + 1))) ≤
    (C * x / a ^ 2 + (z + 1) * P) *
      ∑ l ∈ G, (l.prod : ℝ)⁻¹ := by
  have _ := hP
  classical
  calc
    _ ≤ ∑ l ∈ G, (C * x / a ^ 2 + (z+1)*P)*(l.prod : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      let q : ℝ := l.prod
      have hqpos : 0 < q := hq l hl
      have hL : 0 < Real.log (x/q) :=
        ha.trans_le (hlog l hl)
      have hsq : a^2 ≤ (Real.log (x/q))^2 := by
        nlinarith [hlog l hl]
      have hinv : ((Real.log (x/q))^2)⁻¹ ≤ (a^2)⁻¹ :=
        inv_anti₀ (pow_pos ha 2) hsq
      have hmain :
          C*(x/q)/(Real.log (x/q))^2 ≤
          (C*x/a^2)*q⁻¹ := by
        calc
          C*(x/q)/(Real.log (x/q))^2 =
            (C*x*q⁻¹)*((Real.log (x/q))^2)⁻¹ := by ring
          _ ≤ (C*x*q⁻¹)*(a^2)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv
              (mul_nonneg (mul_nonneg hC hx)
                (inv_nonneg.mpr hqpos.le))
          _ = (C*x/a^2)*q⁻¹ := by ring
      have hratio : 1 ≤ P/q :=
        (one_le_div hqpos).2 (hcap l hl)
      have hsecond : z+1 ≤ ((z+1)*P)*q⁻¹ := by
        calc
          z+1 = (z+1)*1 := by ring
          _ ≤ (z+1)*(P/q) :=
            mul_le_mul_of_nonneg_left hratio hz
          _ = ((z+1)*P)*q⁻¹ := by ring
      dsimp only [q] at hmain hsecond
      nlinarith [hmain,hsecond]
    _ = (C * x / a ^ 2 + (z + 1) * P) *
      ∑ l ∈ G, (l.prod : ℝ)⁻¹ := by
      rw [Finset.mul_sum]

end Green64Analytic.LastPrimeErrors

end

/-! ## G1Harmonic -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem harmonic_power_majorant :
∀ (Y σ e : ℝ), 1 ≤ Y → 0 ≤ e → 1-e ≤ σ →
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℝ)^(-σ)) ≤
      (1+Real.log Y) * Y^e :=
by
  intro Y σ e hY he hσ
  have hypos : 0 < Y := by linarith
  have hnle (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Y⌋₊) :
      1 ≤ (n:ℝ) ∧ (n:ℝ) ≤ Y := by
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    constructor
    · exact_mod_cast h1
    · exact (Nat.cast_le.mpr h2).trans (Nat.floor_le hypos.le)
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Y⌋₊) :
      (n:ℝ)^(-σ) ≤ (n:ℝ)⁻¹ * Y^e := by
    obtain ⟨hn1,hnY⟩ := hnle n hn
    have hnpos : 0 < (n:ℝ) := by linarith
    have hexp : 1-σ ≤ e := by linarith
    have h1 := Real.rpow_le_rpow_of_exponent_le hn1 hexp
    have h2 := Real.rpow_le_rpow hnpos.le hnY he
    have heq : (n:ℝ)^(-σ) = (n:ℝ)⁻¹ * (n:ℝ)^(1-σ) := by
      rw [← Real.rpow_neg_one (n:ℝ), ← Real.rpow_add hnpos]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.mpr hnpos.le)
  calc
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℝ)^(-σ)) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((n:ℝ)⁻¹ * Y^e) :=
        Finset.sum_le_sum (fun n hn => hp n hn)
    _ = (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n:ℝ)⁻¹) * Y^e := by rw [Finset.sum_mul]
    _ = (harmonic ⌊Y⌋₊ : ℝ) * Y^e := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (1+Real.log Y) * Y^e := by
      exact mul_le_mul_of_nonneg_right (harmonic_floor_le_one_add_log Y hY) (Real.rpow_nonneg hypos.le _)
end Green64Analytic.LongPrime

end

