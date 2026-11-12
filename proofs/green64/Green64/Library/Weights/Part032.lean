module

public import Green64.Library.Analysis.Estimates.Part003
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part020
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Green64.Library.Weights.Part006
public import Green64.Library.Sieve.Foundation.Lemma6.Part003

@[expose] public section

/-!
# Weights / Part032

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceSimplexGeometry -/

section

set_option maxHeartbeats 1500000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.SourceSimplexGeometry

/-- Literal independent-coordinate domain from sourceSimplexTerm,
with d coordinates and one dependent last-prime coordinate. -/
def sourceRegion (d : ℕ) (b w : ℝ) : Set (Fin d → ℝ) :=
  {t | (∀ i, b ≤ t i) ∧ ∑ i, t i ≤ w-b}

/-- Exactly the source last-prime kernel, not a surface-measure density. -/
noncomputable def sourceKernel (d : ℕ) (w : ℝ)
    (t : Fin d → ℝ) : ℝ :=
  (∏ i : Fin d, (t i)⁻¹) * (w-∑ i : Fin d, t i)⁻¹

/-- Globally regularized for compact-integrability arguments. -/
noncomputable def boundedKernel (d : ℕ) (b w : ℝ)
    (t : Fin d → ℝ) : ℝ :=
  (∏ i : Fin d, (max b (t i))⁻¹) *
     (max b (w-∑ i : Fin d, t i))⁻¹

theorem sourceRegion_closed (d : ℕ) (b w : ℝ) :
    IsClosed (sourceRegion d b w) := by
  have hcoords : IsClosed {t : Fin d → ℝ | ∀ i, b ≤ t i} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_iInter (fun i : Fin d =>
        (isClosed_le continuous_const (continuous_apply i))))
  have hsum : IsClosed {t : Fin d → ℝ |
      (∑ i : Fin d, t i) ≤ w-b} :=
    isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i))
      continuous_const
  exact hcoords.inter hsum

theorem sourceRegion_subset_box (d : ℕ) (b w : ℝ) (hb : 0 ≤ b) :
    sourceRegion d b w ⊆
      Set.Icc (fun _ : Fin d => b) (fun _ : Fin d => w) := by
  intro t ht
  have h : (∀ i, b ≤ t i) ∧ (∑ i : Fin d, t i) ≤ w-b := ht
  refine ⟨h.1, ?_⟩
  intro i
  have hi : t i ≤ ∑ j : Fin d, t j :=
    Finset.single_le_sum (fun j _ => hb.trans (h.1 j))
      (Finset.mem_univ i)
  linarith

theorem sourceRegion_compact (d : ℕ) (b w : ℝ) (hb : 0 ≤ b) :
    IsCompact (sourceRegion d b w) :=
  isCompact_Icc.of_isClosed_subset (sourceRegion_closed d b w)
    (sourceRegion_subset_box d b w hb)

theorem boundedKernel_continuous (d : ℕ) (b w : ℝ) (hb : 0 < b) :
    Continuous (boundedKernel d b w) := by
  unfold boundedKernel
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i hi
    apply Continuous.inv₀
    · exact continuous_const.max (continuous_apply i)
    · intro t
      exact ne_of_gt (hb.trans_le (le_max_left _ _))
  · apply Continuous.inv₀
    · apply Continuous.max
      · exact continuous_const
      · exact continuous_const.sub
          (continuous_finsetSum _ (fun i _ => continuous_apply i))
    · intro t
      exact ne_of_gt (hb.trans_le (le_max_left _ _))

theorem boundedKernel_eq_source (d : ℕ) (b w : ℝ)
    (t : Fin d → ℝ) (ht : t ∈ sourceRegion d b w) :
    boundedKernel d b w t = sourceKernel d w t := by
  have hi (i : Fin d) : max b (t i) = t i :=
    max_eq_right (ht.1 i)
  have hw : max b (w-∑ i : Fin d, t i) =
      w-∑ i : Fin d, t i :=
    max_eq_right (by linarith [ht.2])
  simp only [boundedKernel, sourceKernel, hi, hw]

theorem sourceKernel_integrableOn (d : ℕ) (b w : ℝ) (hb : 0 < b) :
    IntegrableOn (sourceKernel d w) (sourceRegion d b w) := by
  have hreg : IntegrableOn (boundedKernel d b w) (sourceRegion d b w) :=
    (boundedKernel_continuous d b w hb).continuousOn.integrableOn_compact
      (sourceRegion_compact d b w hb.le)
  apply IntegrableOn.congr_fun hreg
  · intro t ht
    exact boundedKernel_eq_source d b w t ht
  · exact (sourceRegion_closed d b w).measurableSet

theorem sourceKernel_bound (d : ℕ) (b w : ℝ) (hb : 0 < b)
    (t : Fin d → ℝ) (ht : t ∈ sourceRegion d b w) :
    0 ≤ sourceKernel d w t ∧ sourceKernel d w t ≤ (b⁻¹)^(d+1) := by
  have hcoord (i : Fin d) : 0 < t i := hb.trans_le (ht.1 i)
  have hlast : b ≤ w-∑ i : Fin d, t i := by
    have hh : (∑ i : Fin d, t i) ≤ w-b := ht.2
    linarith
  have hprod0 : 0 ≤ ∏ i : Fin d, (t i)⁻¹ :=
    Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hcoord i).le)
  have hprod : (∏ i : Fin d, (t i)⁻¹) ≤ (b⁻¹)^d := by
    calc
      _ ≤ ∏ _i : Fin d, b⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact inv_nonneg.mpr (hcoord i).le
        · intro i hi
          exact inv_anti₀ hb (ht.1 i)
      _ = (b⁻¹)^d := by simp

  have hlast0 : 0 ≤ (w-∑ i : Fin d, t i)⁻¹ :=
    inv_nonneg.mpr (hb.le.trans hlast)
  have hlastBound : (w-∑ i : Fin d, t i)⁻¹ ≤ b⁻¹ :=
    inv_anti₀ hb hlast
  constructor
  · exact mul_nonneg hprod0 hlast0
  · dsimp [sourceKernel]
    calc
      (∏ i : Fin d, (t i)⁻¹) *
          (w-∑ i : Fin d, t i)⁻¹ ≤
          (b⁻¹)^d * b⁻¹ :=
        mul_le_mul hprod hlastBound hlast0
          (pow_nonneg (inv_nonneg.mpr hb.le) d)
      _ = (b⁻¹)^(d+1) := by ring

/-- Not an abstract model: the integrand and domain are DEFINITIONALLY
the exact ones in the source density J_(d-1). -/
theorem sourceSimplexTerm_eq (n : ℕ) (b w : ℝ) :
    Green64Analytic.SmallB.sourceSimplexTerm n b w =
      (∫ t in sourceRegion (n+1) b w,
        sourceKernel (n+1) w t) / ((n+2).factorial : ℝ) := by
  rfl

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceCellFreeze -/

section

set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Exact frozen-corner approximation for the original dependent-last-prime
denominator over a small inner simplex box. Retains w and dimension d. -/
theorem source_last_prime_cell_freeze_bound
    (d : ℕ) (b w η : ℝ) (u v t : Fin d → ℝ)
    (hb : 0 < b) (hη : 0 ≤ η)
    (huv : ∀ i, u i ≤ t i ∧ t i ≤ v i)
    (hwidth : ∀ i, v i - u i ≤ η)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    0 ≤ (w - ∑ i : Fin d, t i)⁻¹ -
          (w - ∑ i : Fin d, u i)⁻¹ ∧
    (w - ∑ i : Fin d, t i)⁻¹ -
          (w - ∑ i : Fin d, u i)⁻¹ ≤
            (d : ℝ) * η / b ^ 2 := by
  have _ := hη
  have hsumUT : (∑ i : Fin d, u i) ≤ ∑ i : Fin d, t i :=
    Finset.sum_le_sum (fun i _ => (huv i).1)
  have hsumTV : (∑ i : Fin d, t i) ≤ ∑ i : Fin d, v i :=
    Finset.sum_le_sum (fun i _ => (huv i).2)
  have hlastT : b ≤ w - ∑ i : Fin d, t i := by linarith
  have hlastU : b ≤ w - ∑ i : Fin d, u i := by linarith
  have hTpos : 0 < w - ∑ i : Fin d, t i := hb.trans_le hlastT
  have hUpos : 0 < w - ∑ i : Fin d, u i := hb.trans_le hlastU
  have hgap : (∑ i : Fin d, t i) - (∑ i : Fin d, u i) ≤ (d : ℝ) * η := by
    calc
      _ = ∑ i : Fin d, (t i - u i) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ _i : Fin d, η := by
        apply Finset.sum_le_sum
        intro i _
        linarith [(huv i).2, hwidth i]
      _ = (d : ℝ) * η := by simp
  have hnum0 : 0 ≤ (∑ i : Fin d, t i) - (∑ i : Fin d, u i) := by
    linarith
  have hden0 : 0 < (w - ∑ i : Fin d, t i) *
      (w - ∑ i : Fin d, u i) := mul_pos hTpos hUpos
  have hb2 : 0 < b^2 := pow_pos hb 2
  have hdenb : b^2 ≤ (w - ∑ i : Fin d, t i) *
      (w - ∑ i : Fin d, u i) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlastT)
      (sub_nonneg.mpr hlastU)]
  have hidentity :
      (w - ∑ i : Fin d, t i)⁻¹ -
          (w - ∑ i : Fin d, u i)⁻¹ =
      ((∑ i : Fin d, t i) - (∑ i : Fin d, u i)) /
        ((w - ∑ i : Fin d, t i) *
          (w - ∑ i : Fin d, u i)) := by
    field_simp
    ring
  rw [hidentity]
  constructor
  · exact div_nonneg hnum0 hden0.le
  · exact (div_le_div_of_nonneg_left hnum0 hb2 hdenb).trans
      (div_le_div_of_nonneg_right hgap hb2.le)

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceCellReciprocal -/

section

set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Exact reciprocal-density mass of a product of half-open frozen
real prime-exponent cells, without invoking any hypothetical grid limit. -/
theorem reciprocal_rectangle_mass_exact
    (d : ℕ) (u v : Fin d → ℝ)
    (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i) :
    (∫ t : Fin d → ℝ,
        ∏ i : Fin d,
          (Set.Ioc (u i) (v i)).indicator (fun x : ℝ => x⁻¹) (t i)) =
      ∏ i : Fin d, Real.log (v i / u i) := by
  rw [integral_fintype_prod_volume_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (huv i)]
  exact integral_inv_of_pos (hu i) ((hu i).trans_le (huv i))

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceCellIntegral -/

section

set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- The genuine half-open continuum box matching the prime exponent cell convention. -/
def sourceCellSet (d : ℕ) (u v : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {t | ∀ i, t i ∈ Set.Ioc (u i) (v i)}

theorem sourceCellSet_measurable (d : ℕ) (u v : Fin d → ℝ) :
    MeasurableSet (sourceCellSet d u v) := by
  unfold sourceCellSet
  measurability

theorem sourceCellSet_subset_sourceRegion
    (d : ℕ) (b w : ℝ) (u v : Fin d → ℝ)
    (hbu : ∀ i, b ≤ u i)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    sourceCellSet d u v ⊆ sourceRegion d b w := by
  intro t ht
  change (∀ i, b ≤ t i) ∧ (∑ i : Fin d, t i) ≤ w - b
  constructor
  · intro i
    exact (hbu i).trans (le_of_lt (ht i).1)
  · have h : (∑ i : Fin d, t i) ≤ ∑ i : Fin d, v i :=
      Finset.sum_le_sum (fun i _ => (ht i).2)
    linarith

/-- Coordinate indicator product equals the indicator of the full half-open box. -/
theorem sourceCellSet_integrand_indicator
    (d : ℕ) (u v : Fin d → ℝ) (t : Fin d → ℝ) :
    (∏ i : Fin d, (Set.Ioc (u i) (v i)).indicator
      (fun x : ℝ => x⁻¹) (t i)) =
    (sourceCellSet d u v).indicator
      (fun t : Fin d → ℝ => ∏ i : Fin d, (t i)⁻¹) t := by
  by_cases ht : t ∈ sourceCellSet d u v
  · rw [Set.indicator_of_mem ht]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (ht i)]
  · rw [Set.indicator_of_notMem ht]
    have hbad : ∃ i : Fin d, t i ∉ Set.Ioc (u i) (v i) := by
      simpa only [sourceCellSet, Set.mem_ofPred_eq, not_forall] using ht
    obtain ⟨i, hi⟩ := hbad
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (fun x : ℝ => x⁻¹))

/-- Exact product rectangle dt/t volume with the same half-open cells
as the finite prime-grid theorem. -/
theorem sourceCellSet_reciprocal_integral
    (d : ℕ) (u v : Fin d → ℝ)
    (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i) :
    (∫ t in sourceCellSet d u v, ∏ i : Fin d, (t i)⁻¹) =
      ∏ i : Fin d, Real.log (v i / u i) := by
  rw [← integral_indicator (sourceCellSet_measurable d u v)]
  calc
    _ = ∫ t : Fin d → ℝ,
        ∏ i : Fin d, (Set.Ioc (u i) (v i)).indicator
          (fun x : ℝ => x⁻¹) (t i) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (fun t => (sourceCellSet_integrand_indicator d u v t).symm)
    _ = ∏ i : Fin d, Real.log (v i / u i) :=
      reciprocal_rectangle_mass_exact d u v hu huv

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceCellDarboux -/

section

set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

theorem sourceCellSet_reciprocal_integrableOn
    (d : ℕ) (b w : ℝ) (u v : Fin d → ℝ)
    (hb : 0 < b) (hbu : ∀ i, b ≤ u i)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    IntegrableOn (fun t : Fin d → ℝ => ∏ i, (t i)⁻¹)
      (sourceCellSet d u v) := by
  let f : (Fin d → ℝ) → ℝ :=
    fun t => ∏ i, (max b (t i))⁻¹
  have hcont : Continuous f := by
    dsimp [f]
    apply continuous_finsetProd
    intro i _
    apply Continuous.inv₀
    · exact continuous_const.max (continuous_apply i)
    · intro t
      exact ne_of_gt (hb.trans_le (le_max_left _ _))
  have hInt : IntegrableOn f (sourceRegion d b w) :=
    hcont.continuousOn.integrableOn_compact (sourceRegion_compact d b w hb.le)
  have hSubset := sourceCellSet_subset_sourceRegion d b w u v hbu hroom
  have hCell : IntegrableOn f (sourceCellSet d u v) :=
    hInt.mono_set hSubset
  apply IntegrableOn.congr_fun hCell
  · intro t ht
    dsimp [f]
    apply Finset.prod_congr rfl
    intro i _
    rw [max_eq_right ((hbu i).trans (le_of_lt (ht i).1))]
  · exact sourceCellSet_measurable d u v

/-- Exact integral of any frozen last-prime constant times the
product reciprocal density on an admissible continuum box. -/
theorem sourceCellSet_frozen_integral
    (d : ℕ) (u v : Fin d → ℝ) (c : ℝ)
    (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i) :
    (∫ t in sourceCellSet d u v,
      c * ∏ i : Fin d, (t i)⁻¹) =
    c * ∏ i : Fin d, Real.log (v i / u i) := by
  rw [integral_const_mul]
  simpa [smul_eq_mul] using congrArg (fun x : ℝ => c * x)
    (sourceCellSet_reciprocal_integral d u v hu huv)

/-- Two-sided integral error of the *true* last-prime source kernel
on a fixed half-open inner rectangle. This is the local continuum
Darboux bound needed for global rectangle exhaustion. -/
theorem sourceCellSet_true_kernel_darboux_bounds
    (d : ℕ) (b w η : ℝ) (u v : Fin d → ℝ)
    (hb : 0 < b) (hη : 0 ≤ η)
    (hbu : ∀ i, b ≤ u i)
    (huv : ∀ i, u i ≤ v i)
    (hwidth : ∀ i, v i - u i ≤ η)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    ((w - ∑ i : Fin d, u i)⁻¹) *
      (∏ i : Fin d, Real.log (v i / u i)) ≤
        (∫ t in sourceCellSet d u v, sourceKernel d w t) ∧
    (∫ t in sourceCellSet d u v, sourceKernel d w t) ≤
      ((w - ∑ i : Fin d, u i)⁻¹ + (d : ℝ) * η / b^2) *
        (∏ i : Fin d, Real.log (v i / u i)) := by
  let W : ℝ := (w - ∑ i : Fin d, u i)⁻¹
  let E : ℝ := (d : ℝ) * η / b^2
  let P : (Fin d → ℝ) → ℝ := fun t => ∏ i, (t i)⁻¹
  have hMeas := sourceCellSet_measurable d u v
  have hSubset := sourceCellSet_subset_sourceRegion d b w u v hbu hroom
  have hK : IntegrableOn (sourceKernel d w) (sourceCellSet d u v) :=
    (sourceKernel_integrableOn d b w hb).mono_set hSubset
  have hP : IntegrableOn P (sourceCellSet d u v) :=
    sourceCellSet_reciprocal_integrableOn d b w u v hb hbu hroom
  have hL : IntegrableOn (fun t => W * P t) (sourceCellSet d u v) :=
    hP.const_mul W
  have hU : IntegrableOn (fun t => (W + E) * P t) (sourceCellSet d u v) :=
    hP.const_mul (W + E)
  have hP0 (t : Fin d → ℝ) (ht : t ∈ sourceCellSet d u v) :
      0 ≤ P t := by
    dsimp [P]
    apply Finset.prod_nonneg
    intro i _
    apply inv_nonneg.mpr
    exact (hb.trans_le ((hbu i).trans (le_of_lt (ht i).1))).le
  have hpoint (t : Fin d → ℝ) (ht : t ∈ sourceCellSet d u v) :
      W ≤ (w - ∑ i : Fin d, t i)⁻¹ ∧
      (w - ∑ i : Fin d, t i)⁻¹ ≤ W + E := by
    have hf := source_last_prime_cell_freeze_bound d b w η u v t
      hb hη (fun i => ⟨(ht i).1.le, (ht i).2⟩) hwidth hroom
    dsimp only [W, E]
    constructor <;> linarith [hf.1, hf.2]
  have hLower :
      (∫ t in sourceCellSet d u v, W * P t) ≤
        (∫ t in sourceCellSet d u v, sourceKernel d w t) := by
    apply setIntegral_mono_on hL hK hMeas
    intro t ht
    have hp := hP0 t ht
    have h := mul_le_mul_of_nonneg_right (hpoint t ht).1 hp
    simpa only [P, sourceKernel, mul_comm] using h
  have hUpper :
      (∫ t in sourceCellSet d u v, sourceKernel d w t) ≤
        (∫ t in sourceCellSet d u v, (W + E) * P t) := by
    apply setIntegral_mono_on hK hU hMeas
    intro t ht
    have hp := hP0 t ht
    have h := mul_le_mul_of_nonneg_right (hpoint t ht).2 hp
    simpa only [P, sourceKernel, mul_comm] using h
  have hu : ∀ i, 0 < u i := fun i => hb.trans_le (hbu i)
  constructor
  · simpa only [W, P] using
      (le_trans (le_of_eq (sourceCellSet_frozen_integral d u v W hu huv).symm) hLower)
  · simpa only [W, E, P] using
      (le_trans hUpper (le_of_eq (sourceCellSet_frozen_integral d u v (W+E) hu huv)))

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceFiniteGridIntegral -/

section

set_option maxHeartbeats 1800000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Different frozen grid assignments define disjoint continuum boxes. -/
theorem sourceGridCells_disjoint
    (d k : ℕ) (u v : Fin k → ℝ)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (c c' : Fin d → Fin k) (hne : c ≠ c') :
    Disjoint
      (sourceCellSet d (fun i => u (c i)) (fun i => v (c i)))
      (sourceCellSet d (fun i => u (c' i)) (fun i => v (c' i))) := by
  have hcoord : ∃ i : Fin d, c i ≠ c' i := by
    by_contra hnone
    apply hne
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hcoord
  apply Set.disjoint_left.mpr
  intro t ht ht'
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hv := (ht i).2
    have hu := (ht' i).1
    linarith [hsep (c i) (c' i) hlt]
  · have hv := (ht' i).2
    have hu := (ht i).1
    linarith [hsep (c' i) (c i) hgt]

/-- The finite disjoint union of source grid cells. -/
def sourceGridUnion (d k : ℕ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) : Set (Fin d → ℝ) :=
  ⋃ c ∈ S, sourceCellSet d (fun i => u (c i)) (fun i => v (c i))

/-- A finite grid's exact frozen-corner Darboux sum is no greater
than the complete source integral, preserving the dependent-last-prime
kernel and half-open cell convention. -/
theorem finite_source_grid_integral_lower
    (d k : ℕ) (b w η : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hη : 0 ≤ η)
    (hbu : ∀ j, b ≤ u j)
    (huv : ∀ j, u j ≤ v j)
    (hwidth : ∀ j, v j - u j ≤ η)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    (∑ c ∈ S,
      (w - ∑ i : Fin d, u (c i))⁻¹ *
        (∏ i : Fin d, Real.log (v (c i) / u (c i)))) ≤
    (∫ t in sourceRegion d b w, sourceKernel d w t) := by
  let cell : (Fin d → Fin k) → Set (Fin d → ℝ) :=
    fun c => sourceCellSet d (fun i => u (c i)) (fun i => v (c i))
  have hSub (c : Fin d → Fin k) (hc : c ∈ S) :
      cell c ⊆ sourceRegion d b w :=
    sourceCellSet_subset_sourceRegion d b w
      (fun i => u (c i)) (fun i => v (c i))
      (fun i => hbu (c i)) (hroom c hc)
  have hMeas (c : Fin d → Fin k) (hc : c ∈ S) :
      MeasurableSet (cell c) :=
    sourceCellSet_measurable d (fun i => u (c i)) (fun i => v (c i))
  have hInt (c : Fin d → Fin k) (hc : c ∈ S) :
      IntegrableOn (sourceKernel d w) (cell c) :=
    (sourceKernel_integrableOn d b w hb).mono_set (hSub c hc)
  have hDisj : Set.Pairwise (↑S) (Disjoint on cell) := by
    intro c hc c' hc' hne
    exact sourceGridCells_disjoint d k u v hsep c c' hne
  have hSplit :
      (∫ t in sourceGridUnion d k u v S, sourceKernel d w t) =
      ∑ c ∈ S, ∫ t in cell c, sourceKernel d w t := by
    change (∫ t in ⋃ c ∈ S, cell c, sourceKernel d w t) = _
    exact integral_biUnion_finset S hMeas hDisj hInt
  have hGridSubset :
      sourceGridUnion d k u v S ⊆ sourceRegion d b w := by
    intro t ht
    change t ∈ ⋃ c ∈ S, cell c at ht
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hcin, htcell⟩ := Set.mem_iUnion.mp hc
    exact hSub c hcin htcell
  have hNonneg :
      0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict (sourceRegion d b w)]
        sourceKernel d w := by
    filter_upwards [ae_restrict_mem (sourceRegion_closed d b w).measurableSet] with t ht
    exact (sourceKernel_bound d b w hb t ht).1
  have hFullBound :
      (∫ t in sourceGridUnion d k u v S, sourceKernel d w t) ≤
      (∫ t in sourceRegion d b w, sourceKernel d w t) :=
    setIntegral_mono_set (sourceKernel_integrableOn d b w hb)
      hNonneg (Filter.Eventually.of_forall hGridSubset)
  calc
    _ ≤ ∑ c ∈ S, ∫ t in cell c, sourceKernel d w t := by
      apply Finset.sum_le_sum
      intro c hc
      exact (sourceCellSet_true_kernel_darboux_bounds d b w η
        (fun i => u (c i)) (fun i => v (c i))
        hb hη (fun i => hbu (c i))
        (fun i => huv (c i))
        (fun i => hwidth (c i)) (hroom c hc)).1
    _ = ∫ t in sourceGridUnion d k u v S, sourceKernel d w t := hSplit.symm
    _ ≤ _ := hFullBound

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceSimplexIntegralBound -/

section

set_option maxHeartbeats 900000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.SourceSimplexGeometry

/-- Uniform L¹ bound for the ACTUAL source d+1-prime simplex integral.
It makes boundary-collar estimates depend only on geometric volume. -/
theorem sourceKernel_integral_bounds (d : ℕ) (b w : ℝ) (hb : 0 < b) :
    0 ≤ ∫ t in sourceRegion d b w, sourceKernel d w t ∧
    (∫ t in sourceRegion d b w, sourceKernel d w t) ≤
      (volume (sourceRegion d b w)).toReal * (b⁻¹)^(d+1) := by
  let K := sourceRegion d b w
  have hclosed := sourceRegion_closed d b w
  have hmeas : MeasurableSet K := hclosed.measurableSet
  have hfin : volume K ≠ (⊤ : ENNReal) :=
    (sourceRegion_compact d b w hb.le).measure_lt_top.ne
  have hInt : IntegrableOn (sourceKernel d w) K :=
    sourceKernel_integrableOn d b w hb
  have hConst : IntegrableOn
      (fun _ : Fin d → ℝ => (b⁻¹)^(d+1)) K :=
    integrableOn_const hfin
  have hLo : 0 ≤ ∫ t in K, sourceKernel d w t :=
    setIntegral_nonneg hmeas (fun t ht => (sourceKernel_bound d b w hb t ht).1)
  have hUp := setIntegral_mono_on hInt hConst hmeas
    (fun t ht => (sourceKernel_bound d b w hb t ht).2)
  constructor
  · exact hLo
  · simpa [K, Measure.real_def, smul_eq_mul] using hUp

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceSimplexCollar -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.SourceSimplexGeometry

/-- Transfer the exact source integrand to any measurable piece of the
compact simplex. The error is bounded by its true Lebesgue volume. -/
theorem sourceKernel_integral_subset_bound (d : ℕ) (b w : ℝ)
    (hb : 0 < b) (A : Set (Fin d → ℝ))
    (hA : A ⊆ sourceRegion d b w) (hMeas : MeasurableSet A) :
    0 ≤ ∫ t in A, sourceKernel d w t ∧
    (∫ t in A, sourceKernel d w t) ≤
       (volume A).toReal * (b⁻¹)^(d+1) := by
  have hfin : volume A ≠ (⊤ : ENNReal) :=
    ((measure_mono hA).trans_lt
       (sourceRegion_compact d b w hb.le).measure_lt_top).ne
  have hInt : IntegrableOn (sourceKernel d w) A :=
    (sourceKernel_integrableOn d b w hb).mono_set hA
  have hConst : IntegrableOn
      (fun _ : Fin d → ℝ => (b⁻¹)^(d+1)) A :=
    integrableOn_const hfin
  have hLo : 0 ≤ ∫ t in A, sourceKernel d w t :=
    setIntegral_nonneg hMeas (fun t ht =>
      (sourceKernel_bound d b w hb t (hA ht)).1)
  have hUp := setIntegral_mono_on hInt hConst hMeas
    (fun t ht => (sourceKernel_bound d b w hb t (hA ht)).2)
  constructor
  · exact hLo
  · simpa [Measure.real_def, smul_eq_mul] using hUp

/-- Removing a fixed δ collar is a genuine SET DIFFERENCE, with
unchanged last-prime denominator at w=1 throughout. -/
def sourceCollar (d : ℕ) (b δ : ℝ) : Set (Fin d → ℝ) :=
  sourceRegion d b 1 \ sourceRegion d b (1-δ)

theorem truncated_source_subset (d : ℕ) (b δ : ℝ) (hδ : 0 ≤ δ) :
    sourceRegion d b (1-δ) ⊆ sourceRegion d b 1 := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  have hsum := ht.2
  dsimp only [sourceRegion, Set.mem_ofPred_eq] at ht
  linarith

theorem sourceCollar_measurable (d : ℕ) (b δ : ℝ) :
    MeasurableSet (sourceCollar d b δ) :=
  (sourceRegion_closed d b 1).measurableSet.diff
    (sourceRegion_closed d b (1-δ)).measurableSet

/-- Exact δ-truncation identity; no illicit replacement of
1/(1-Σt) by the kernel with w=1-δ. -/
theorem source_integral_collar_identity (d : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) :
    (∫ t in sourceRegion d b 1, sourceKernel d 1 t) =
      (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) +
      (∫ t in sourceCollar d b δ, sourceKernel d 1 t) := by
  have h := setIntegral_sdiff
    (sourceRegion_closed d b (1-δ)).measurableSet
    (sourceKernel_integrableOn d b 1 hb)
    (truncated_source_subset d b δ hδ)
  dsimp only [sourceCollar] at *
  linarith

theorem sourceCollar_mem_iff (d : ℕ) (b δ : ℝ)
    (t : Fin d → ℝ) :
    t ∈ sourceCollar d b δ ↔
      (∀ i, b ≤ t i) ∧
      1-b-δ < (∑ i : Fin d, t i) ∧
      (∑ i : Fin d, t i) ≤ 1-b := by
  constructor
  · intro ht
    change t ∈ sourceRegion d b 1 ∧ t ∉ sourceRegion d b (1-δ) at ht
    have h := ht
    have hhi := h.1.2
    have hlo : 1-b-δ < (∑ i : Fin d, t i) := by
      by_contra hn
      have hbnd : (∑ i : Fin d, t i) ≤ (1-δ)-b := by
        push Not at hn
        linarith
      exact h.2 ⟨h.1.1,hbnd⟩
    exact ⟨h.1.1,hlo,hhi⟩
  · rintro ⟨hcoord,hlo,hhi⟩
    change t ∈ sourceRegion d b 1 ∧ t ∉ sourceRegion d b (1-δ)
    refine ⟨⟨hcoord,hhi⟩,?_⟩
    intro ht
    have hh := ht.2
    linarith

/-- Explicit norm budget: the unproved part of δ removal is now
solely the GEOMETRIC volume of the true thin sum-coordinate slab. -/
theorem source_integral_collar_bound (d : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) :
    0 ≤ (∫ t in sourceRegion d b 1, sourceKernel d 1 t) -
        (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ∧
    (∫ t in sourceRegion d b 1, sourceKernel d 1 t) -
        (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
       (volume (sourceCollar d b δ)).toReal * (b⁻¹)^(d+1) := by
  have h := source_integral_collar_identity d b δ hb hδ
  have hbnd := sourceKernel_integral_subset_bound d b 1 hb
    (sourceCollar d b δ) Set.sdiff_subset
    (sourceCollar_measurable d b δ)
  constructor <;> linarith

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceSimplexDensityBudget -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.SourceSimplexGeometry

/-- Every source simplex at w≤1 lies in the unit coordinate cube,
irrespective of the number of prime factors. -/
theorem sourceRegion_volume_le_one (d : ℕ) (b w : ℝ)
    (hb : 0 ≤ b) (hw : w ≤ 1) :
    volume (sourceRegion d b w) ≤ 1 := by
  have hs : sourceRegion d b w ⊆
      Set.Icc (fun _ : Fin d => (0:ℝ)) (fun _ => (1:ℝ)) := by
    intro t ht
    have hBox := sourceRegion_subset_box d b w hb ht
    exact ⟨(fun i => hb.trans (hBox.1 i)),
      (fun i => (hBox.2 i).trans hw)⟩
  calc
    volume (sourceRegion d b w) ≤
      volume (Set.Icc (fun _ : Fin d => (0:ℝ))
        (fun _ => (1:ℝ))) := measure_mono hs
    _ = 1 := by simp [Real.volume_Icc_pi]

/-- Uniform quantitative bound for the LITERAL nth source summand:
no new density or prime limit is assumed. -/
theorem sourceSimplexTerm_uniform_bound (n : ℕ) (b w : ℝ)
    (hb : 0 < b) (hw : w ≤ 1) :
    0 ≤ Green64Analytic.SmallB.sourceSimplexTerm n b w ∧
    Green64Analytic.SmallB.sourceSimplexTerm n b w ≤
      (b⁻¹)^(n+2) / ((n+2).factorial : ℝ) := by
  have hintegral := sourceKernel_integral_bounds (n+1) b w hb
  have hVol := sourceRegion_volume_le_one (n+1) b w hb.le hw
  have hVolReal : (volume (sourceRegion (n+1) b w)).toReal ≤ 1 := by
    have hh := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤) hVol
    simpa using hh

  have hp : 0 ≤ (b⁻¹)^(n+2) := by positivity
  have hUpper :
      (∫ t in sourceRegion (n+1) b w,
         sourceKernel (n+1) w t) ≤ (b⁻¹)^(n+2) := by
    calc
      _ ≤ (volume (sourceRegion (n+1) b w)).toReal *
          (b⁻¹)^((n+1)+1) := hintegral.2
      _ ≤ 1 * (b⁻¹)^(n+2) := by
        have := mul_le_mul_of_nonneg_right hVolReal hp
        simpa [Nat.add_assoc] using this
      _ = _ := by ring
  rw [sourceSimplexTerm_eq]
  have hf : (0:ℝ) < ((n+2).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos (n+2)
  exact ⟨div_nonneg hintegral.1 hf.le,
    (div_le_div_of_nonneg_right hUpper hf.le)⟩

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceKernelShift -/

section

set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Same frozen δ-truncated domain, comparing the genuinely different
dependent-prime kernels at w=1-δ and w=1. -/
theorem sourceKernel_shift_bound (d : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) (t : Fin d → ℝ)
    (ht : t ∈ sourceRegion d b (1-δ)) :
    0 ≤ sourceKernel d (1-δ) t - sourceKernel d 1 t ∧
    sourceKernel d (1-δ) t - sourceKernel d 1 t ≤
      δ * (b⁻¹)^(d+2) := by
  let g : ℝ := ∏ i : Fin d, (t i)⁻¹
  let a : ℝ := 1-δ-∑ i : Fin d, t i
  let c : ℝ := 1-∑ i : Fin d, t i
  have ha : b ≤ a := by
    dsimp [a]
    have hh := ht.2
    linarith
  have hc : b ≤ c := by
    dsimp [c]
    linarith
  have hap : 0 < a := hb.trans_le ha
  have hcp : 0 < c := hb.trans_le hc
  have hainv : a⁻¹ ≤ b⁻¹ := inv_anti₀ hb ha
  have hcinv : c⁻¹ ≤ b⁻¹ := inv_anti₀ hb hc
  have hg0 : 0 ≤ g := by
    dsimp [g]
    exact Finset.prod_nonneg (fun i _ =>
      inv_nonneg.mpr (hb.le.trans (ht.1 i)))

  have hg : g ≤ (b⁻¹)^d := by
    dsimp [g]
    calc
      (∏ i : Fin d, (t i)⁻¹) ≤ ∏ _i : Fin d, b⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact inv_nonneg.mpr (hb.le.trans (ht.1 i))
        · intro i hi
          exact inv_anti₀ hb (ht.1 i)
      _ = (b⁻¹)^d := by simp
  have hden : 0 ≤ a⁻¹ * c⁻¹ ∧ a⁻¹ * c⁻¹ ≤ (b⁻¹)^2 := by
    constructor
    · positivity
    · calc
        a⁻¹ * c⁻¹ ≤ b⁻¹ * b⁻¹ :=
          mul_le_mul hainv hcinv (inv_nonneg.mpr hcp.le)
            (inv_nonneg.mpr hb.le)
        _ = (b⁻¹)^2 := by ring
  have hid : a⁻¹ - c⁻¹ = δ * (a⁻¹*c⁻¹) := by
    have hd : c-a=δ := by dsimp [a,c]; ring
    field_simp [ne_of_gt hap, ne_of_gt hcp]
    nlinarith
  have hfact : sourceKernel d (1-δ) t - sourceKernel d 1 t =
      g * (δ * (a⁻¹*c⁻¹)) := by
    dsimp [sourceKernel, g, a, c] at hid ⊢
    rw [← mul_sub]
    exact congrArg _ hid
  rw [hfact]
  constructor
  · exact mul_nonneg hg0 (mul_nonneg hδ hden.1)

  · calc
      g * (δ * (a⁻¹*c⁻¹)) ≤
          (b⁻¹)^d * (δ * (b⁻¹)^2) := by
        apply mul_le_mul hg
          (mul_le_mul_of_nonneg_left hden.2 hδ)
          (mul_nonneg hδ hden.1)
          (pow_nonneg (inv_nonneg.mpr hb.le) d)
      _ = δ * (b⁻¹)^(d+2) := by
        rw [pow_add]
        ring

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceIntegralShift -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.SourceSimplexGeometry

/-- At fixed δ, replacing the shortened dependent-prime denominator
by the genuine source denominator costs at most δ*b^(-d-2).
This uses Lebesgue integrals over the SAME exact truncated simplex. -/
theorem source_integral_shift_bound (d : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) :
    0 ≤ (∫ t in sourceRegion d b (1-δ), sourceKernel d (1-δ) t) -
        (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ∧
    (∫ t in sourceRegion d b (1-δ), sourceKernel d (1-δ) t) -
        (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
        δ * (b⁻¹)^(d+2) := by
  let K := sourceRegion d b (1-δ)
  have hMeas : MeasurableSet K :=
    (sourceRegion_closed d b (1-δ)).measurableSet
  have hIntδ : IntegrableOn (sourceKernel d (1-δ)) K :=
    sourceKernel_integrableOn d b (1-δ) hb
  have hInt1 : IntegrableOn (sourceKernel d 1) K :=
    (sourceKernel_integrableOn d b 1 hb).mono_set
      (truncated_source_subset d b δ hδ)
  have hIntDiff : IntegrableOn
      (fun t => sourceKernel d (1-δ) t - sourceKernel d 1 t) K :=
    hIntδ.sub hInt1

  have hfin : volume K ≠ (⊤ : ENNReal) :=
    (sourceRegion_compact d b (1-δ) hb.le).measure_lt_top.ne
  have hConst : IntegrableOn
      (fun _ : Fin d → ℝ => δ*(b⁻¹)^(d+2)) K :=
    integrableOn_const hfin
  have hLo : 0 ≤
      ∫ t in K, (sourceKernel d (1-δ) t - sourceKernel d 1 t) :=
    setIntegral_nonneg hMeas (fun t ht =>
      (sourceKernel_shift_bound d b δ hb hδ t ht).1)
  have hUp := setIntegral_mono_on hIntDiff hConst hMeas
    (fun t ht => (sourceKernel_shift_bound d b δ hb hδ t ht).2)
  have hVol := sourceRegion_volume_le_one d b (1-δ) hb.le (by linarith)
  have hVolReal : (volume K).toReal ≤ 1 := by
    have hh := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤) hVol
    simpa [K] using hh
  have hBound : 0 ≤ δ * (b⁻¹)^(d+2) := by positivity
  have hUp' : (∫ t in K,
      (sourceKernel d (1-δ) t - sourceKernel d 1 t)) ≤
      δ * (b⁻¹)^(d+2) := by
    calc
      _ ≤ (volume K).toReal * (δ * (b⁻¹)^(d+2)) := by
        simpa [Measure.real_def, smul_eq_mul] using hUp
      _ ≤ 1 * (δ * (b⁻¹)^(d+2)) :=
        mul_le_mul_of_nonneg_right hVolReal hBound
      _ = _ := by ring

  have hDiff :
      (∫ t in K, (sourceKernel d (1-δ) t - sourceKernel d 1 t)) =
        (∫ t in K, sourceKernel d (1-δ) t) -
        (∫ t in K, sourceKernel d 1 t) := by
    exact integral_sub hIntδ hInt1
  rw [hDiff] at hLo hUp'
  exact ⟨hLo,hUp'⟩

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceSourceArcPartition -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- Final exact source major/minor *pointwise partition* of every
frequency theta. No unproved Dirichlet approximation or source scale
hypothesis remains. Large-r gives 4/L^B four-term C6 bracket;
small-r lies within the original width L^Cprime/H' of one rational
circle center with positive denominator q <= |k| ceil(L^B).
The local major-arc Fourier energy is a separate obligation. -/
theorem eventually_source_original_major_minor_arcs
    (c d A B Cprime C₁ C₂ Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A)
    (hB : 0 ≤ B) (hCprime : A+B ≤ Cprime)
    (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (U₁ U₂ Hprime : ℝ),
        Real.exp (L^c-C₁) ≤ U₁ →
        Real.exp (L^c-C₂) ≤ U₂ →
        Hprime = U₁*U₂ →
        0 < Hprime →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        ∀ (theta : ℝ) (k : ℤ), k ≠ 0 →
          (∃ (a : ℤ) (r : ℕ), 0 < r ∧
          Int.gcd a (r:ℤ) = 1 ∧
          |(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
          ((L^B ≤ (r:ℝ) ∧
            1/U₂+1/(r:ℝ)+Real.log (2*(r:ℝ))/U₁+
              (r:ℝ)*Real.log (2*(r:ℝ))/(U₁*U₂) ≤ 4/L^B)
            ∨ ∃ (h : ℤ) (q : ℕ) (shift : ℤ),
              0 < q ∧ q ≤ k.natAbs * Nat.ceil (L^B) ∧
              0 ≤ h ∧ h < (q:ℤ) ∧
              |theta-(shift:ℝ)-(h:ℝ)/(q:ℝ)| ≤
                L^Cprime/Hprime)) := by
  have hsplit :=
    eventually_source_major_minor_split c d A B Cprime C₁ C₂ Chigh
      hc hd hdA hB hCprime hChigh
  filter_upwards [hsplit] with L hsource
  rcases hsource with ⟨hL,hSplit⟩
  refine ⟨hL,?_⟩
  intro U₁ U₂ Hprime hU₁ hU₂ hH hHp hHhi theta k hk
  have hLp : 0 < L := by linarith
  let Q : ℕ := Nat.floor (Hprime/L^Cprime)
  let R : ℕ := Nat.ceil (L^B)
  obtain ⟨a,r,hr,hrQ,hcop,hnear,hbeta,hCases⟩ :=
    hSplit U₁ U₂ Hprime hU₁ hU₂ hH hHp hHhi theta k hk
  refine ⟨a,r,hr,hcop,hbeta,?_⟩
  rcases hCases with hminor | hmajor
  · exact Or.inl hminor
  · right
    obtain ⟨h,q,shift,hrR,hq,hqpos,hqQ,h0,h0lt,hArc⟩ := hmajor
    have hqR : q ≤ k.natAbs*R := by
      rw [hq]
      exact Nat.mul_le_mul_left _ (Nat.le_of_lt hrR)
    have hmax :=
      source_floor_dirichlet_arc_radius Hprime L Cprime Q r k
        hHp hLp rfl hr hk
    exact ⟨h,q,shift,hqpos,hqR,h0,h0lt,hArc.trans hmax⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceOriginalMinorCircle -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 3000000

/-- The original Dirichlet dichotomy on the COMPLEMENT of the actual
circle major arcs. It is applied to -k, matching star(Uhat)*Vhat.
All four minor-arc terms and the signed rational approximation are retained. -/
theorem eventually_source_circle_minor_rational434
    (c d A B Carc C1 C2 Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A) (hB : 0 ≤ B)
    (hCarc : A+B ≤ Carc) (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ ∀ U1 U2 Hprime : ℝ,
        Real.exp (L^c-C1) ≤ U1 → Real.exp (L^c-C2) ≤ U2 →
        Hprime = U1*U2 → 0 < Hprime →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        ∀ (theta : ℝ) (k : ℤ), k ≠ 0 →
          (theta:AddCircle (1:ℝ)) ∉ sourceCircleRationalArcs434
            (k.natAbs*Nat.ceil (L^B)) (L^Carc/Hprime) →
          ∃ (a : ℤ) (r : ℕ), 0 < r ∧ Int.gcd a (r:ℤ) = 1 ∧
            |-(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
            L^B ≤ (r:ℝ) ∧
            1/U2+1/(r:ℝ)+Real.log (2*(r:ℝ))/U1+
              (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) ≤ 4/L^B := by
  have hPartition := Green64Analytic.CorrelationD.eventually_source_original_major_minor_arcs
    c d A B Carc C1 C2 Chigh hc hd hdA hB hCarc hChigh
  filter_upwards [hPartition] with L hL
  refine ⟨hL.1,?_⟩
  intro U1 U2 Hprime hU1 hU2 hH hHp hHhi theta k hk hOutside
  obtain ⟨a,r,hr,hcop,hNear,hCases⟩ := hL.2 U1 U2 Hprime hU1 hU2 hH hHp hHhi
    theta (-k) (neg_ne_zero.mpr hk)
  rcases hCases with hMinor | hMajor
  · exact ⟨a,r,hr,hcop,by simpa only [Int.cast_neg] using hNear,hMinor.1,hMinor.2⟩
  · obtain ⟨h,q,z,hq,hqCap,hh0,hhq,hLift⟩ := hMajor
    have hqCap' : q ≤ k.natAbs*Nat.ceil (L^B) := by
      simpa only [Int.natAbs_neg] using hqCap
    exact False.elim (hOutside (source_circle_rational_mem_of_lift434 _ q h z theta _
      hq hqCap' hh0 hhq hLift))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductAtomMinorScale -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- Containing dyadic blocks may start to the right of the original real
cell endpoints. The C6 bracket only decreases; H' remains U1*U2. -/
theorem source_c6_four_term_mono434 (U1 U2 M N : ℝ) (r : ℕ)
    (hU1 : 0 < U1) (hU2 : 0 < U2) (hM : U1 ≤ M) (hN : U2 ≤ N)
    (hr : 0 < r) :
    1/N+1/(r:ℝ)+Real.log (2*(r:ℝ))/M+
      (r:ℝ)*Real.log (2*(r:ℝ))/(M*N) ≤
    1/U2+1/(r:ℝ)+Real.log (2*(r:ℝ))/U1+
      (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) := by
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hLog : 0 ≤ Real.log (2*(r:ℝ)) := Real.log_nonneg (by linarith)
  have hFirst := one_div_le_one_div_of_le hU2 hN
  have hThird := div_le_div_of_nonneg_left hLog hU1 hM
  have hMN : U1*U2 ≤ M*N := mul_le_mul hM hN hU2.le (hU1.trans_le hM).le
  have hFourth := div_le_div_of_nonneg_left
    (mul_nonneg (by linarith : (0:ℝ) ≤ (r:ℝ)) hLog) (mul_pos hU1 hU2) hMN
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductArcGeometry -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 2500000

/-- The true |k|*ceil(L^B) denominator budget, including rounding. -/
theorem source_product_rational_denominator_cap434 (L Ck B : ℝ) (k : ℤ)
    (hL : 2 ≤ L) (hB : 0 ≤ B) (hk : (k.natAbs:ℝ) ≤ L^Ck) :
    ((k.natAbs*Nat.ceil (L^B):ℕ):ℝ) ≤ L^(Ck+B+1) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hPow : 1 ≤ L^B := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hLone hB
  have hCeil : (Nat.ceil (L^B):ℝ) ≤ L^(B+1) := by
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ L^B)
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith
  rw [Nat.cast_mul]
  calc
    _ ≤ L^Ck*L^(B+1) := mul_le_mul hk hCeil (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring

/-- Original stretched-exponential cell bounds supply the circle injectivity
radius. No dyadic integer endpoint is substituted for U1 or U2. -/
theorem eventually_source_product_arc_radius434 (c Carc C1 C2 : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ ∀ U1 U2 : ℝ,
      Real.exp (L^c-C1) ≤ U1 → Real.exp (L^c-C2) ≤ U2 →
      0 ≤ L^Carc/(U1*U2) ∧ L^Carc/(U1*U2) < 1/2 := by
  have h1 := eventually_source_comparison_lower c (Carc+1) C1 hc
  have h2 := eventually_source_comparison_lower c 0 C2 hc
  filter_upwards [h1,h2,eventually_ge_atTop (2:ℝ)] with L h1 h2 hL
  refine ⟨hL,?_⟩
  intro U1 U2 hU1 hU2
  have hLp : 0 < L := by linarith
  have hU1p : 0 < U1 := (Real.exp_pos _).trans_le hU1
  have hU2p : 0 < U2 := (Real.exp_pos _).trans_le hU2
  have hP : 0 < L^Carc := Real.rpow_pos_of_pos hLp _
  have hLo1 : L^Carc*L < U1 := by
    simpa only [Real.rpow_add hLp,Real.rpow_one] using h1.trans_le hU1
  have hLo2 : 1 < U2 := by simpa only [Real.rpow_zero] using h2.trans_le hU2
  refine ⟨by positivity,?_⟩
  rw [div_lt_iff₀ (mul_pos hU1p hU2p)]
  have hProd := mul_lt_mul_of_pos_left hLo2 hU1p
  nlinarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMovingQcharChoice -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Compatibility of the ACTUAL SOURCE03 Fourier theta-arc
denominator budget Qtheta=|k|*ceil(L^(D+1)) with the
primitive-character cutoff Qchar. Choose Qchar at an
explicitly larger logarithmic power. It both COVERS the
true rational denominators and remains polynomial in L.
The choice is made BEFORE the true five-index mode family
is formed; no arbitrary post hoc adjustment of its
character cutoff is assumed. -/
theorem source_original_true_moving_Qchar_choice434
    (L Ck D Cchar : ℝ) (k : ℤ)
    (hL : 2 ≤ L) (hD : 0 ≤ D+1) (hCchar : 0 ≤ Cchar)
    (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (hExponent : Ck+(D+1)+1 ≤ Cchar) :
    let Qchar := Nat.ceil (L^Cchar)
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar ∧
      (Qchar:ℝ) ≤ L^(Cchar+1) := by
  dsimp only
  have hLone : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hCap :=
    source_product_rational_denominator_cap434
      L Ck (D+1) k hL hD hk
  have hPower : L^(Ck+(D+1)+1) ≤ L^Cchar :=
    Real.rpow_le_rpow_of_exponent_le hLone hExponent
  have hQtheta :
      ((k.natAbs*Nat.ceil (L^(D+1)) : ℕ):ℝ) ≤
        (Nat.ceil (L^Cchar):ℝ) :=
    (hCap.trans hPower).trans (Nat.le_ceil _)
  have hNat :
      k.natAbs*Nat.ceil (L^(D+1)) ≤ Nat.ceil (L^Cchar) := by
    exact_mod_cast hQtheta
  have hPowOne : 1 ≤ L^Cchar := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hLone hCchar)
  have hPowNN : 0 ≤ L^Cchar := by linarith
  have hCeil :
      ((Nat.ceil (L^Cchar)):ℝ) ≤ L^(Cchar+1) := by
    calc
      _ ≤ L^Cchar+1 :=
        le_of_lt (Nat.ceil_lt_add_one hPowNN)
      _ ≤ 2*L^Cchar := by linarith
      _ ≤ L*L^Cchar :=
        mul_le_mul_of_nonneg_right hL hPowNN
      _ = L^(Cchar+1) := by
        rw [Real.rpow_add hLpos,Real.rpow_one]
        ring
  exact ⟨hNat,hCeil⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMinorPolynomialLossAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The precise eighth-power arithmetic loss in the ORIGINAL
source03 TWO-independent-character, TWO-independent-global-cell
physical minor norm-square is absorbable by selecting the
Dirichlet saving exponent Bsave once, BEFORE all ν patterns.
This handles ((Qchar^4)*(xi^-4))² rather than falsely treating
the primitive character/cell family cardinality as constant.
All polynomial estimates on Qchar and xi⁻¹ are explicit. -/
theorem source_original_true_minor_polynomial_loss_absorb434
    (L : ℝ) (hL : 1 ≤ L)
    (Qchar : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (Cchar Cxi Bsave Bgoal : ℝ)
    (hQchar : (Qchar:ℝ) ≤ L^Cchar)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (hBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave) :
    (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * L^(-Bsave) ≤
      L^(-Bgoal) := by
  have hLnn : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hQnn : (0:ℝ) ≤ (Qchar:ℝ) := Nat.cast_nonneg _
  have hXinn : 0 ≤ xi⁻¹ := (inv_nonneg.mpr hxi.le)
  have hQ4 : ((Qchar:ℝ)^4) ≤ (L^Cchar)^4 :=
    pow_le_pow_left₀ hQnn hQchar 4
  have hXi4 : (xi⁻¹)^4 ≤ (L^Cxi)^4 :=
    pow_le_pow_left₀ hXinn hXi 4
  have hProd4 :
      ((Qchar:ℝ)^4)*(xi⁻¹)^4 ≤
        (L^Cchar)^4*(L^Cxi)^4 := by
    calc
      _ ≤ (L^Cchar)^4*(xi⁻¹)^4 :=
        mul_le_mul_of_nonneg_right hQ4 (pow_nonneg hXinn 4)
      _ ≤ (L^Cchar)^4*(L^Cxi)^4 :=
        mul_le_mul_of_nonneg_left hXi4
          (pow_nonneg (Real.rpow_nonneg hLnn _) 4)
  have hProd4nn :
      0 ≤ ((Qchar:ℝ)^4)*(xi⁻¹)^4 :=
    mul_nonneg (pow_nonneg hQnn _) (pow_nonneg hXinn _)
  have hSquare :
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 ≤
        ((L^Cchar)^4*(L^Cxi)^4)^2 :=
    pow_le_pow_left₀ hProd4nn hProd4 2
  have hQPower : (L^Cchar)^4 = L^(4*Cchar) := by
    calc
      _ = (L^Cchar)^(4:ℝ) :=
        (Real.rpow_natCast (L^Cchar) 4).symm
      _ = L^(Cchar*4) := (Real.rpow_mul hLnn Cchar 4).symm
      _ = L^(4*Cchar) := by ring
  have hXiPower : (L^Cxi)^4 = L^(4*Cxi) := by
    calc
      _ = (L^Cxi)^(4:ℝ) :=
        (Real.rpow_natCast (L^Cxi) 4).symm
      _ = L^(Cxi*4) := (Real.rpow_mul hLnn Cxi 4).symm
      _ = L^(4*Cxi) := by ring
  have hProdPower :
      ((L^Cchar)^4*(L^Cxi)^4)^2 =
        L^(8*(Cchar+Cxi)) := by
    rw [hQPower, hXiPower]
    calc
      (L^(4*Cchar)*L^(4*Cxi))^2 =
        (L^(4*Cchar+4*Cxi))^2 := by
          rw [Real.rpow_add hLpos]
      _ = (L^(4*Cchar+4*Cxi))^(2:ℝ) :=
        (Real.rpow_natCast (L^(4*Cchar+4*Cxi)) 2).symm
      _ = L^((4*Cchar+4*Cxi)*2) :=
        (Real.rpow_mul hLnn (4*Cchar+4*Cxi) 2).symm
      _ = L^(8*(Cchar+Cxi)) := by ring
  have hSaving :
      8*(Cchar+Cxi)-Bsave ≤ -Bgoal := by linarith [hBudget]
  calc
    (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*L^(-Bsave) ≤
        ((L^Cchar)^4*(L^Cxi)^4)^2*L^(-Bsave) :=
      mul_le_mul_of_nonneg_right hSquare (Real.rpow_nonneg hLnn _)
    _ = L^(8*(Cchar+Cxi))*L^(-Bsave) := by rw [hProdPower]
    _ = L^(8*(Cchar+Cxi)-Bsave) := by
      rw [sub_eq_add_neg, Real.rpow_add hLpos]
    _ ≤ L^(-Bgoal) :=
      Real.rpow_le_rpow_of_exponent_le hL hSaving

/-- The EXACT squared signed physical RAW-minus-Knu minor budget
from `source_original_source03_true_nu_signed_raw_minus_Knu_minor434`
has the right arbitrary prescribed target log saving after
absorbing true polynomial character and global-cell losses.
The 500 is the genuine 2*2*125 bound from the signed
triangle, not a claim of operator cancellation. -/
theorem source_original_true_minor_entire_polynomial_budget434
    (L : ℝ) (hL : 1 ≤ L)
    (Qchar : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (Cchar Cxi Bsave Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hQchar : (Qchar:ℝ) ≤ L^Cchar)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (hBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave) :
    2*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
         (125*L^(-Bsave)) +125*L^(-Bsave)) ≤
      500*L^(-Bgoal) := by
  have hFirst :=
    source_original_true_minor_polynomial_loss_absorb434
      L hL Qchar xi hxi Cchar Cxi Bsave Bgoal
      hQchar hXi hBudget
  have hBsave : Bgoal ≤ Bsave := by
    nlinarith [hBudget, hCchar, hCxi]
  have hSecond :
      L^(-Bsave) ≤ L^(-Bgoal) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith [hBsave])
  have hA :
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
        (125*L^(-Bsave)) ≤
          125*L^(-Bgoal) := by
    calc
      _ = 125*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
          L^(-Bsave)) := by ring
      _ ≤ 125*L^(-Bgoal) :=
        mul_le_mul_of_nonneg_left hFirst (by norm_num)
  have hB :
      125*L^(-Bsave) ≤ 125*L^(-Bgoal) :=
    mul_le_mul_of_nonneg_left hSecond (by norm_num)
  nlinarith [hA,hB]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalOwnMinorBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Exact SOURCE03 full ν-mode original RAW-minus-primitive-Knu
physical selected-cell signed C6 BUDGET, including all four
matched input and output windows and two independent original
characters. The real loss 2*(16*125*A+2000)*L^-Bsave
is bounded by 8000*L^-Bgoal with the explicit
8*(Cchar+Cxi) exponent budget; no hidden atom or
physical-slot factor. -/
theorem source_original_true_physical_own_minor_budget434
    (L : ℝ) (hL : 1 ≤ L)
    (Qchar : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (Cchar Cxi Bsave Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hQchar : (Qchar:ℝ) ≤ L^Cchar)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (hBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave) :
    2*(16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
          (125*L^(-Bsave))) + 2000*L^(-Bsave)) ≤
        8000*L^(-Bgoal) := by
  have hKnu := source_original_true_minor_polynomial_loss_absorb434
    L hL Qchar xi hxi Cchar Cxi Bsave Bgoal
    hQchar hXi hBudget
  have hBsave : Bgoal ≤ Bsave := by
    nlinarith [hBudget,hCchar,hCxi]
  have hRaw : L^(-Bsave) ≤ L^(-Bgoal) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  nlinarith [hKnu,hRaw]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductAtomMinorCircle -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 7000000

/-- Uniform original product-atom saving on the complement of the actual
circle arcs. The threshold precedes all group types, labels, cells and tests.
The factor |k| and the original real H'=U1*U2 are retained. -/
theorem eventually_source_product_atom_minor_circle434
    (cexp dexp Aarc Bsave Carc C1 C2 Chigh C0 vmin D : ℝ) (m0 : ℕ)
    (hc : 0 < cexp) (hd : 0 ≤ dexp) (hdA : dexp < Aarc)
    (hB : 0 ≤ Bsave) (hCarc : Aarc+Bsave ≤ Carc)
    (hChigh : 0 ≤ Chigh) (hv : 0 < vmin) (hC0 : 0 ≤ C0)
    (hChoice : 2*(C0*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vmin⁻¹)^m0)+D) ≤ Bsave) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ {γ₁ γ₂ : Type} [DecidableEq γ₁] [DecidableEq γ₂]
        (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
        (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
        (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
        (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ),
        (∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p) →
        (∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p) →
        (∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h)) →
        (∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h)) →
        (∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ)) →
        (∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ)) →
        (∀ g ∈ G₁, k₁ g ≤ m0) → (∀ g ∈ G₂, k₂ g ≤ m0) →
        (∀ g ∈ G₁, vmin ≤ V₁ g) → (∀ g ∈ G₂, vmin ≤ V₂ g) →
        (G₁.card:ℝ) ≤ C0*Real.log L → (G₂.card:ℝ) ≤ C0*Real.log L →
        ∀ (M N P Q : ℕ), 0 < M → 0 < N → P ≤ M → Q ≤ N →
        ∀ (U1 U2 : ℝ),
        Real.exp (L^cexp-C1) ≤ U1 → Real.exp (L^cexp-C2) ≤ U2 →
        U1 ≤ (M:ℝ) → U2 ≤ (N:ℝ) →
        U1*U2 ≤ Real.exp (Chigh*Real.log L*L^dexp) →
        ∀ (b₁ b₂ : ℕ → ℂ),
        (∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1) →
        (∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1) →
        ∀ (k : ℤ), k ≠ 0 → ∀ theta : AddCircle (1:ℝ),
        theta ∉ sourceCircleRationalArcs434
          (k.natAbs*Nat.ceil (L^Bsave)) (L^Carc/(U1*U2)) →
        ‖sourceProductMultiplier434 M N P Q
          (sourceProductAtomMass G₁ S₁ k₁ V₁)
          (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ k theta‖ ≤ 16*L^(-D) := by
  have hGeom := eventually_source_circle_minor_rational434
    cexp dexp Aarc Bsave Carc C1 C2 Chigh hc hd hdA hB hCarc hChigh
  filter_upwards [hGeom] with L hL
  refine ⟨hL.1,?_⟩
  intro γ₁ γ₂ _ _ G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N P Q hM hN hP hQ U1 U2 hMscale hNscale hU1M hU2N hHigh b₁ b₂ hb₁ hb₂ k hk theta hOutside
  obtain ⟨theta,rfl⟩ := Quotient.exists_rep theta
  have hU1 : 0 < U1 := (Real.exp_pos _).trans_le hMscale
  have hU2 : 0 < U2 := (Real.exp_pos _).trans_le hNscale
  obtain ⟨a,r,hr,hcop,hNear,hrlo,hBracket⟩ := hL.2
    U1 U2 (U1*U2) hMscale hNscale rfl
    (mul_pos hU1 hU2) hHigh theta k hk hOutside
  have hBracketNative := (source_c6_four_term_mono434 U1 U2 (M:ℝ) (N:ℝ)
    r hU1 hU2 hU1M hU2N hr).trans hBracket
  have hRaw := source_product_atom_multiplier_rational434
    G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact
    m0 vmin C0 L hv hL.1 hC0 hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N P Q hM hN hP hQ b₁ b₂ hb₁ hb₂ a k r theta Bsave hr hcop hNear hBracketNative
  dsimp only at hRaw
  have hExp : C0*Real.log ((Nat.factorial m0:ℝ)*(max (1:ℝ) vmin⁻¹)^m0)-
      Bsave/2 ≤ -D := by linarith
  exact hRaw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL.1 hExp) (by norm_num))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductLogCellMinor -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 7000000

/-- Uniform complete-logcell product-atom saving on the complement of the actual
circle arcs. The threshold precedes all group types, labels, cells and tests.
The factor |k| and the original real H'=U1*U2 are retained. -/
theorem eventually_source_product_logcell_minor_circle434
    (cexp dexp Aarc Bsave Carc C1 C2 Chigh C0 vmin D : ℝ) (m0 : ℕ)
    (hc : 0 < cexp) (hd : 0 ≤ dexp) (hdA : dexp < Aarc)
    (hB : 0 ≤ Bsave) (hCarc : Aarc+Bsave ≤ Carc)
    (hChigh : 0 ≤ Chigh) (hv : 0 < vmin) (hC0 : 0 ≤ C0)
    (hChoice : 2*(C0*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vmin⁻¹)^m0)+D) ≤ Bsave) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ {γ₁ γ₂ : Type} [DecidableEq γ₁] [DecidableEq γ₂]
        (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
        (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
        (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
        (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ),
        (∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p) →
        (∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p) →
        (∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h)) →
        (∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h)) →
        (∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ)) →
        (∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ)) →
        (∀ g ∈ G₁, k₁ g ≤ m0) → (∀ g ∈ G₂, k₂ g ≤ m0) →
        (∀ g ∈ G₁, vmin ≤ V₁ g) → (∀ g ∈ G₂, vmin ≤ V₂ g) →
        (G₁.card:ℝ) ≤ C0*Real.log L → (G₂.card:ℝ) ≤ C0*Real.log L →
        ∀ (M N : ℕ), 0 < M → 0 < N →
        ∀ (U1 U2 : ℝ),
        Real.exp (L^cexp-C1) ≤ U1 → Real.exp (L^cexp-C2) ≤ U2 →
        U1 ≤ (M:ℝ) → U2 ≤ (N:ℝ) →
        U1*U2 ≤ Real.exp (Chigh*Real.log L*L^dexp) →
        ∀ (b₁ b₂ : ℕ → ℂ),
        (∀ n ∈ Finset.Ico M (M+3*M), ‖b₁ n‖ ≤ 1) →
        (∀ n ∈ Finset.Ico N (N+3*N), ‖b₂ n‖ ≤ 1) →
        ∀ (k : ℤ), k ≠ 0 → ∀ theta : AddCircle (1:ℝ),
        theta ∉ sourceCircleRationalArcs434
          (k.natAbs*Nat.ceil (L^Bsave)) (L^Carc/(U1*U2)) →
        ‖sourceProductMultiplier434 M N (3*M) (3*N)
          (sourceProductAtomMass G₁ S₁ k₁ V₁)
          (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ k theta‖ ≤ 64*L^(-D) := by
  have hMinor := eventually_source_product_atom_minor_circle434
    cexp dexp Aarc Bsave Carc C1 C2 Chigh C0 vmin D m0
    hc hd hdA hB hCarc hChigh hv hC0 hChoice
  filter_upwards [hMinor] with L hMinorL
  refine ⟨hMinorL.1,?_⟩
  intro γ₁ γ₂ _ _ G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N hM hN U1 U2 hMscale hNscale hU1M hU2N hHigh b₁ b₂ hb₁ hb₂ k hk theta hOutside
  have hBlock (M' N' : ℕ) (hMlo : M ≤ M') (hNlo : N ≤ N')
      (hMhi : M'+M' ≤ M+3*M) (hNhi : N'+N' ≤ N+3*N) :
      ‖sourceProductMultiplier434 M' N' M' N'
        (sourceProductAtomMass G₁ S₁ k₁ V₁)
        (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ k theta‖ ≤ 16*L^(-D) := by
    have hMbound : U1 ≤ (M':ℝ) := hU1M.trans (by exact_mod_cast hMlo)
    have hNbound : U2 ≤ (N':ℝ) := hU2N.trans (by exact_mod_cast hNlo)
    refine hMinorL.2 G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact
      hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂ M' N' M' N'
      (by omega) (by omega) le_rfl le_rfl U1 U2 hMscale hNscale hMbound hNbound hHigh
      b₁ b₂ ?_ ?_ k hk theta hOutside
    · intro n hn
      apply hb₁
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    · intro n hn
      apply hb₂
      simp only [Finset.mem_Ico] at hn ⊢
      omega
  have hAll := source_product_multiplier_four_block_bound434 M N
    (sourceProductAtomMass G₁ S₁ k₁ V₁) (sourceProductAtomMass G₂ S₂ k₂ V₂)
    b₁ b₂ k theta (16*L^(-D))
    (hBlock M N (by omega) (by omega) (by omega) (by omega))
    (hBlock M (2*N) (by omega) (by omega) (by omega) (by omega))
    (hBlock (2*M) N (by omega) (by omega) (by omega) (by omega))
    (hBlock (2*M) (2*N) (by omega) (by omega) (by omega) (by omega))
  nlinarith

/-- An actual width-one logarithmic cell lies in the four-block envelope
based at ceil(U), including both endpoints of the source cell. -/
theorem source_log_cell_nat_cover434 (U : ℝ) (n : ℕ)
    (hU : 0 < U) (hLo : U ≤ (n:ℝ)) (hHi : (n:ℝ) ≤ Real.exp 1*U) :
    n ∈ Finset.Ico (Nat.ceil U) (Nat.ceil U+3*Nat.ceil U) := by
  have hM : U ≤ (Nat.ceil U:ℝ) := Nat.le_ceil U
  have hMp : (0:ℝ) < (Nat.ceil U:ℝ) := hU.trans_le hM
  have hE := mul_lt_mul_of_pos_right Real.exp_one_lt_three hU
  refine Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hLo,?_⟩
  have hn : (n:ℝ) < ((Nat.ceil U+3*Nat.ceil U:ℕ):ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hn
end Green64Analytic.CorrelationSquare

end

/-! ## SourceTruncatedLimit -/

section

set_option maxHeartbeats 1800000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Specialization of the PREVIOUSLY CHECKED genuine-source simplex
continuity to fixed b and variable w; no density-limit premise. -/
theorem sourceSimplexTerm_continuous_w (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ContinuousAt (fun w : ℝ =>
      Green64Analytic.SmallB.sourceSimplexTerm n b w) 1 := by
  have hOn : ContinuousOn (fun q : ℝ × ℝ =>
      Green64Analytic.SmallB.sourceSimplexTerm n q.1 q.2)
      {q | 0 < q.1} := by
    simpa only [Green64Analytic.SmallB.sourceSimplexTerm] using
      (Green64Analytic.ReciprocalSimplex.literal_simplex_continuity
        (n+1) (by omega))
  have hOpen : IsOpen {q : ℝ × ℝ | 0 < q.1} :=
    isOpen_lt continuous_const continuous_fst
  have hmem : (b, (1:ℝ)) ∈ {q : ℝ × ℝ | 0 < q.1} := hb
  have hAt := hOn.continuousAt (hOpen.mem_nhds hmem)
  exact hAt.comp ((continuous_const.prodMk continuous_id).continuousAt)

theorem sourceIntegral_continuous_w (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ContinuousAt (fun w : ℝ =>
      ∫ t in sourceRegion (n+1) b w, sourceKernel (n+1) w t) 1 := by
  have hf : (((n+2).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n+2)
  have hEq (w : ℝ) :
      (∫ t in sourceRegion (n+1) b w, sourceKernel (n+1) w t) =
        ((n+2).factorial : ℝ) *
          Green64Analytic.SmallB.sourceSimplexTerm n b w := by
    rw [sourceSimplexTerm_eq]
    field_simp
  have hCont : ContinuousAt (fun w : ℝ =>
      ((n+2).factorial : ℝ) *
        Green64Analytic.SmallB.sourceSimplexTerm n b w) 1 :=
    continuousAt_const.mul (sourceSimplexTerm_continuous_w n b hb)
  simpa only [←hEq] using hCont

/-- The kernel-denominator change disappears as δ↓0. This is an
independent quantitative limit, not a boundary-null assumption. -/
theorem source_integral_shift_error_tendsto (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun δ : ℝ =>
      (∫ t in sourceRegion (n+1) b (1-δ),
        sourceKernel (n+1) (1-δ) t) -
      (∫ t in sourceRegion (n+1) b (1-δ),
        sourceKernel (n+1) 1 t))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let E : ℝ → ℝ := fun δ =>
    (∫ t in sourceRegion (n+1) b (1-δ),
      sourceKernel (n+1) (1-δ) t) -
    (∫ t in sourceRegion (n+1) b (1-δ),
      sourceKernel (n+1) 1 t)
  have hbounds : ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)),
      0 ≤ E δ ∧ E δ ≤ δ * (b⁻¹)^((n+1)+2) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact source_integral_shift_bound (n+1) b δ hb hδ.le
  have hlim : Tendsto (fun δ : ℝ => δ * (b⁻¹)^((n+1)+2))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hh.mul_const ((b⁻¹)^((n+1)+2))

  have hLo : ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)), 0 ≤ E δ := by
    filter_upwards [hbounds] with δ hh
    exact hh.1
  have hUp : ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)),
      E δ ≤ δ * (b⁻¹)^((n+1)+2) := by
    filter_upwards [hbounds] with δ hh
    exact hh.2
  exact squeeze_zero' hLo hUp hlim

/-- A FULL δ↓0 TRUNCATION-REMOVAL theorem, for each actual source
prime-count summand with its genuine w=1 dependent denominator.
No measure-of-hyperplane or hypothetical moving-simplex limit is used. -/
theorem source_truncated_integral_tendsto (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun δ : ℝ =>
      ∫ t in sourceRegion (n+1) b (1-δ),
        sourceKernel (n+1) 1 t)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in sourceRegion (n+1) b 1,
        sourceKernel (n+1) 1 t)) := by
  let J : ℝ → ℝ := fun δ =>
    ∫ t in sourceRegion (n+1) b (1-δ),
      sourceKernel (n+1) (1-δ) t
  let I : ℝ → ℝ := fun δ =>
    ∫ t in sourceRegion (n+1) b (1-δ),
      sourceKernel (n+1) 1 t
  let full : ℝ := ∫ t in sourceRegion (n+1) b 1,
      sourceKernel (n+1) 1 t
  have hW : Tendsto (fun δ : ℝ => 1-δ)
      (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    have h0 : Tendsto (fun δ : ℝ => 1-δ)
        (𝓝 (0:ℝ)) (𝓝 (1:ℝ)) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)))
    exact h0.mono_left nhdsWithin_le_nhds
  have hJ : Tendsto J (𝓝[>] (0:ℝ)) (𝓝 full) := by
    exact (sourceIntegral_continuous_w n b hb).tendsto.comp hW
  have hE : Tendsto (fun δ => J δ - I δ)
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    source_integral_shift_error_tendsto n b hb

  have hI : Tendsto (fun δ => J δ - (J δ - I δ))
      (𝓝[>] (0:ℝ)) (𝓝 (full - 0)) := hJ.sub hE
  have heq (δ : ℝ) : J δ - (J δ - I δ) = I δ := by ring
  simpa only [sub_zero, heq, I, full] using hI

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceFullDensityDelta -/

section

set_option maxHeartbeats 1600000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- The exact w=1 dependent-prime kernel on a δ-truncated region,
retaining the source 1/(n+2)! normalization. -/
noncomputable def truncatedSourceTerm (n : ℕ) (b δ : ℝ) : ℝ :=
  (∫ t in sourceRegion (n+1) b (1-δ),
      sourceKernel (n+1) 1 t) / ((n+2).factorial : ℝ)

/-- The one-prime term remains exactly 1. -/
noncomputable def truncatedSourceDensity (b δ : ℝ) : ℝ :=
  1 + ∑' n : ℕ, truncatedSourceTerm n b δ

theorem truncatedSourceTerm_tendsto (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun δ : ℝ => truncatedSourceTerm n b δ)
      (𝓝[>] (0:ℝ))
      (𝓝 (Green64Analytic.SmallB.sourceSimplexTerm n b 1)) := by
  have h := (source_truncated_integral_tendsto n b hb).div_const
    ((n+2).factorial : ℝ)
  simpa only [truncatedSourceTerm, sourceSimplexTerm_eq] using h

/-- The original finite cutoff also truncates every w=1 inner
simplex at all δ≥0. This depends only on exact source geometry. -/
theorem truncatedSourceTerm_zero_of_large
    (N n : ℕ) (b δ : ℝ) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) (hn : N ≤ n) :
    truncatedSourceTerm n b δ = 0 := by
  have hcast : (((N+2 : ℕ) : ℝ)) ≤ ((n+2:ℕ):ℝ) := by
    exact_mod_cast (show N+2 ≤ n+2 by omega)
  have hbound : 1-δ ≤ ((n+2:ℕ):ℝ)*b := by
    nlinarith [mul_le_mul_of_nonneg_right hcast hb.le]
  have hzero :
      (∫ t in sourceRegion (n+1) b (1-δ),
        sourceKernel (n+1) 1 t) = 0 := by
    exact Green64Analytic.ReciprocalSimplex.simplex_boundary_zero
      (n+1) b (1-δ) (sourceKernel (n+1) 1)
      (by omega) (by simpa only [Nat.add_assoc] using hbound)
  simp only [truncatedSourceTerm,hzero,zero_div]

theorem truncatedSourceDensity_finite_cutoff
    (N : ℕ) (b δ : ℝ) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    truncatedSourceDensity b δ =
      1 + ∑ n ∈ Finset.range N, truncatedSourceTerm n b δ := by
  have hs : (∑' n : ℕ, truncatedSourceTerm n b δ) =
      ∑ n ∈ Finset.range N, truncatedSourceTerm n b δ := by
    apply tsum_eq_sum
    intro n hn
    exact truncatedSourceTerm_zero_of_large N n b δ hb hδ hcut
      (by simpa using hn)
  simp only [truncatedSourceDensity,hs]

/-- A single fixed finite set of source dimensions, chosen from b
before δ is sent to zero. -/
theorem truncatedSourceDensity_tendsto_of_cutoff
    (N : ℕ) (b : ℝ) (hb : 0 < b)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    Tendsto (fun δ : ℝ => truncatedSourceDensity b δ)
      (𝓝[>] (0:ℝ))
      (𝓝 (Green64Analytic.SmallB.sourceDensity b 1)) := by
  have hSourceFinite :
      (∑' n : ℕ, Green64Analytic.SmallB.sourceSimplexTerm n b 1) =
      ∑ n ∈ Finset.range N, Green64Analytic.SmallB.sourceSimplexTerm n b 1 := by
    simpa only [Green64Analytic.SmallB.sourceSimplexTerm] using
      (Green64Analytic.ReciprocalSimplex.density_finite_cutoff
        N b 1 hb.le hcut)
  have hFin (s : Finset ℕ) :
      Tendsto (fun δ : ℝ => ∑ n ∈ s, truncatedSourceTerm n b δ)
        (𝓝[>] (0:ℝ))
        (𝓝 (∑ n ∈ s,
          Green64Analytic.SmallB.sourceSimplexTerm n b 1)) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact tendsto_const_nhds
    | @insert n s hns ih =>
        simpa only [Finset.sum_insert hns] using
          (truncatedSourceTerm_tendsto n b hb).add ih
  have hTarget :
      Tendsto (fun δ : ℝ =>
        1 + ∑ n ∈ Finset.range N, truncatedSourceTerm n b δ)
        (𝓝[>] (0:ℝ))
        (𝓝 (Green64Analytic.SmallB.sourceDensity b 1)) := by
    have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    have h := h1.add (hFin (Finset.range N))
    simpa only [Green64Analytic.SmallB.sourceDensity, one_div, inv_one,
      hSourceFinite] using h

  have hEq :
      (fun δ : ℝ => truncatedSourceDensity b δ) =ᶠ[(𝓝[>] (0:ℝ))]
        (fun δ => 1 + ∑ n ∈ Finset.range N,
          truncatedSourceTerm n b δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact truncatedSourceDensity_finite_cutoff N b δ hb hδ.le hcut
  exact hTarget.congr' hEq.symm

/-- Genuine full-source δ-removal for every fixed b>0. The finite
support in prime-factor length is derived, not made a premise. -/
theorem truncatedSourceDensity_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun δ : ℝ => truncatedSourceDensity b δ)
      (𝓝[>] (0:ℝ))
      (𝓝 (Green64Analytic.SmallB.sourceDensity b 1)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1/b)
  have hbn : (1:ℝ) < (N:ℝ)*b := by
    exact (div_lt_iff₀ hb).mp hN
  have hcut : 1 ≤ ((N+2:ℕ):ℝ)*b := by
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hb.le]
  exact truncatedSourceDensity_tendsto_of_cutoff N b hb hcut

/-- Freeze the truncation δ independently of the prime cutoff L.
For every target precision ε, all sufficiently small positive δ
capture the full literal density to precision ε. -/
theorem truncatedSourceDensity_eventual_lower
    (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)),
       Green64Analytic.SmallB.sourceDensity b 1 ≤
         truncatedSourceDensity b δ + ε := by
  have hT := truncatedSourceDensity_tendsto b hb
  have hMem :
      Green64Analytic.SmallB.sourceDensity b 1 ∈
      Set.Ioi (Green64Analytic.SmallB.sourceDensity b 1 - ε) := by
    exact Set.mem_Ioi.mpr (by linarith)
  have hEv := hT.eventually (isOpen_Ioi.mem_nhds hMem)
  filter_upwards [hEv] with δ hδ
  have hh : Green64Analytic.SmallB.sourceDensity b 1 - ε <
      truncatedSourceDensity b δ := hδ
  linarith

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceMinSectorBridge -/

section

set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The prerequisite of the minimum-sector partition is discharged
by genuine source simplex integrability, not posited. -/
theorem source_partition_unconditional
    (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x in sourceSimplex n b 1,
      (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹) =
    (n + 2 : ℝ) *
      (∫ x in dependentMinimumSector n b 1,
        (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹) := by
  apply minimum_partition_exact n b 1
  have h := Green64Analytic.SourceSimplexGeometry.sourceKernel_integrableOn
      (n+1) b 1 hb
  change IntegrableOn
    (fun x : Fin (n+1) → ℝ =>
      (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹)
    (sourceSimplex n b 1) at h
  exact h

/-- Exact n+2-prime source simplex coefficient after choosing the
minimum coordinate, with the factorial reduced by exactly one. -/
theorem sourceSimplexTerm_eq_minimum_sector
    (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Green64Analytic.SmallB.sourceSimplexTerm n b 1 =
      (∫ x in dependentMinimumSector n b 1,
        (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹) /
          ((n+1).factorial : ℝ) := by
  have hpart := source_partition_unconditional n b hb
  let J : ℝ :=
    (∫ x in dependentMinimumSector n b 1,
        (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹)
  change ((∫ x in sourceSimplex n b 1,
    (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹) /
      ((n+2).factorial : ℝ)) = J / ((n+1).factorial : ℝ)
  rw [hpart]
  have hfac : (n + 2 : ℝ) / ((n+2).factorial : ℝ) =
      1 / ((n+1).factorial : ℝ) := by
    convert (factorial_minimum_normalization (n+1)) using 1
    simp [Nat.add_assoc, Nat.cast_add, Nat.cast_one]
    ring
  calc
    ((n+2:ℝ) * J) / ((n+2).factorial:ℝ) =
        J * ((n+2:ℝ)/((n+2).factorial:ℝ)) := by ring
    _ = J * (1/((n+1).factorial:ℝ)) := by rw [hfac]
    _ = J / ((n+1).factorial:ℝ) := by ring

end Green64Analytic.MinDisintegration

end

/-! ## SourceDensityMinimum -/

section

set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The exact dependent-minimum contribution in a source simplex
with n+2 total primes and the reduced n+1 factorial. -/
noncomputable def minimumSectorTerm (n : ℕ) (b : ℝ) : ℝ :=
  (∫ x in dependentMinimumSector n b 1,
    (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹) /
      ((n+1).factorial : ℝ)

/-- The complete original source density minus its one-prime term
equals the sum of actual dependent-minimum sectors, for b>0.
No additional integrability or disintegration hypothesis. -/
theorem sourceDensity_sub_one_eq_minimum_tsum
    (b : ℝ) (hb : 0 < b) :
    Green64Analytic.SmallB.sourceDensity b 1 - 1 =
      ∑' n : ℕ, minimumSectorTerm n b := by
  have heq : (fun n : ℕ =>
      Green64Analytic.SmallB.sourceSimplexTerm n b 1) =
        (fun n : ℕ => minimumSectorTerm n b) := by
    funext n
    exact sourceSimplexTerm_eq_minimum_sector n b hb
  unfold Green64Analytic.SmallB.sourceDensity
  simp only [one_div, inv_one, heq]
  ring

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberGeometry -/

section

set_option maxHeartbeats 3000000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- Split off slot zero without forgetting the original finite-coordinate measure. -/
noncomputable def fiberInsert (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) : Fin (n+1) → ℝ :=
  (0 : Fin (n+1)).insertNth z.1 z.2

/-- Swap that slot with the actual dependent last coordinate. -/
noncomputable def fiberIndependent (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) : Fin (n+1) → ℝ :=
  exchangeDependent n 1 0 (fiberInsert n z)

theorem fiberInsert_zero (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    fiberInsert n z 0 = z.1 := by
  simp [fiberInsert]

theorem fiberInsert_tail (n : ℕ) (z : ℝ × (Fin n → ℝ))
    (j : Fin n) :
    fiberInsert n z ((0 : Fin (n+1)).succAbove j) = z.2 j := by
  simp [fiberInsert]
theorem fiberIndependent_zero (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) :
    fiberIndependent n z 0 = 1-z.1-∑ j : Fin n, z.2 j := by
  unfold fiberIndependent
  rw [exchange_dependent_at, Fin.sum_univ_succAbove
      (fun j => fiberInsert n z j) 0]
  rw [fiberInsert_zero]
  have ht : (∑ j : Fin n, fiberInsert n z ((0 : Fin (n+1)).succAbove j)) =
      ∑ j : Fin n, z.2 j := by
    apply Finset.sum_congr rfl
    intro j _
    exact fiberInsert_tail n z j
  rw [ht]
  ring

theorem fiberIndependent_tail (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) (j : Fin n) :
    fiberIndependent n z ((0 : Fin (n+1)).succAbove j) = z.2 j := by
  unfold fiberIndependent
  rw [exchange_dependent_other]
  exact fiberInsert_tail n z j

theorem fiberIndependent_last (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) :
    1 - ∑ j : Fin (n+1), fiberIndependent n z j = z.1 := by
  unfold fiberIndependent
  rw [exchange_dependent_last, fiberInsert_zero]
/-- The affine reflection has determinant ±1, with full original
Lebesgue product normalization in every dimension, including n=0. -/
theorem fiberIndependent_measurePreserving (n : ℕ) :
    MeasurePreserving (fiberIndependent n)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n+1) → ℝ)) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n+1) => ℝ) (0 : Fin (n+1))
  have hsplit := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n+1) => ℝ) (0 : Fin (n+1))
  have hreverse : MeasurePreserving (fiberInsert n)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n+1) → ℝ)) := by
    have heq : fiberInsert n = e.symm := by
      funext z i
      simp [fiberInsert, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [heq]
    exact hsplit.symm e
  have hExchange : MeasurePreserving (exchangeDependent n 1 0)
      (volume : Measure (Fin (n+1) → ℝ))
      (volume : Measure (Fin (n+1) → ℝ)) := by
    have hmeas : Measurable (exchangeDependent n 1 0) := by
      have hmid : Measurable (fun z : ℝ × (Fin n → ℝ) =>
          (1 - (∑ j : Fin n, z.2 j) - z.1, z.2)) := by fun_prop
      have hEq : exchangeDependent n 1 0 =
          e.symm ∘ (fun z : ℝ × (Fin n → ℝ) =>
            (1 - (∑ j : Fin n, z.2 j) - z.1, z.2)) ∘ e := by
        funext x
        rfl
      rw [hEq]
      exact e.symm.measurable.comp (hmid.comp e.measurable)
    exact ⟨hmeas, exchange_dependent_volume n 1 0⟩
  exact hExchange.comp hreverse

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberSector -/

section

set_option maxHeartbeats 3000000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- Exactly the dependent-minimum sector in (minimum, remaining coordinates)
coordinates; no artificial positivity or surrogate kernel. -/
def fiberSector (n : ℕ) (b : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {z | b ≤ z.1 ∧ (∀ i, z.1 ≤ z.2 i) ∧
      (∑ i : Fin n, z.2 i) ≤ 1-2*z.1}

theorem fiberSector_mem_iff (n : ℕ) (b : ℝ)
    (z : ℝ × (Fin n → ℝ)) :
    z ∈ fiberSector n b ↔ b ≤ z.1 ∧
       z.2 ∈ Green64Analytic.SourceSimplexGeometry.sourceRegion n z.1 (1-z.1) := by
  change (b ≤ z.1 ∧ (∀ i, z.1 ≤ z.2 i) ∧
      (∑ i : Fin n, z.2 i) ≤ 1-2*z.1) ↔
      (b ≤ z.1 ∧ (∀ i, z.1 ≤ z.2 i) ∧
      (∑ i : Fin n, z.2 i) ≤ (1-z.1)-z.1)
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h1,h2,by linarith⟩
/-- The geometric description is valid with ALL n+2 source factors.
The last coordinate after reflection is exactly z.1, not a proxy. -/
theorem fiberSector_iff_minimum
    (n : ℕ) (b : ℝ) (z : ℝ × (Fin n → ℝ)) :
    fiberIndependent n z ∈ dependentMinimumSector n b 1 ↔
      z ∈ fiberSector n b := by
  let x := fiberIndependent n z
  have hlast : 1 - ∑ i : Fin (n+1), x i = z.1 :=
    fiberIndependent_last n z
  have hzero : x 0 = 1-z.1-∑ j : Fin n, z.2 j :=
    fiberIndependent_zero n z
  have htail (j : Fin n) : x (Fin.succ j) = z.2 j := by
    simpa only [Fin.zero_succAbove] using fiberIndependent_tail n z j
  constructor
  · intro h
    rcases h with ⟨hs,hmin⟩
    have hb : b ≤ z.1 := by
      have h := hs.2
      change (∑ i, x i) ≤ 1-b at h
      linarith
    have hother (j : Fin n) : z.1 ≤ z.2 j := by
      have hj := hmin (Fin.succ j)
      rw [hlast] at hj
      change z.1 ≤ x (Fin.succ j) at hj
      rw [htail] at hj
      exact hj
    have hroom : (∑ j : Fin n, z.2 j) ≤ 1-2*z.1 := by
      have h0 := hmin 0
      rw [hlast] at h0
      change z.1 ≤ x 0 at h0
      rw [hzero] at h0
      linarith
    exact ⟨hb,hother,hroom⟩
  · rintro ⟨hb,hother,hroom⟩
    have hmin (i : Fin (n+1)) : z.1 ≤ x i := by
      induction i using Fin.cases with
      | zero =>
        rw [hzero]
        linarith
      | succ j =>
        rw [htail]
        exact hother j
    have hsource : x ∈ sourceSimplex n b 1 := by
      constructor
      · intro i
        exact hb.trans (hmin i)
      · change (∑ i : Fin (n+1), x i) ≤ 1-b
        linarith
    refine ⟨hsource, ?_⟩
    intro i
    change (1 - ∑ j : Fin (n+1), x j) ≤ x i
    rw [hlast]
    exact hmin i

theorem fiberSector_measurable (n : ℕ) (b : ℝ) :
    MeasurableSet (fiberSector n b) := by
  unfold fiberSector
  measurability

theorem fiberSector_min_le_half (n : ℕ) (b : ℝ) (hb : 0 < b)
    (z : ℝ × (Fin n → ℝ)) (hz : z ∈ fiberSector n b) :
    z.1 ≤ 1/2 := by
  have hn : 0 ≤ (∑ i : Fin n, z.2 i) := by
    apply Finset.sum_nonneg
    intro i _
    linarith [hb, hz.1, hz.2.1 i]
  linarith [hz.2.2,hn]

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberKernel -/

section

set_option maxHeartbeats 3000000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The exact original kernel equals a reciprocal minimum times
the (n+1)-factor residual simplex kernel. -/
theorem fiber_kernel_identity (n : ℕ)
    (z : ℝ × (Fin n → ℝ)) :
    ((∏ j : Fin (n+1), (fiberIndependent n z j)⁻¹) *
      (1 - ∑ j : Fin (n+1), fiberIndependent n z j)⁻¹) =
      z.1⁻¹ * Green64Analytic.SourceSimplexGeometry.sourceKernel n
        (1-z.1) z.2 := by
  rw [fiberIndependent_last, Fin.prod_univ_succAbove
      (fun j : Fin (n+1) => (fiberIndependent n z j)⁻¹) 0]
  rw [fiberIndependent_zero]
  have hp : (∏ j : Fin n,
      (fiberIndependent n z ((0 : Fin (n+1)).succAbove j))⁻¹) =
      ∏ j : Fin n, (z.2 j)⁻¹ := by
    apply Finset.prod_congr rfl
    intro j _
    rw [fiberIndependent_tail]
  rw [hp]
  dsimp [Green64Analytic.SourceSimplexGeometry.sourceKernel]
  ring
/-- The sector integral after the measure-preserving reflection. -/
noncomputable def fiberWeight (n : ℕ) (b : ℝ)
    (z : ℝ × (Fin n → ℝ)) : ℝ :=
  (fiberSector n b).indicator
    (fun z => z.1⁻¹ *
      Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-z.1) z.2) z

noncomputable def originalMinWeight (n : ℕ) (b : ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  (dependentMinimumSector n b 1).indicator
    (fun x => (∏ i : Fin (n+1), (x i)⁻¹) *
      (1 - ∑ i : Fin (n+1), x i)⁻¹) x

theorem originalMinWeight_comp_fiber (n : ℕ) (b : ℝ)
    (z : ℝ × (Fin n → ℝ)) :
    originalMinWeight n b (fiberIndependent n z) = fiberWeight n b z := by
  have hs := (fiberSector_iff_minimum n b z)
  by_cases hz : z ∈ fiberSector n b
  · have hx := hs.mpr hz
    simp only [originalMinWeight, fiberWeight,
      Set.indicator_of_mem hx, Set.indicator_of_mem hz]
    exact fiber_kernel_identity n z
  · have hx : fiberIndependent n z ∉ dependentMinimumSector n b 1 :=
      fun h => hz (hs.mp h)
    simp [originalMinWeight, fiberWeight,
      Set.indicator_of_notMem hz, Set.indicator_of_notMem hx]
/-- Exact normalization: no Jacobian or factorial is introduced
by switching from the original dependent minimum to a fiber. -/
theorem minimum_sector_integral_eq_fiber (n : ℕ) (b : ℝ) :
    (∫ x in dependentMinimumSector n b 1,
      (∏ i : Fin (n+1), (x i)⁻¹) *
        (1 - ∑ i : Fin (n+1), x i)⁻¹) =
      ∫ z : ℝ × (Fin n → ℝ), fiberWeight n b z := by
  have hMeas := dependent_minimum_measurable n b 1
  have hmp := fiberIndependent_measurePreserving n
  have hf : StronglyMeasurable (originalMinWeight n b) :=
    (source_kernel_measurable n 1).stronglyMeasurable.indicator hMeas
  have htransport := MeasureTheory.integral_map_of_stronglyMeasurable
    (μ := ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))))
    hmp.measurable hf
  rw [hmp.map_eq] at htransport
  calc
    _ = ∫ x : Fin (n+1) → ℝ, originalMinWeight n b x := by
      exact (integral_indicator hMeas).symm
    _ = ∫ z : ℝ × (Fin n → ℝ),
        originalMinWeight n b (fiberIndependent n z) :=
      htransport
    _ = ∫ z : ℝ × (Fin n → ℝ), fiberWeight n b z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (originalMinWeight_comp_fiber n b)

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberFubini -/

section

set_option maxHeartbeats 3500000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The original source minimum kernel is integrable, not an
assumption on a transformed probability measure. -/
theorem originalMinWeight_integrable (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (originalMinWeight n b)
      (volume : Measure (Fin (n+1) → ℝ)) := by
  have hsource :=
    Green64Analytic.SourceSimplexGeometry.sourceKernel_integrableOn (n+1) b 1 hb
  have hsubset : dependentMinimumSector n b 1 ⊆ sourceSimplex n b 1 :=
    fun _ hx => hx.1
  change IntegrableOn (fun x : Fin (n+1) → ℝ =>
      (∏ j, (x j)⁻¹) * (1 - ∑ j, x j)⁻¹)
      (sourceSimplex n b 1) at hsource
  have hInt := hsource.mono_set hsubset
  change Integrable ((dependentMinimumSector n b 1).indicator
      (fun x => (∏ j : Fin (n+1), (x j)⁻¹) *
      (1 - ∑ j : Fin (n+1), x j)⁻¹)) volume
  exact hInt.integrable_indicator (dependent_minimum_measurable n b 1)
/-- Honest Bochner-Fubini for the source's physical minimum sector.
The integrability is transported from the original simplex. -/
theorem fiberWeight_integrable (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fiberWeight n b)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have hOrig := originalMinWeight_integrable n b hb
  have hmp := fiberIndependent_measurePreserving n
  have hcomp := (hmp.integrable_comp hOrig.aestronglyMeasurable).mpr hOrig
  have heq : fiberWeight n b =
      (originalMinWeight n b) ∘ (fiberIndependent n) := by
    funext z
    exact (originalMinWeight_comp_fiber n b z).symm
  rw [heq]
  exact hcomp

theorem minimum_sector_integral_fubini
    (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x in dependentMinimumSector n b 1,
      (∏ i : Fin (n+1), (x i)⁻¹) *
        (1 - ∑ i : Fin (n+1), x i)⁻¹) =
      ∫ u : ℝ, ∫ r : Fin n → ℝ, fiberWeight n b (u,r) := by
  rw [minimum_sector_integral_eq_fiber]
  exact integral_prod (fiberWeight n b) (fiberWeight_integrable n b hb)
theorem fiberWeight_slice (n : ℕ) (b u : ℝ) (hbu : b ≤ u)
    (r : Fin n → ℝ) :
    fiberWeight n b (u,r) =
      (Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u)).indicator
        (fun r => u⁻¹ *
          Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r) r := by
  let K := Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u)
  by_cases hr : r ∈ K
  · have hz : (u,r) ∈ fiberSector n b :=
      (fiberSector_mem_iff n b (u,r)).mpr ⟨hbu,hr⟩
    simp only [fiberWeight, Set.indicator_of_mem hz]
    change _ = K.indicator _ r
    rw [Set.indicator_of_mem hr]
  · have hz : (u,r) ∉ fiberSector n b := by
      intro h
      exact hr ((fiberSector_mem_iff n b (u,r)).mp h).2
    simp only [fiberWeight, Set.indicator_of_notMem hz]
    change _ = K.indicator _ r
    rw [Set.indicator_of_notMem hr]
theorem fiberWeight_inner_of_ge (n : ℕ) (b u : ℝ) (hbu : b ≤ u) :
    (∫ r : Fin n → ℝ, fiberWeight n b (u,r)) =
      u⁻¹ * (∫ r in
        Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u),
          Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r) := by
  simp_rw [fiberWeight_slice n b u hbu]
  rw [integral_indicator
    (Green64Analytic.SourceSimplexGeometry.sourceRegion_closed n u (1-u)).measurableSet]
  rw [integral_const_mul]

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberInterval -/

section

set_option maxHeartbeats 3800000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

theorem fiberWeight_inner_of_below (n : ℕ) (b u : ℝ) (hu : u < b) :
    (∫ r : Fin n → ℝ, fiberWeight n b (u,r)) = 0 := by
  have hpoint (r : Fin n → ℝ) : fiberWeight n b (u,r) = 0 := by
    have hs : (u,r) ∉ fiberSector n b := by
      intro hz
      exact (not_le_of_gt hu) hz.1
    simp only [fiberWeight, Set.indicator_of_notMem hs]
  simp only [hpoint, integral_zero]

theorem fiberWeight_inner_of_above (n : ℕ) (b u : ℝ)
    (hb : 0 < b) (hu : 1/2 < u) :
    (∫ r : Fin n → ℝ, fiberWeight n b (u,r)) = 0 := by
  have hpoint (r : Fin n → ℝ) : fiberWeight n b (u,r) = 0 := by
    have hs : (u,r) ∉ fiberSector n b := by
      intro hz
      exact (not_le_of_gt hu) (fiberSector_min_le_half n b hb (u,r) hz)
    simp only [fiberWeight, Set.indicator_of_notMem hs]
  simp only [hpoint, integral_zero]
/-- The fiber has support precisely on the original minimum interval
[b, 1/2], with no mass beyond the upper geometric endpoint. -/
theorem fiberWeight_inner_eq_interval_indicator
    (n : ℕ) (b u : ℝ) (hb : 0 < b) :
    (∫ r : Fin n → ℝ, fiberWeight n b (u,r)) =
      (Set.Icc b (1/2)).indicator
        (fun u => u⁻¹ * (∫ r in
          Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u),
          Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r)) u := by
  by_cases hbu : b ≤ u
  · by_cases hupper : u ≤ 1/2
    · have hm : u ∈ Set.Icc b (1/2) := ⟨hbu,hupper⟩
      rw [Set.indicator_of_mem hm]
      exact fiberWeight_inner_of_ge n b u hbu
    · have hu : 1/2 < u := lt_of_not_ge hupper
      have hn : u ∉ Set.Icc b (1/2) := fun h => hupper h.2
      rw [Set.indicator_of_notMem hn]
      exact fiberWeight_inner_of_above n b u hb hu
  · have hu : u < b := lt_of_not_ge hbu
    have hn : u ∉ Set.Icc b (1/2) := fun h => hbu h.1
    rw [Set.indicator_of_notMem hn]
    exact fiberWeight_inner_of_below n b u hu
/-- Exact one-dimensional Fubini identity for EACH literal
n+2-prime minimum sector (before factorial normalization). -/
theorem minimum_sector_integral_eq_interval
    (n : ℕ) (b : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1/2) :
    (∫ x in dependentMinimumSector n b 1,
      (∏ i : Fin (n+1), (x i)⁻¹) *
        (1 - ∑ i : Fin (n+1), x i)⁻¹) =
    ∫ u in b..(1/2), u⁻¹ *
      (∫ r in Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u),
         Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r) := by
  rw [minimum_sector_integral_fubini n b hb]
  simp_rw [fiberWeight_inner_eq_interval_indicator n b _ hb]
  rw [integral_indicator (measurableSet_Icc)]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hbhalf]

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberTerms -/

section

set_option maxHeartbeats 3500000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The source residual-prime length n+1 density at w=1-u,
including its exact (n+1)! normalization. -/
noncomputable def fiberDensityTerm (n : ℕ) (u : ℝ) : ℝ :=
  (∫ r in Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u),
    Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r) /
      ((n+1).factorial : ℝ)

theorem fiberDensityTerm_succ (n : ℕ) (u : ℝ) :
    fiberDensityTerm (n+1) u =
      Green64Analytic.SmallB.sourceSimplexTerm n u (1-u) := by
  rfl

theorem fiberDensityTerm_zero (u : ℝ) (hu : u ≤ 1/2) :
    fiberDensityTerm 0 u = (1-u)⁻¹ := by
  have hreg : Green64Analytic.SourceSimplexGeometry.sourceRegion 0 u (1-u) =
      Set.univ := by
    ext r
    simp [Green64Analytic.SourceSimplexGeometry.sourceRegion]
    linarith
  simp [fiberDensityTerm, hreg, Green64Analytic.SourceSimplexGeometry.sourceKernel,
    Finset.univ_eq_empty, volume_pi]
  change ((Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))
      Set.univ).toReal * (1-u)⁻¹ : ℝ) = (1-u)⁻¹
  rw [Measure.pi_empty_univ]
  norm_num

/-- Each exact original minimum-sector coefficient is its genuine
residual-simplex fiber integral, divided by precisely (n+1)!. -/
theorem minimumSectorTerm_eq_fiber_interval
    (n : ℕ) (b : ℝ) (hb : 0 < b) (hhalf : b ≤ 1/2) :
    minimumSectorTerm n b =
      ∫ u in b..(1/2), u⁻¹ * fiberDensityTerm n u := by
  have hbase := minimum_sector_integral_eq_interval n b hb hhalf
  unfold minimumSectorTerm
  rw [hbase]
  unfold fiberDensityTerm
  have hh := (intervalIntegral.integral_mul_const
      (a := b) (b := (1/2:ℝ)) (μ := volume)
      (((n+1).factorial : ℝ)⁻¹)
      (fun u : ℝ => u⁻¹ *
        (∫ r in Green64Analytic.SourceSimplexGeometry.sourceRegion n u (1-u),
          Green64Analytic.SourceSimplexGeometry.sourceKernel n (1-u) r))).symm
  simpa [div_eq_mul_inv, mul_assoc] using hh
/-- The original fixed-b density is a finite sum, uniformly for all
minimum values u≥b in the full inner interval. -/
theorem fiberDensity_finite_eq_source
    (N : ℕ) (b u : ℝ)
    (hb : 0 < b) (hbu : b ≤ u) (hhalf : u ≤ 1/2)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    (∑ d ∈ Finset.range (N+1), fiberDensityTerm d u) =
       Green64Analytic.SmallB.sourceDensity u (1-u) := by
  have hu : 0 < u := hb.trans_le hbu
  have hcast : ((N+2:ℕ):ℝ)*b ≤ ((N+2:ℕ):ℝ)*u := by
    gcongr
  have hcut_u : (1-u) ≤ ((N+2:ℕ):ℝ)*u := by linarith
  have hs : (∑' n : ℕ,
      Green64Analytic.SmallB.sourceSimplexTerm n u (1-u)) =
      ∑ n ∈ Finset.range N,
         Green64Analytic.SmallB.sourceSimplexTerm n u (1-u) := by
    simpa only [Green64Analytic.SmallB.sourceSimplexTerm] using
      (Green64Analytic.ReciprocalSimplex.density_finite_cutoff
        N u (1-u) hu.le hcut_u)
  rw [Finset.sum_range_succ']
  rw [fiberDensityTerm_zero u hhalf]
  simp_rw [fiberDensityTerm_succ]
  rw [Green64Analytic.SmallB.sourceDensity, hs]
  ring

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberFullSum -/

section

set_option maxHeartbeats 4000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The true minimum-fiber integrand on the global real line. -/
noncomputable def normalizedFiberTerm (n : ℕ) (b u : ℝ) : ℝ :=
  (∫ r : Fin n → ℝ, fiberWeight n b (u,r)) /
    ((n+1).factorial : ℝ)

theorem normalizedFiberTerm_integrable (n : ℕ) (b : ℝ)
    (hb : 0 < b) :
    Integrable (normalizedFiberTerm n b) (volume : Measure ℝ) := by
  have h := (fiberWeight_integrable n b hb).integral_prod_left
  unfold normalizedFiberTerm
  exact h.div_const ((n+1).factorial : ℝ)

/-- Return to the original minimum sector with exact factorial. -/
theorem minimumSectorTerm_eq_normalizedFiber_integral
    (n : ℕ) (b : ℝ) (hb : 0 < b) :
    minimumSectorTerm n b =
      ∫ u : ℝ, normalizedFiberTerm n b u := by
  have hbase := minimum_sector_integral_fubini n b hb
  unfold minimumSectorTerm normalizedFiberTerm
  rw [hbase]
  have h := (integral_mul_const (μ := (volume : Measure ℝ))
      (((n+1).factorial : ℝ)⁻¹)
      (fun u : ℝ => ∫ r : Fin n → ℝ, fiberWeight n b (u,r))).symm
  simpa [div_eq_mul_inv] using h

theorem normalizedFiberTerm_on_interval (n : ℕ) (b u : ℝ)
    (hbu : b ≤ u) :
    normalizedFiberTerm n b u = u⁻¹ * fiberDensityTerm n u := by
  unfold normalizedFiberTerm fiberDensityTerm
  rw [fiberWeight_inner_of_ge n b u hbu]
  ring

theorem normalizedFiberTerm_outside (n : ℕ) (b u : ℝ)
    (hb : 0 < b) (hu : u ∉ Set.Icc b (1/2)) :
    normalizedFiberTerm n b u = 0 := by
  unfold normalizedFiberTerm
  rw [fiberWeight_inner_eq_interval_indicator n b u hb]
  rw [Set.indicator_of_notMem hu]
  simp
/-- One single length cutoff works for the complete literal original
minimum-sector sum, with exact source factorials. -/
theorem sourceDensity_sub_one_eq_minimum_finite
    (N : ℕ) (b : ℝ) (hb : 0 < b)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    Green64Analytic.SmallB.sourceDensity b 1 - 1 =
      ∑ n ∈ Finset.range N, minimumSectorTerm n b := by
  have hs : (∑' n : ℕ,
      Green64Analytic.SmallB.sourceSimplexTerm n b 1) =
      ∑ n ∈ Finset.range N,
        Green64Analytic.SmallB.sourceSimplexTerm n b 1 := by
    simpa only [Green64Analytic.SmallB.sourceSimplexTerm] using
      (Green64Analytic.ReciprocalSimplex.density_finite_cutoff
        N b 1 hb.le hcut)
  calc
    _ = ∑' n : ℕ, Green64Analytic.SmallB.sourceSimplexTerm n b 1 := by
      simp only [Green64Analytic.SmallB.sourceDensity, one_div, inv_one]
      ring
    _ = ∑ n ∈ Finset.range N,
         Green64Analytic.SmallB.sourceSimplexTerm n b 1 := hs
    _ = ∑ n ∈ Finset.range N, minimumSectorTerm n b := by
      apply Finset.sum_congr rfl
      intro n _
      exact sourceSimplexTerm_eq_minimum_sector n b hb

end Green64Analytic.MinDisintegration

end

/-! ## MinFiberSumPointwise -/

section

set_option maxHeartbeats 3500000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- Uniform finite support of the exact source density in every
minimum coordinate u ∈ [b, 1/2], including the one-prime term. -/
theorem finite_normalizedFiber_sum_eq_density_indicator
    (N : ℕ) (b u : ℝ) (hb : 0 < b)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    (∑ d ∈ Finset.range (N+1), normalizedFiberTerm d b u) =
      (Set.Icc b (1/2)).indicator
        (fun u => u⁻¹ *
          Green64Analytic.SmallB.sourceDensity u (1-u)) u := by
  by_cases hIcc : u ∈ Set.Icc b (1/2)
  · have hbu : b ≤ u := hIcc.1
    have hsum := fiberDensity_finite_eq_source N b u
      hb hbu hIcc.2 hcut
    rw [Set.indicator_of_mem hIcc]
    calc
      _ = ∑ d ∈ Finset.range (N+1), u⁻¹ * fiberDensityTerm d u := by
        apply Finset.sum_congr rfl
        intro d _
        exact normalizedFiberTerm_on_interval d b u hbu
      _ = u⁻¹ * ∑ d ∈ Finset.range (N+1), fiberDensityTerm d u := by
        rw [Finset.mul_sum]
      _ = u⁻¹ * Green64Analytic.SmallB.sourceDensity u (1-u) := by rw [hsum]
  · rw [Set.indicator_of_notMem hIcc]
    apply Finset.sum_eq_zero
    intro d _
    exact normalizedFiberTerm_outside d b u hb hIcc

end Green64Analytic.MinDisintegration

end

/-! ## SourceMinimumDisintegration -/

section

set_option maxHeartbeats 5000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- EXACT original minimum-coordinate disintegration at w=1:
no conditional disintegration, no surrogate kernel, and no assumed
summation/integrability. The right-hand side is the literal
SmallB.sourceDensity at (t, 1-t), with the one-prime term included. -/
theorem literal_minimum_disintegration
    (b : ℝ) (hb : 0 < b) (hhalf : b ≤ 1/2) :
    Green64Analytic.SmallB.sourceDensity b 1 - 1 =
      ∫ t in b..(1/2),
        Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1/b)
  have hN1 : (1:ℝ) < (N:ℝ)*b :=
    (div_lt_iff₀ hb).mp hN
  have hcut : 1 ≤ ((N+2:ℕ):ℝ)*b := by
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hb.le]
  have hcutMore : 1 ≤ (((N+1)+2:ℕ):ℝ)*b := by
    have hcast : ((N+2:ℕ):ℝ) ≤ (((N+1)+2:ℕ):ℝ) := by
      exact_mod_cast (show N+2 ≤ (N+1)+2 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hcast hb.le]
  have hMin := sourceDensity_sub_one_eq_minimum_finite
    (N+1) b hb hcutMore
  have hInt : ∀ d ∈ Finset.range (N+1),
      Integrable (normalizedFiberTerm d b) (volume : Measure ℝ) := by
    intro d _
    exact normalizedFiberTerm_integrable d b hb
  have hPoint (t : ℝ) :
      (∑ d ∈ Finset.range (N+1), normalizedFiberTerm d b t) =
        (Set.Icc b (1/2)).indicator
          (fun t => t⁻¹ *
             Green64Analytic.SmallB.sourceDensity t (1-t)) t :=
    finite_normalizedFiber_sum_eq_density_indicator N b t hb hcut
  calc
    _ = ∑ d ∈ Finset.range (N+1), minimumSectorTerm d b := hMin
    _ = ∑ d ∈ Finset.range (N+1),
          ∫ t : ℝ, normalizedFiberTerm d b t := by
      apply Finset.sum_congr rfl
      intro d _
      exact minimumSectorTerm_eq_normalizedFiber_integral d b hb
    _ = ∫ t : ℝ,
          ∑ d ∈ Finset.range (N+1), normalizedFiberTerm d b t :=
      (integral_finsetSum (Finset.range (N+1)) hInt).symm
    _ = ∫ t : ℝ, (Set.Icc b (1/2)).indicator
          (fun t => t⁻¹ *
              Green64Analytic.SmallB.sourceDensity t (1-t)) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => hPoint t)
    _ = ∫ t in b..(1/2),
          Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹ := by
      rw [integral_indicator measurableSet_Icc]
      rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le hhalf]
      apply intervalIntegral.integral_congr
      intro t _
      ring

end Green64Analytic.MinDisintegration

end

/-! ## MinDensityIntegrability -/

section

set_option maxHeartbeats 4000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.MinDisintegration

/-- The actual source D_t(1-t)/t is interval-integrable, derived
from the transported original minimum-sector integrability and
finite support of all prime-factor lengths. -/
theorem source_density_intervalIntegrable
    (b : ℝ) (hb : 0 < b) (hhalf : b ≤ 1/2) :
    IntervalIntegrable
      (fun t : ℝ => Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹)
      volume b (1/2) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/b)
  have hN1 : (1:ℝ) < (N:ℝ)*b := (div_lt_iff₀ hb).mp hN
  have hcut : 1 ≤ ((N+2:ℕ):ℝ)*b := by
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hb.le]
  have hInt : Integrable
      (fun t : ℝ => ∑ d ∈ Finset.range (N+1), normalizedFiberTerm d b t)
      volume := by
    exact integrable_finsetSum (Finset.range (N+1))
      (fun d _ => normalizedFiberTerm_integrable d b hb)
  have hPoint (t : ℝ) :
      (∑ d ∈ Finset.range (N+1), normalizedFiberTerm d b t) =
      (Set.Icc b (1/2)).indicator
        (fun t => Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹) t := by
    rw [finite_normalizedFiber_sum_eq_density_indicator N b t hb hcut]
    by_cases ht : t ∈ Set.Icc b (1/2)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hInd : Integrable
      ((Set.Icc b (1/2)).indicator
        (fun t => Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹))
      volume := by
    have heq : (fun t : ℝ => ∑ d ∈ Finset.range (N+1),
          normalizedFiberTerm d b t) =
        ((Set.Icc b (1/2)).indicator
          (fun t => Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹)) :=
      funext hPoint
    rw [← heq]
    exact hInt
  have hOn : IntegrableOn
      (fun t : ℝ => Green64Analytic.SmallB.sourceDensity t (1-t) * t⁻¹)
      (Set.Icc b (1/2)) :=
    (integrable_indicator_iff measurableSet_Icc).mp hInd
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hhalf).mpr hOn

end Green64Analytic.MinDisintegration

end

/-! ## SourceTwistedThetaBound -/

section

namespace Green64Analytic.SourceSW

/-- Explicit transfer from the actual von Mangoldt prefix to prime log weights. -/
theorem norm_twistedTheta_le_twistedPsi_add_primePowerError
    {q x : ℕ} (hx : 1 ≤ x) (χ : DirichletCharacter ℂ q) :
    ‖twistedTheta x χ‖ ≤
      ‖Chen.BombieriVinogradov.twistedPsi x χ‖ +
        2 * Real.sqrt x * Real.log x := by
  calc
    ‖twistedTheta x χ‖ =
        ‖(twistedTheta x χ - Chen.BombieriVinogradov.twistedPsi x χ) +
          Chen.BombieriVinogradov.twistedPsi x χ‖ := by ring
    _ ≤ ‖twistedTheta x χ - Chen.BombieriVinogradov.twistedPsi x χ‖ +
        ‖Chen.BombieriVinogradov.twistedPsi x χ‖ := norm_add_le _ _
    _ ≤ ‖Chen.BombieriVinogradov.twistedPsi x χ‖ +
        2 * Real.sqrt x * Real.log x := by
      have h := norm_twistedPsi_sub_twistedTheta_le_sqrt_log hx χ
      rw [norm_sub_rev] at h
      linarith
end Green64Analytic.SourceSW

end

