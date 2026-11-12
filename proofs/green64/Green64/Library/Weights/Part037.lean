module

public import Green64.Library.Weights.SourceD28UniformBand
public import Green64.Library.Weights.Part035
public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Weights.Part036
public import Green64.Library.Weights.Part033
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part032
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Analysis.Estimates.Part008
public import Green64.Library.Weights.SourceD27LengthSplit
public import Green64.Library.Analysis.Estimates.Part006
public import Green64.Library.Correlation.Part002
public import Green64.Library.Weights.Part012
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib
public import Green64.Library.Weights.Part022
public import Green64.Library.Weights.Part001
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Weights / Part037

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD28UniformGrid -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

/-- PNT reciprocal-grid errors are uniform over ALL selections from a
fixed finite grid. There are only finitely many possible selections,
even if a selection is itself driven by a moving exponent w(L). -/
theorem sourceD28_actual_grid_uniform_in_selection
    (d k : ℕ) (a M ε : ℝ) (u v : Fin k → ℝ)
    (ha : 0<a) (haM : a≤M) (hε : 0<ε)
    (hcells : ∀ j,a≤u j ∧ u j≤v j ∧ v j≤M)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j) :
    ∀ᶠ L : ℝ in atTop, ∀ C : Finset (Fin d → Fin k),
      (∑ ps∈orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) C,
        ∏ i : Fin d,(ps i:ℝ)⁻¹) ≤
      (∑ c∈C,∏ i : Fin d,Real.log (v (c i)/u (c i)))+ε := by
  obtain ⟨K,hK,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  have hAll : ∀ᶠ L : ℝ in atTop,
      ∀ C : Finset (Fin d → Fin k),
        (∑ ps∈orderedPrimeGridTuples d k
          (fun j => actualPrimeCellSet L (u j) (v j)) C,
          ∏ i : Fin d,(ps i:ℝ)⁻¹) -
        (∑ c∈C,∏ i : Fin d,Real.log (v (c i)/u (c i))) < ε := by
    apply Filter.eventually_all.2
    intro C
    have hlim := actual_ordered_prime_grid_tendsto_zero
      d k a M K u v ha haM hK hcells hsep (fun _L => C) hPNT
    have hev := hlim.eventually (isOpen_Iio.mem_nhds hε)
    simpa only [logCell] using hev
  filter_upwards [hAll] with L hL
  intro C
  have h := hL C
  linarith

/-- Uniform arithmetic-grid-to-collar comparison for an arbitrary moving
selection C(w), as long as it sits inside the true geometric band. -/
theorem sourceD28_actual_grid_le_moving_band
    (d k : ℕ) (a M b δ ε : ℝ) (u v : Fin k → ℝ)
    (C : ℝ → Finset (Fin d → Fin k))
    (ha : 0<a) (haM : a≤M) (hb : 0<b) (hε : 0<ε)
    (hcells : ∀ j,a≤u j ∧ u j≤v j ∧ v j≤M)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j)
    (hbu : ∀ j,b≤u j)
    (hband : ∀ w,
      sourceGridUnion d k u v (C w) ⊆
        sourceD26BoundaryBand d b w δ) :
    ∀ᶠ L : ℝ in atTop, ∀ w : ℝ,
      (∑ ps∈orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) (C w),
        ∏ i : Fin d,(ps i:ℝ)⁻¹) ≤
      (∫ t in sourceD26BoundaryBand d b w δ,
        reciprocalProduct d t)+ε := by
  filter_upwards [sourceD28_actual_grid_uniform_in_selection
    d k a M ε u v ha haM hε hcells hsep] with L hL
  intro w
  have hc := sourceD26_continuum_grid_le_band d k b w δ u v (C w)
    hb hbu (fun j => (hcells j).2.1) hsep (hband w)
  linarith [hL (C w)]



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformBandPrefix -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

/-- A SINGLE frozen exponent grid makes the complete original
boundary-band PrefixKernel arbitrarily small, uniformly in every
moving cofactor exponent w from an arbitrary compact interval. -/
theorem sourceD28_uniform_band_prefix_small
    (n : ℕ) (S b A B ε τ : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hε : 0<ε) (hτ : 0<τ) :
    ∃ k : ℕ, 0<k ∧ gridStep b k < b ∧ gridStep b k ≤ τ ∧
      ∀ᶠ L : ℝ in atTop, ∀ w ∈ Set.Icc A B,
        L*(∑ pre∈sourceGridPrefixLists (n+1) k L
          (gridLower b (gridStep b k) k)
          (gridUpper b (gridStep b k) k)
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
            ((Real.exp L)^b) pre) ≤ ε := by
  let η : ℝ := ε*b/8
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨δ0,hδ0,hInt⟩ :=
    sourceD28_uniform_band_integral_small n b A B η hb hη
  have hstep := gridStep_tendsto_zero b
  have hGridEv : ∀ᶠ k : ℕ in atTop,
      0<k ∧ ((n+2:ℝ)*gridStep b k ≤ δ0) ∧
      gridStep b k ≤ b/2 ∧ gridStep b k ≤ τ := by
    have h1 : ∀ᶠ k : ℕ in atTop, 0<k := eventually_gt_atTop 0
    have h2 : ∀ᶠ k : ℕ in atTop, (n+2:ℝ)*gridStep b k < δ0 := by
      have ht := hstep.const_mul (n+2:ℝ)
      have hz : (n+2:ℝ)*0 < δ0 := by simpa using hδ0
      simpa only [mul_zero] using ht.eventually (isOpen_Iio.mem_nhds hz)
    have h3 : ∀ᶠ k : ℕ in atTop, gridStep b k < b/2 :=
      hstep.eventually (isOpen_Iio.mem_nhds (half_pos hb))
    have h4 : ∀ᶠ k : ℕ in atTop, gridStep b k < τ :=
      hstep.eventually (isOpen_Iio.mem_nhds hτ)
    filter_upwards [h1,h2,h3,h4] with k hk h2k h3k h4k
    exact ⟨hk,h2k.le,h3k.le,h4k.le⟩
  obtain ⟨k,hk,hbandwidth,hhhalf,hhτ⟩ := hGridEv.exists
  have hh : 0<gridStep b k := gridStep_pos b k hb1 hk
  have hhb : gridStep b k < b := hhhalf.trans_lt (half_lt_self hb)
  have hcells := sourceD26_grid_cells_basic k b hb hb1 hk
  have hsep : ∀ i j : Fin k, i<j →
      gridUpper b (gridStep b k) k i ≤
      gridLower b (gridStep b k) k j :=
    grid_separated b (gridStep b k) k hh.le
  have hbandwidth' : (((n+1:ℕ):ℝ)+1)*gridStep b k ≤ δ0 := by
    have heq : ((n+1:ℕ):ℝ)+1 = (n:ℝ)+2 := by push_cast;ring
    rw [heq]
    exact hbandwidth
  have hband (w : ℝ) :
      sourceGridUnion (n+1) k
        (gridLower b (gridStep b k) k)
        (gridUpper b (gridStep b k) k)
        (sourceD26BandCells (n+1) k b (gridStep b k) w) ⊆
      sourceD26BoundaryBand (n+1) b w δ0 :=
    (sourceD26_band_grid_union_subset (n+1) k b (gridStep b k) w hh.le).trans
      (sourceD26_boundary_band_mono (n+1) b w
        ((((n+1:ℕ):ℝ)+1)*gridStep b k) δ0 hbandwidth')
  have hActual := sourceD28_actual_grid_le_moving_band
    (n+1) k b 1 b δ0 η
    (gridLower b (gridStep b k) k)
    (gridUpper b (gridStep b k) k)
    (fun w => sourceD26BandCells (n+1) k b (gridStep b k) w)
    hb hb1.le hb hη (fun j => hcells j) hsep
    (fun j => (hcells j).1) hband
  have hzetaT := tendsto_rpow_neg_atTop (show 0<S+1 by linarith)
  have hzeta : ∀ᶠ L : ℝ in atTop, L^(-S-1) ≤ gridStep b k := by
    have hzraw := hzetaT.eventually (Iic_mem_nhds hh)
    filter_upwards [hzraw] with L hLz
    simpa only [show -(S+1) = -S-1 by ring] using hLz
  refine ⟨k,hk,hhb,hhτ,?_⟩
  filter_upwards [hActual,hzeta,eventually_gt_atTop (1:ℝ)]
    with L hact hz hL1
  intro w hw
  have hBandPrefix := sourceD26_band_prefix_le_reciprocal
    (n+1) k S b L w hS hb (by linarith) hz hhb
  have hInv : (b-gridStep b k)⁻¹ ≤ 2/b := by
    have hpos : 0<b-gridStep b k := sub_pos.mpr hhb
    have hbh : b/2 ≤ b-gridStep b k := by linarith [hhhalf]
    calc
      _ ≤ (b/2)⁻¹ := inv_anti₀ (half_pos hb) hbh
      _ = 2/b := by field_simp [hb.ne']
  have hMass0 : 0 ≤
      (∑ ps∈orderedPrimeGridTuples (n+1) k
        (fun j => actualPrimeCellSet L
          (gridLower b (gridStep b k) k j)
          (gridUpper b (gridStep b k) k j))
        (sourceD26BandCells (n+1) k b (gridStep b k) w),
        ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) := by
    apply Finset.sum_nonneg
    intro ps hps
    exact Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hMass : (∑ ps∈orderedPrimeGridTuples (n+1) k
        (fun j => actualPrimeCellSet L
          (gridLower b (gridStep b k) k j)
          (gridUpper b (gridStep b k) k j))
        (sourceD26BandCells (n+1) k b (gridStep b k) w),
        ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) ≤ 2*η := by
    have hIntw := hInt w hw
    have hActw := hact w
    linarith
  have hMul := mul_le_mul_of_nonneg_right hInv hMass0
  have htarget : (2/b)*(2*η) = ε/2 := by
    dsimp [η]
    field_simp [hb.ne']
    ring
  calc
    L*(∑ pre∈sourceGridPrefixLists (n+1) k L
      (gridLower b (gridStep b k) k)
      (gridUpper b (gridStep b k) k)
      (sourceD26BandCells (n+1) k b (gridStep b k) w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) ≤
        (b-gridStep b k)⁻¹ *
        (∑ ps∈orderedPrimeGridTuples (n+1) k
          (fun j => actualPrimeCellSet L
            (gridLower b (gridStep b k) k j)
            (gridUpper b (gridStep b k) k j))
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) := hBandPrefix
    _ ≤ (2/b)*
        (∑ ps∈orderedPrimeGridTuples (n+1) k
          (fun j => actualPrimeCellSet L
            (gridLower b (gridStep b k) k j)
            (gridUpper b (gridStep b k) k j))
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) := hMul
    _ ≤ (2/b)*(2*η) :=
      mul_le_mul_of_nonneg_left hMass (div_nonneg (by norm_num) hb.le)
    _ = ε/2 := htarget
    _ ≤ ε := by linarith [hε]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformWeightedGrid -/

section

open Filter Topology
open scoped BigOperators Classical

namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.ReciprocalPrimeGrid

/-- Uniform quantitative PNT2' grid error for ALL selections AND ALL
bounded nonnegative weights. The weights may depend on an arbitrary
moving cofactor exponent; the eventual L is chosen beforehand. -/
theorem sourceD28_uniform_weighted_grid_error
    (d k : ℕ) (a M W ε : ℝ) (u v : Fin k → ℝ)
    (ha : 0<a) (haM : a≤M) (hW : 0≤W) (hε : 0<ε)
    (hcells : ∀ j,a≤u j ∧ u j≤v j ∧ v j≤M) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (C : Finset (Fin d → Fin k))
        (wt : (Fin d → Fin k) → ℝ),
        (∀ c∈C,0≤wt c) → (∀ c∈C,wt c≤W) →
        (∑ c∈C,wt c*∏ i : Fin d,
          reciprocalPrimeCell L (u (c i)) (v (c i))) ≤
        (∑ c∈C,wt c*∏ i : Fin d,
          Real.log (v (c i)/u (c i)))+ε := by
  obtain ⟨K,hK,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  let E : ℝ → ℝ := fun L => pntGridError a M K L
  have hE : Tendsto E atTop (𝓝 0) :=
    pntGridError_tendsto_zero a M K ha
  let H : ℝ := Real.log (M/a)
  have hEH : Tendsto (fun L => H+E L) atTop (𝓝 H) := by
    simpa using tendsto_const_nhds.add hE
  have hEP : Tendsto (fun L => E L*(H+E L)^(d-1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hE.mul (hEH.pow (d-1))
  let B : ℝ → ℝ := fun L =>
    (k:ℝ)^d*W*((d:ℝ)*E L*(H+E L)^(d-1))
  have hB : Tendsto B atTop (𝓝 0) := by
    have h := hEP.const_mul (((k:ℝ)^d)*W*(d:ℝ))
    simpa only [B,mul_assoc,zero_mul,mul_zero] using h
  have hsmall : ∀ᶠ L : ℝ in atTop, B L < ε :=
    hB.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hPNT,eventually_ge_atTop (1/a),hsmall]
    with L hPNTL hL hsmallL
  have hAl : 1≤a*L := by
    have hh := mul_le_mul_of_nonneg_left hL ha.le
    have hc : a*(1/a)=1 := by field_simp [ha.ne']
    linarith
  intro C wt hwt0 hwt
  have hbound := weighted_prime_grid_uniform_bound
    d k a M L K W u v ha haM hAl hK hW hcells
    hPNTL C wt hwt0 hwt
  have hUp : (∑ c∈C,wt c*∏ i : Fin d,
          reciprocalPrimeCell L (u (c i)) (v (c i))) -
        (∑ c∈C,wt c*∏ i : Fin d,
          Real.log (v (c i)/u (c i))) ≤ B L := by
    exact (le_abs_self _).trans (by simpa only [E,H,B,logCell] using hbound)
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28MovingInteriorUpper -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

/-- One L-threshold for every moving cofactor exponent and every
interior grid selection; the true dependent denominator is retained. -/
theorem sourceD28_moving_upper_corner_grid
    (d k : ℕ) (b M η ε : ℝ) (u v : Fin k → ℝ)
    (C : ℝ → Finset (Fin d → Fin k))
    (hb : 0 < b) (hbM : b ≤ M) (hη : 0 ≤ η) (hε : 0 < ε)
    (hcells : ∀ j, b ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hwidth : ∀ j, v j-u j ≤ η)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ w, ∀ c ∈ C w, b ≤ w-∑ i : Fin d, v (c i)) :
    ∀ᶠ L : ℝ in atTop, ∀ w : ℝ,
      sourceD25UpperArithmeticGrid d k L w u v (C w) ≤
        (∫ t in sourceRegion d b w, sourceKernel d w t) +
        ((d:ℝ)*η/b^2) *
          (∫ t in sourceRegion d b w, reciprocalProduct d t) + ε := by
  have hPNT := sourceD28_uniform_weighted_grid_error
    d k b M b⁻¹ ε u v hb hbM (inv_nonneg.mpr hb.le) hε hcells
  filter_upwards [hPNT] with L hL
  intro w
  have hwt := sourceD25_upper_corner_weight_bounds d k b w v (C w) hb (hroom w)
  have hNum : sourceD25UpperArithmeticGrid d k L w u v (C w) ≤
      sourceD25UpperContinuumGrid d k w u v (C w) + ε := by
    have hh := hL (C w) (fun c => (w-∑ i : Fin d, v (c i))⁻¹)
      (fun c hc => (hwt c hc).1) (fun c hc => (hwt c hc).2)
    simpa only [sourceD25UpperArithmeticGrid,sourceD25UpperContinuumGrid] using hh
  have hCont := sourceD25_upper_continuum_bound
    d k b w η u v (C w) hb hη
    (fun j => (hcells j).1) (fun j => (hcells j).2.1)
    hwidth hsep (hroom w)
  linarith

/-- Uniform in w interior D24 prefix-grid to literal simplex upper,
with a single finite grid and its exact factorial-free coefficient. -/
theorem sourceD28_moving_selected_prefix_to_simplex
    (d k : ℕ) (S γ b M η ε : ℝ) (u v : Fin k → ℝ)
    (C : ℝ → Finset (Fin d → Fin k))
    (hb : 0 < b) (hbM : b ≤ M) (hη : 0 ≤ η) (hε : 0 < ε)
    (hcells : ∀ j, b ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hwidth : ∀ j, v j-u j ≤ η)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ w, ∀ c ∈ C w, b ≤ w-∑ i : Fin d, v (c i)) :
    ∀ᶠ L : ℝ in atTop, ∀ w : ℝ, 0 < L →
      L*(∑ pre ∈ sourceGridPrefixLists d k L u v (C w),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^γ) pre) ≤
        (∫ t in sourceRegion d b w, sourceKernel d w t) +
        ((d:ℝ)*η/b^2) *
          (∫ t in sourceRegion d b w, reciprocalProduct d t) + ε := by
  filter_upwards [sourceD28_moving_upper_corner_grid d k b M η ε u v C
    hb hbM hη hε hcells hwidth hsep hroom] with L hgrid
  intro w hLp
  exact (sourceD25_selected_prefix_kernel_upper d k S γ L w b u v
      (C w) hLp hb (hroom w)).trans
      ((sourceD25_selected_tuple_kernel_upper d k L b w u v (C w)
        hLp hb hsep (hroom w)).trans (hgrid w))



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformMassBudget -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.SourceSimplexGeometry

/-- A single finite continuum reciprocal budget at the largest
cofactor exponent bounds every smaller moving exponent, with
the ORIGINAL source simplex regions and measures. -/
theorem sourceD28_uniform_reciprocal_mass_bound
    (d : ℕ) (b w B : ℝ) (hb : 0<b) (hw : w≤B) :
    (∫ t in sourceRegion d b w, reciprocalProduct d t) ≤
      (∫ t in sourceRegion d b B, reciprocalProduct d t) := by
  have hsub : sourceRegion d b w ⊆ sourceRegion d b B := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hInt : IntegrableOn (reciprocalProduct d) (sourceRegion d b B) :=
    reciprocalProduct_integrableOn_source d b B hb
  have hNonneg : 0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict
      (sourceRegion d b B)] reciprocalProduct d := by
    filter_upwards [ae_restrict_mem (sourceRegion_closed d b B).measurableSet]
      with t ht
    exact reciprocalProduct_nonneg_source d b B hb t ht
  exact setIntegral_mono_set hInt hNonneg (Filter.Eventually.of_forall hsub)

/-- Explicit nonnegative common integral budget, before choosing a
fixed exponent mesh independent of the moving cofactor exponent. -/
theorem sourceD28_uniform_reciprocal_mass_nonneg
    (d : ℕ) (b B : ℝ) (hb : 0<b) :
    0 ≤ (∫ t in sourceRegion d b B, reciprocalProduct d t) := by
  apply setIntegral_nonneg (sourceRegion_closed d b B).measurableSet
  intro t ht
  exact reciprocalProduct_nonneg_source d b B hb t ht



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28FullPrefixUniform -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

/-- Complete all-prefix prime grid -> source literal simplex upper,
UNIFORM in every moving w on a fixed compact exponent interval.
The same fixed k works for all w and all sufficiently large L. -/
theorem sourceD28_uniform_full_prefix_to_simplex
    (n : ℕ) (S b A B ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbA : b<A) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      L*(∑ pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (n+1) ((Real.exp L)^b)
        (Real.exp (L^(-S))*Real.exp (w*L)),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) ≤
      (∫ t in sourceRegion (n+1) b w,
        sourceKernel (n+1) w t) + ε := by
  have _ := hbA
  let d : ℕ := n+1
  let R : ℝ := ∫ t in sourceRegion d b B, reciprocalProduct d t
  have hR : 0≤R := sourceD28_uniform_reciprocal_mass_nonneg d b B hb
  have hD : (0:ℝ)<(d:ℝ) := by dsimp [d]; positivity
  let τ0 : ℝ := ε*b^2/(16*(d:ℝ)*(R+1))
  have hden : 0<16*(d:ℝ)*(R+1) := by positivity
  have hτ0 : 0<τ0 := div_pos (mul_pos hε (sq_pos_of_pos hb)) hden
  let τ : ℝ := min (b/4) τ0
  have hτ : 0<τ := lt_min (by positivity) hτ0
  obtain ⟨k,hk,hhb,hkτ,hBandSmall⟩ :=
    sourceD28_uniform_band_prefix_small n S b A B (ε/4) τ
      hS hb hb1 (by positivity) hτ
  let h : ℝ := gridStep b k
  have hh : 0<h := gridStep_pos b k hb1 hk
  have hcells := sourceD26_grid_cells_basic k b hb hb1 hk
  have hsep : ∀ i j : Fin k, i<j →
      gridUpper b h k i ≤ gridLower b h k j :=
    grid_separated b h k hh.le
  have hwidth : ∀ j : Fin k,
      gridUpper b h k j-gridLower b h k j ≤ h := by
    intro j
    rw [gridUpper_eq_lower_add]
    linarith
  have hroom : ∀ w,∀ c∈sourceD26InteriorCells d k b h w,
      b≤w-∑ i : Fin d,gridUpper b h k (c i) := by
    intro w c hc
    exact sourceD26_interior_room d k b h w c hc
  have hInterior :=
    sourceD28_moving_selected_prefix_to_simplex
      d k S b b 1 h (ε/4)
      (gridLower b h k) (gridUpper b h k)
      (fun w => sourceD26InteriorCells d k b h w)
      hb hb1.le hh.le (by positivity)
      (fun j => hcells j) hwidth hsep hroom
  have hkτ0 : h≤τ0 := hkτ.trans (min_le_right _ _)
  have hbudget : 16*(d:ℝ)*(R+1)*h≤ε*b^2 := by
    have hq : h≤ε*b^2/(16*(d:ℝ)*(R+1)) := by
      simpa only [τ0] using hkτ0
    have hz := (le_div_iff₀ hden).mp hq
    nlinarith
  have hmeshnum : (d:ℝ)*h*R ≤ ε*b^2/16 := by
    have hRm : R≤R+1 := by linarith
    have hp := mul_le_mul_of_nonneg_left hRm (mul_nonneg hD.le hh.le)
    nlinarith [hbudget,hp]
  have hmeshR : (((d:ℝ)*h)/b^2)*R≤ε/16 := by
    have hb2 : 0<b^2 := sq_pos_of_pos hb
    calc
      (((d:ℝ)*h)/b^2)*R = (((d:ℝ)*h)*R)/b^2 := by ring
      _ ≤ (ε*b^2/16)/b^2 :=
        div_le_div_of_nonneg_right hmeshnum hb2.le
      _ = ε/16 := by field_simp [hb2.ne']
  have hzetat := tendsto_rpow_neg_atTop (show 0<S+1 by linarith)
  have hzeta : ∀ᶠ L : ℝ in atTop, L^(-S-1)≤h := by
    have ht := hzetat.eventually (Iic_mem_nhds hh)
    filter_upwards [ht] with L hv
    simpa only [show -(S+1)=-S-1 by ring] using hv
  have hScale : ∀ᶠ L : ℝ in atTop,
      1<L ∧ L^(-S)+B*L≤L := by
    let q : ℝ := 1-B
    have hq : 0<q := sub_pos.mpr hB
    filter_upwards [eventually_gt_atTop (max 1 (1/q))] with L hL
    have hLp : 0<L := by linarith [(le_max_left (1:ℝ) (1/q)).trans_lt hL]
    have hL1 : 1<L := (le_max_left (1:ℝ) (1/q)).trans_lt hL
    have hmesh : L^(-S)≤1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hL1.le (show -S≤0 by linarith)
    have hqL : 1≤q*L := by
      have hhq := mul_le_mul_of_nonneg_left
        ((le_max_right (1:ℝ) (1/q)).trans (le_of_lt hL)) hq.le
      have hcancel : q*(1/q)=1 := by simpa [one_div] using mul_inv_cancel₀ hq.ne'
      linarith
    refine ⟨hL1,?_⟩
    dsimp [q] at hqL
    linarith
  filter_upwards [hBandSmall,hInterior,hzeta,hScale]
    with L hBandL hInteriorL hZ hL
  obtain ⟨hL1,hScaleB⟩ := hL
  have hLp : 0<L := by linarith
  intro w hw
  have hScaleW : L^(-S)+w*L≤L := by
    have hhW := mul_le_mul_of_nonneg_right hw.2 hLp.le
    linarith
  have hSplit := sourceD26_prefix_sum_split
    d k S b L w hS hb hb1 hL1 hk hScaleW hZ hhb
  have hSplitL := mul_le_mul_of_nonneg_left hSplit hLp.le
  rw [mul_add] at hSplitL
  have hMass :
      (∫ t in sourceRegion d b w,reciprocalProduct d t)≤R := by
    exact sourceD28_uniform_reciprocal_mass_bound d b w B hb hw.2
  have hmeshW : (((d:ℝ)*h)/b^2)*
      (∫ t in sourceRegion d b w, reciprocalProduct d t) ≤ ε/16 := by
    have ht := mul_le_mul_of_nonneg_left hMass (div_nonneg
      (mul_nonneg hD.le hh.le) (sq_nonneg b))
    exact ht.trans hmeshR
  have hI : L*(∑ pre∈sourceGridPrefixLists d k L
      (gridLower b h k) (gridUpper b h k)
      (sourceD26InteriorCells d k b h w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) ≤
      (∫ t in sourceRegion d b w,sourceKernel d w t)+ε/16+ε/4 := by
    have hi := hInteriorL w hLp
    linarith [hi,hmeshW]
  have hBand : L*(∑ pre∈sourceGridPrefixLists d k L
      (gridLower b h k) (gridUpper b h k)
      (sourceD26BandCells d k b h w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) ≤ ε/4 := by
    simpa only [d,h] using hBandL w hw
  calc
    _ ≤ L*(∑ pre∈sourceGridPrefixLists d k L
      (gridLower b h k) (gridUpper b h k)
      (sourceD26InteriorCells d k b h w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) +
      L*(∑ pre∈sourceGridPrefixLists d k L
      (gridLower b h k) (gridUpper b h k)
      (sourceD26BandCells d k b h w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) := hSplitL
    _ ≤ ((∫ t in sourceRegion d b w,sourceKernel d w t)+ε/16+ε/4)+ε/4 :=
      add_le_add hI hBand
    _ ≤ (∫ t in sourceRegion d b w,sourceKernel d w t)+ε := by
      linarith [hε]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformKernelBound -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.SourceSimplexGeometry

/-- The EXACT source last-prime simplex kernel, with its dependent
denominator, is at most b^{-1} times reciprocalProduct in its region. -/
theorem sourceD28_source_kernel_reciprocal_pointwise
    (d : ℕ) (b w : ℝ) (hb : 0 < b) (t : Fin d → ℝ)
    (ht : t ∈ sourceRegion d b w) :
    sourceKernel d w t ≤ b⁻¹ * reciprocalProduct d t := by
  have hlast : b ≤ w-∑ i : Fin d, t i := by
    have hh := ht.2
    linarith
  have hinv : (w-∑ i : Fin d,t i)⁻¹ ≤ b⁻¹ :=
    inv_anti₀ hb hlast
  have hpos := reciprocalProduct_nonneg_source d b w hb t ht
  have hh := mul_le_mul_of_nonneg_left hinv hpos
  simpa only [sourceKernel,reciprocalProduct,mul_comm] using hh

/-- A single finite nonnegative integral at the UPPER compact
exponent B bounds ALL source simplex integrals for b<w<=B. -/
theorem sourceD28_uniform_source_kernel_bound
    (d : ℕ) (b w B : ℝ) (hb : 0 < b) (hwB : w ≤ B) :
    (∫ t in sourceRegion d b w, sourceKernel d w t) ≤
      b⁻¹ * (∫ t in sourceRegion d b B, reciprocalProduct d t) := by
  have hIntK := sourceKernel_integrableOn d b w hb
  have hIntR := reciprocalProduct_integrableOn_source d b w hb
  have hMeas := (sourceRegion_closed d b w).measurableSet
  have hPoint (t : Fin d → ℝ) (ht : t ∈ sourceRegion d b w) :
      sourceKernel d w t ≤ b⁻¹ * reciprocalProduct d t :=
    sourceD28_source_kernel_reciprocal_pointwise d b w hb t ht
  have hStep : (∫ t in sourceRegion d b w, sourceKernel d w t) ≤
      (∫ t in sourceRegion d b w, b⁻¹*reciprocalProduct d t) :=
    setIntegral_mono_on hIntK (hIntR.const_mul _) hMeas hPoint
  have hRes := sourceD28_uniform_reciprocal_mass_bound d b w B hb hwB
  calc
    _ ≤ (∫ t in sourceRegion d b w, b⁻¹*reciprocalProduct d t) := hStep
    _ = b⁻¹*(∫ t in sourceRegion d b w, reciprocalProduct d t) := by
      rw [integral_const_mul]
    _ ≤ b⁻¹*(∫ t in sourceRegion d b B, reciprocalProduct d t) :=
      mul_le_mul_of_nonneg_left hRes (inv_nonneg.mpr hb.le)



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformHigherLayer -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.SourceSimplexGeometry

/-- Exact factorial-normalized full-cell higher-prime upper, with a
SINGLE eventual L threshold for ALL moving w in [A,B], including
every threshold w=k*b. The original literal simplex term is retained. -/
theorem sourceD28_uniform_higher_length_cell_upper
    (n : ℕ) (S b A B ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbA : b<A) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
          ((n+2).factorial:ℝ) ≤
      (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+ε) := by
  let d : ℕ := n+1
  let R : ℝ := ∫ t in sourceRegion d b B, reciprocalProduct d t
  let Jmax : ℝ := b⁻¹*R
  have hR : 0≤R := sourceD28_uniform_reciprocal_mass_nonneg d b B hb
  have hJmax : 0≤Jmax := mul_nonneg (inv_nonneg.mpr hb.le) hR
  let η : ℝ := ε*((n+2).factorial:ℝ)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hδquarter,hbudgetMax⟩ :=
    sourceD27_budget_choice Jmax η hJmax hη
  have htuple := sourceD24_ordered_cell_prefix_kernel_upper
    (n+1) S b δ hS hb hδ
  have hprefix := sourceD28_uniform_full_prefix_to_simplex
    n S b A B (η/4) hS hb hb1 hbA hB (by positivity)
  have hlim : Tendsto (fun L : ℝ => Real.exp (L^(-S))) atTop (𝓝 (1:ℝ)) := by
    have hpow : Tendsto (fun L : ℝ => L^(-S)) atTop (𝓝 (0:ℝ)) :=
      tendsto_rpow_neg_atTop hS
    simpa only [Function.comp_def,Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp hpow)
  have hexp : ∀ᶠ L : ℝ in atTop,
      Real.exp (L^(-S))≤1+δ := by
    have he := hlim.eventually (isOpen_Iio.mem_nhds (show (1:ℝ)<1+δ by linarith))
    filter_upwards [he] with L h
    exact h.le
  filter_upwards [htuple,hprefix,hexp,eventually_gt_atTop (0:ℝ)]
    with L htupleL hprefixL hex hL
  intro w hw
  let J : ℝ := ∫ t in sourceRegion d b w,sourceKernel d w t
  let H : ℝ := (Real.exp (L^(-S))-1)*Real.exp (w*L)
  let K : ℝ := ∑ pre ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
    (n+1) ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L)),
    sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre
  let T : ℝ := ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
      (L^(-S)) ((Real.exp L)^b)).card:ℝ)
  have hJ : 0≤J :=
    sourceD27_simplex_nonneg n b w hb
  have hJB : J≤Jmax := by
    simpa only [J,Jmax,R,d] using
      sourceD28_uniform_source_kernel_bound (n+1) b w B hb hw.2
  have hDcoef : 0≤(1+δ)^2-1 := by nlinarith [hδ.le]
  have hJbudget : (1+δ)^2*(J+η/4)≤J+η := by
    have hh := mul_le_mul_of_nonneg_left hJB hDcoef
    nlinarith [hbudgetMax,hh]
  have hH : 0≤H := by
    dsimp [H]
    exact mul_nonneg
      (sub_nonneg.mpr (Real.one_le_exp (Real.rpow_nonneg hL.le _)))
      (Real.exp_pos _).le
  have hfac : (0:ℝ)<((n+2).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos (n+2)
  have hfactor : 0≤(1+δ)*Real.exp (L^(-S))*H := by positivity
  have htupleBound : T ≤ (1+δ)*Real.exp (L^(-S))*H*K := by
    simpa only [T,K,H,mul_assoc] using
      htupleL (Real.exp (w*L)) (Real.exp_pos _).le
  have hprefixBound : L*K ≤ J+η/4 := by
    simpa only [J,K,d] using hprefixL w hw
  have hbound : (1+δ)*Real.exp (L^(-S)) ≤ (1+δ)^2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hex (show (0:ℝ)≤1+δ by linarith)
  have hmain : L*T ≤ H*(J+η) := by
    have hjp : 0≤J+η/4 := by positivity
    calc
      L*T ≤ L*((1+δ)*Real.exp (L^(-S))*H*K) :=
        mul_le_mul_of_nonneg_left htupleBound hL.le
      _ = ((1+δ)*Real.exp (L^(-S))*H)*(L*K) := by ring
      _ ≤ ((1+δ)*Real.exp (L^(-S))*H)*(J+η/4) :=
        mul_le_mul_of_nonneg_left hprefixBound hfactor
      _ = ((1+δ)*Real.exp (L^(-S)))*(H*(J+η/4)) := by ring
      _ ≤ (1+δ)^2*(H*(J+η/4)) :=
        mul_le_mul_of_nonneg_right hbound (mul_nonneg hH hjp)
      _ = H*((1+δ)^2*(J+η/4)) := by ring
      _ ≤ H*(J+η) := mul_le_mul_of_nonneg_left hJbudget hH
  have hScaled : T ≤ (H/L)*(J+η) := by
    have hh : T ≤ H*(J+η)/L :=
      (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hmain)
    calc
      T ≤ H*(J+η)/L := hh
      _ = (H/L)*(J+η) := by ring
  have hSource : Green64Analytic.SmallB.sourceSimplexTerm n b w =
      J/((n+2).factorial:ℝ) := rfl
  rw [hSource]
  apply (div_le_iff₀ hfac).mpr
  have heq : (H/L)*(J/((n+2).factorial:ℝ)+ε)*
      ((n+2).factorial:ℝ) = (H/L)*(J+η) := by
    dsimp [η]
    field_simp [hfac.ne']
  rw [heq]
  exact hScaled


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformFiniteLayers -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- All fixed literal Ω layers in the TRUE complete moving full cell,
uniform in the cofactor exponent w on any compact interval. -/
theorem sourceD28_uniform_finite_all_layers_upper
    (K : ℕ) (S b A B ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbA : b<A) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      (∑ ell∈Finset.range (K+2),
        ((sourceD24OrderedCellTuples ell (Real.exp (w*L))
          (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
          (ell.factorial:ℝ)) ≤
      (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
        (1/w+(∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w)+ε) := by
  let η : ℝ := ε/((K+1:ℕ):ℝ)
  have hKp : (0:ℝ)<((K+1:ℕ):ℝ) := by positivity
  have hη : 0<η := div_pos hε hKp
  have hPrime := sourceD28_uniform_one_prime_length_upper
    S b A B η hS hb hbA hη
  have hComp : ∀ᶠ L : ℝ in atTop,
      ∀ n∈Finset.range K, ∀ w∈Set.Icc A B,
        ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
          (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
            ((n+2).factorial:ℝ) ≤
        (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
          (Green64Analytic.SmallB.sourceSimplexTerm n b w+η) := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact sourceD28_uniform_higher_length_cell_upper
      n S b A B η hS hb hb1 hbA hB hη
  filter_upwards [hPrime,hComp,eventually_gt_atTop (0:ℝ)]
    with L hp hc hL
  intro w hw
  let H : ℝ := ((Real.exp (L^(-S))-1)*Real.exp (w*L))/L
  have hY : 1≤Real.exp (w*L) :=
    Real.one_le_exp (mul_nonneg (hb.trans (hbA.trans_le hw.1)).le hL.le)
  have hSplit := sourceD27_length_sum_split K
    (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) hY
  have hSum : (∑ n∈Finset.range K,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ)/((n+2).factorial:ℝ)) ≤
      H*(∑ n∈Finset.range K,
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) := by
    calc
      _ ≤ ∑ n∈Finset.range K,
          H*(Green64Analytic.SmallB.sourceSimplexTerm n b w+η) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hc n hn w hw
      _ = _ := by rw [Finset.mul_sum]
  have hBudget : η+(K:ℝ)*η=ε := by
    have hh : ((K+1:ℕ):ℝ)*η=ε := mul_div_cancel₀ ε hKp.ne'
    calc
      _ = ((K+1:ℕ):ℝ)*η := by push_cast; ring
      _ = ε := hh
  rw [hSplit]
  have hEq : (∑ n∈Finset.range K,
      (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) =
      (∑ n∈Finset.range K,
        Green64Analytic.SmallB.sourceSimplexTerm n b w)+(K:ℝ)*η := by
    rw [Finset.sum_add_distrib]
    simp
  calc
    _ ≤ H*(1/w+η)+H*(∑ n∈Finset.range K,
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) :=
      add_le_add (hp w hw) hSum
    _ = H*(1/w+(∑ n∈Finset.range K,
        Green64Analytic.SmallB.sourceSimplexTerm n b w)+ε) := by
      rw [hEq]
      calc
        H*(1/w+η)+H*((∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w)+(K:ℝ)*η) =
          H*(1/w+(∑ n∈Finset.range K,
            Green64Analytic.SmallB.sourceSimplexTerm n b w)+(η+(K:ℝ)*η)) := by ring
        _ = _ := by rw [hBudget]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformNumerator -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Original full-cell y-rough numerator: one L-threshold, all
cofactor exponents in a compact interval, ALL Ω lengths and repeated
prime factors, and exact SmallB.sourceDensity even across thresholds. -/
theorem sourceD28_uniform_actual_rough_numerator_density
    (S b A B ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbA : b<A) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      sourceD22Count (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) ≤
        (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
          (Green64Analytic.SmallB.sourceDensity b w+ε) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (B/b)
  have hgap : B < b*((K+2:ℕ):ℝ) := by
    have hh := (div_lt_iff₀ hb).mp hK
    push_cast
    nlinarith [hb]
  have hCutB := sourceD27_fixed_exponent_cutoff K S b B hS hb hgap
  have hε2 : 0<ε/2 := half_pos hε
  have hLayers := sourceD28_uniform_finite_all_layers_upper
    K S b A B (ε/2) hS hb hb1 hbA hB hε2
  have hRepeat := sourceD24_repeated_any_cell_saving S b 1 (ε/2)
    hS hb hε2
  filter_upwards [hCutB,hLayers,hRepeat,eventually_gt_atTop (0:ℝ)]
    with L hCutL hLayersL hRepeatL hL
  intro w hw
  let Y : ℝ := Real.exp (w*L)
  let Δ : ℝ := L^(-S)
  let y : ℝ := (Real.exp L)^b
  let H : ℝ := (Real.exp Δ-1)*Y
  have hY : 0≤Y := (Real.exp_pos _).le
  have hy : 1≤y :=
    Real.one_le_rpow (Real.one_le_exp hL.le) hb.le
  have hYB : Y≤Real.exp (B*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw.2 hL.le)
  have hcut : Real.exp Δ*Y≤y^(K+2) := by
    calc
      Real.exp Δ*Y ≤ Real.exp Δ*Real.exp (B*L) :=
        mul_le_mul_of_nonneg_left hYB (Real.exp_pos _).le
      _ ≤ y^(K+2) := by simpa only [Δ,y] using hCutL
  have hRough : sourceD22Count Y Δ y ≤
      (∑ ell∈Finset.range (K+2),
        ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/
          (ell.factorial:ℝ)) +
      ((sourceD24RepeatedCell Y Δ y).card:ℝ) :=
    sourceD27_full_rough_exact_repeated (K+1) Y Δ y hY hy
      (by simpa only [show (K+1)+1=K+2 by omega] using hcut)
  have hRep : ((sourceD24RepeatedCell Y Δ y).card:ℝ) ≤ (ε/2)*H/L := by
    simpa only [Y,Δ,y,H,Real.rpow_one] using hRepeatL Y hY
  have hSum : (∑ ell∈Finset.range (K+2),
      ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/
        (ell.factorial:ℝ)) ≤
      (H/L)*(1/w+(∑ n∈Finset.range K,
        Green64Analytic.SmallB.sourceSimplexTerm n b w)+ε/2) := by
    simpa only [Y,Δ,y,H] using hLayersL w hw
  have hDensity : 1/w+(∑ n∈Finset.range K,
      Green64Analytic.SmallB.sourceSimplexTerm n b w) =
        Green64Analytic.SmallB.sourceDensity b w :=
    sourceD27_finite_density_identity K b w hb (by nlinarith [hgap, hw.2])
  calc
    sourceD22Count Y Δ y ≤
      (∑ ell∈Finset.range (K+2),
        ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/
          (ell.factorial:ℝ)) +
      ((sourceD24RepeatedCell Y Δ y).card:ℝ) := hRough
    _ ≤ (H/L)*(1/w+(∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w)+ε/2)+
          (ε/2)*H/L := add_le_add hSum hRep
    _ = (H/L)*(Green64Analytic.SmallB.sourceDensity b w+ε) := by
      rw [←hDensity]
      ring


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformRatio -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- SHARP REAL FULL-CELL rough ratio, uniformly for all moving
cofactor exponents in a fixed compact range, including all
multiplicity threshold transitions. No source distribution premise. -/
theorem sourceD28_uniform_actual_full_cell_ratio
    (S b A B ε : ℝ) (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbA : b<A) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      sourceD20CellRatio
        (sourceD22Cell (Real.exp (w*L)) (L^(-S)))
        (Real.exp (Real.sqrt L)) ((Real.exp L)^b) ≤
      (Green64Analytic.SmallB.sourceDensity b w+ε) /
        (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  obtain ⟨C,hC0,hC⟩ := sourceD28_density_compact_bounded b A B hb hbA
  let δ : ℝ := ε/(2*(C+ε+2))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδlt : δ<1 := by
    dsimp [δ]
    apply (div_lt_one (by positivity)).mpr
    linarith [hC0,hε]
  have hδeq : δ*(2*(C+ε+2))=ε := by
    dsimp [δ]
    field_simp
  have hnum := sourceD28_uniform_actual_rough_numerator_density
    S b A B δ hS hb hb1 hbA hB hδ
  filter_upwards [hnum,
    sourceD22_denominator_relative S b δ hb hδ,
    sourceD22_denominator_positive S b hb,
    eventually_gt_atTop (0:ℝ)] with L hNumL hDenL hPosL hL
  intro w hw
  let D : ℝ := Green64Analytic.SmallB.sourceDensity b w
  have hDw : 0≤D := by
    have hh := Green64Analytic.SmallB.sourceDensity_one_prime_lower b w hb
    have hW0 : 0<w := hb.trans (hbA.trans_le hw.1)
    exact (by positivity : (0:ℝ)≤1/w).trans hh
  have hDC : D≤C := hC w hw
  have hmul := mul_le_mul_of_nonneg_left hDC hδ.le
  have hcoef : D+δ ≤ (D+ε)*(1-δ) := by
    nlinarith [hδeq,hmul,hDw,hC0,hδ.le,hε]
  let Y : ℝ := Real.exp (w*L)
  let H : ℝ := (Real.exp (L^(-S))-1)*Y
  let V : ℝ := sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
  let N : ℝ := sourceD22Count Y (L^(-S)) ((Real.exp L)^b)
  let T : ℝ := sourceD22Count Y (L^(-S)) (Real.exp (Real.sqrt L))
  have hY : Real.exp (b*L)≤Y :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (hbA.le.trans hw.1) hL.le)
  have hHp : 0<H := by
    dsimp [H]
    exact mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr
      (Real.rpow_pos_of_pos hL _))) (Real.exp_pos _)
  have hV : 0<V := (inv_pos.mpr (Real.exp_pos _)).trans_le
    (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hT : 0<T := hPosL Y hY
  have hTlower : (1-δ)*H*V≤T := by
    have hh := (abs_le.mp (hDenL Y hY)).1
    change -(δ*(H*V))≤T-H*V at hh
    nlinarith only [hh]
  have hN : N*L≤H*(D+δ) := by
    have hn := hNumL w hw
    change N≤H/L*(D+δ) at hn
    have hh := mul_le_mul_of_nonneg_right hn hL.le
    calc
      N*L ≤ (H/L*(D+δ))*L := hh
      _ = H*(D+δ) := by field_simp [hL.ne']
  change N/T ≤ (D+ε)/(L*V)
  apply (div_le_div_iff₀ hT (mul_pos hL hV)).mpr
  calc
    N*(L*V) = (N*L)*V := by ring
    _ ≤ (H*(D+δ))*V :=
      mul_le_mul_of_nonneg_right hN hV.le
    _ ≤ (H*((D+ε)*(1-δ)))*V := by
      have hh := mul_le_mul_of_nonneg_left hcoef hHp.le
      nlinarith only [hh,hV.le]
    _ = (D+ε)*((1-δ)*H*V) := by ring
    _ ≤ (D+ε)*T :=
      mul_le_mul_of_nonneg_left hTlower (by linarith [hDw,hε])


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD29CellExponent -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- True *complete* logarithmic cell: the exponent of the cell's base
differs from the exponent of any integer it contains by at most Δ/L. -/
theorem sourceD29_cell_exponent_gap
    (L Δ : ℝ) (j n : ℕ) (hL : 0<L) (hΔ : 0<Δ)
    (hn : n∈sourceD20LogCell Δ j) :
    0 < Real.log (n:ℝ)/L - ((j:ℝ)*Δ)/L ∧
      Real.log (n:ℝ)/L - ((j:ℝ)*Δ)/L ≤ Δ/L := by
  have _ := hΔ
  obtain ⟨hl,hu⟩ := (sourceD20_mem_cell Δ j n).mp hn
  have hnpos : (0:ℝ)<n := (Real.exp_pos _).trans hl
  have hlow : (j:ℝ)*Δ < Real.log (n:ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hl
    simpa only [Real.log_exp] using h
  have hhi : Real.log (n:ℝ) ≤ ((j:ℝ)+1)*Δ :=
    (Real.log_le_iff_le_exp hnpos).mpr hu
  have hnum : 0 < Real.log (n:ℝ)-(j:ℝ)*Δ ∧
      Real.log (n:ℝ)-(j:ℝ)*Δ ≤ Δ := by
    constructor <;> nlinarith
  have heq : Real.log (n:ℝ)/L - (j:ℝ)*Δ/L =
      (Real.log (n:ℝ)-(j:ℝ)*Δ)/L := by ring
  rw [heq]
  exact ⟨div_pos hnum.1 hL,div_le_div_of_nonneg_right hnum.2 hL.le⟩

/-- Uniformly for all n in a fixed positive exponent window, the
ACTUAL base of its D20 full cell lies in an expanded compact exponent
window, and is arbitrarily close to log(n)/L. -/
theorem sourceD29_uniform_cell_exponent_bounds
    (S b A B ρ : ℝ) (hS : 0<S) (hb : 0<b)
    (hbA : b<A) (hAB : A≤B) (hB1 : B<1) (hρ : 0<ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (A*L) ≤ (n:ℝ) → (n:ℝ) ≤ Real.exp (B*L) →
      let Δ := L^(-S)
      let j := sourceD20CellIndex Δ n
      let wcell := (j:ℝ)*Δ/L
      let wn := Real.log (n:ℝ)/L
      n∈sourceD20LogCell Δ j ∧
        wcell∈Set.Icc ((A+b)/2) ((B+1)/2) ∧
        wn∈Set.Icc ((A+b)/2) ((B+1)/2) ∧
        dist wcell wn < ρ := by
  have hgap : 0 < (A-b)/2 := by linarith
  have hsmall : ∀ᶠ L : ℝ in atTop,
      L^(-S-1) < min ρ ((A-b)/2) := by
    have ht := tendsto_rpow_neg_atTop (show 0<S+1 by linarith)
    have hh : (0:ℝ) < min ρ ((A-b)/2) := lt_min hρ hgap
    simpa only [show -(S+1)=-S-1 by ring] using
      ht.eventually (isOpen_Iio.mem_nhds hh)
  filter_upwards [hsmall,eventually_gt_atTop (1:ℝ)] with L hsmallL hL1
  have hL : 0<L := by linarith
  have hΔ : 0<L^(-S) := Real.rpow_pos_of_pos hL _
  have hpow : L^(-S)/L = L^(-S-1) := by
    have hh := Real.rpow_sub hL (-S) 1
    rw [Real.rpow_one] at hh
    simpa only [show -S-1=(-S)-1 by ring] using hh.symm
  intro n hnl hnu
  have hA : 0<A := hb.trans hbA
  have hn1 : (1:ℝ)<n := (Real.one_lt_exp_iff.mpr (mul_pos hA hL)).trans_le hnl
  have hn2 : 2≤n := by
    have hnN : 1<n := by exact_mod_cast hn1
    omega
  let Δ : ℝ := L^(-S)
  let j : ℕ := sourceD20CellIndex Δ n
  let wcell : ℝ := (j:ℝ)*Δ/L
  let wn : ℝ := Real.log (n:ℝ)/L
  have hcell : n∈sourceD20LogCell Δ j := sourceD20_index_mem hΔ n hn2
  have hdist0 := sourceD29_cell_exponent_gap L Δ j n hL hΔ hcell
  have hdist1 : 0<wn-wcell ∧ wn-wcell≤L^(-S-1) := by
    dsimp [wn,wcell,Δ] at hdist0 ⊢
    rw [←hpow]
    exact hdist0
  have hlnlo : A≤wn := by
    have hh := Real.log_le_log (Real.exp_pos _) hnl
    rw [Real.log_exp] at hh
    exact (le_div_iff₀ hL).mpr (by simpa only [wn,mul_comm] using hh)
  have hlnhi : wn≤B := by
    have hh := (Real.log_le_iff_le_exp (by linarith : (0:ℝ)<n)).mpr hnu
    exact (div_le_iff₀ hL).mpr (by simpa only [wn,mul_comm] using hh)
  have hcellLo : (A+b)/2≤wcell := by
    have hsmallgap : L^(-S-1) < (A-b)/2 := hsmallL.trans_le (min_le_right _ _)
    linarith [hdist1.2]
  have hcellHi : wcell≤(B+1)/2 := by
    have hUp : B<(B+1)/2 := by linarith [hB1]
    linarith [hdist1.1,hlnhi]
  have hwnLo : (A+b)/2≤wn := by linarith [hlnlo,hbA]
  have hwnHi : wn≤(B+1)/2 := by linarith [hlnhi,hB1]
  have hd : dist wcell wn < ρ := by
    rw [Real.dist_eq]
    have he : wcell-wn<0 := by linarith [hdist1.1]
    rw [abs_of_neg he]
    have hsmallρ : L^(-S-1)<ρ := hsmallL.trans_le (min_le_left _ _)
    linarith [hdist1.2]
  exact ⟨hcell,⟨hcellLo,hcellHi⟩,⟨hwnLo,hwnHi⟩,hd⟩



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD29PointwiseProxy -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- UNIFORM SHARP pointwise bound for the original D20 full-cell rough
proxy at every natural integer in a fixed positive power window. The
actual complete cell is used, even near a multiplicity threshold. -/
theorem sourceD29_original_full_proxy_pointwise_compact
    (S b A B ε : ℝ) (hS : 0<S) (hb : 0<b)
    (hbA : b<A) (hAB : A≤B) (hB : B<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (A*L)≤(n:ℝ) → (n:ℝ)≤Real.exp (B*L) →
      sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L))
        ((Real.exp L)^b) n ≤
      (Green64Analytic.SmallB.sourceDensity b (Real.log (n:ℝ)/L)+ε) /
        (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  let A0 : ℝ := (A+b)/2
  let B0 : ℝ := (B+1)/2
  have hA0 : b<A0 := by dsimp [A0]; linarith [hbA]
  have hB0 : B0<1 := by dsimp [B0]; linarith [hB]
  have hb1 : b<1 := hbA.trans_le (hAB.trans_lt hB).le
  have hε2 : 0<ε/2 := half_pos hε
  have hUC := sourceD27_original_density_uniform_continuity b A0 B0 hb hA0
  obtain ⟨ρ,hρ,hD⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) (ε/2) hε2
  have hCell := sourceD29_uniform_cell_exponent_bounds
    S b A B ρ hS hb hbA hAB hB hρ
  have hRatio := sourceD28_uniform_actual_full_cell_ratio
    S b A0 B0 (ε/2) hS hb hb1 hA0 hB0 hε2
  filter_upwards [hCell,hRatio,eventually_gt_atTop (0:ℝ)]
    with L hCells hRatios hL
  intro n hnl hnu
  let Δ : ℝ := L^(-S)
  let j : ℕ := sourceD20CellIndex Δ n
  let wcell : ℝ := (j:ℝ)*Δ/L
  let wn : ℝ := Real.log (n:ℝ)/L
  let W : ℝ := Real.exp (Real.sqrt L)
  let V : ℝ := sourceNaturalEuler ⌊W⌋₊
  let y : ℝ := (Real.exp L)^b
  have hΔ : 0<Δ := Real.rpow_pos_of_pos hL _
  obtain ⟨hj,hc,hnw,hnear⟩ := hCells n hnl hnu
  have hDclose : dist (Green64Analytic.SmallB.sourceDensity b wcell)
      (Green64Analytic.SmallB.sourceDensity b wn) < ε/2 :=
    hD wcell hc wn hnw hnear
  have hDcomp :
      Green64Analytic.SmallB.sourceDensity b wcell+ε/2 ≤
      Green64Analytic.SmallB.sourceDensity b wn+ε := by
    rw [Real.dist_eq] at hDclose
    have hh := (abs_lt.mp hDclose).2
    linarith
  have hV : 0<V := by
    dsimp [V,W]
    exact (inv_pos.mpr (Real.exp_pos _)).trans_le
      (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hbase : Real.exp (wcell*L) = Real.exp ((j:ℝ)*Δ) := by
    congr 1
    dsimp [wcell]
    field_simp [hL.ne']
  have hfull :
      sourceD20FullProxy Δ W y n ≤
        sourceD20CellRatio
          (sourceD22Cell (Real.exp (wcell*L)) Δ) W y := by
    rw [sourceD20_full_proxy_on_cell hΔ hj]
    rw [sourceD22_log_cell_exact]
    rw [←hbase]
    unfold sourceD20CellProxy
    split_ifs
    · exact le_refl _
    · unfold sourceD20CellRatio
      positivity
  have hR := hRatios wcell hc
  have hfrac := div_le_div_of_nonneg_right hDcomp
    (mul_pos hL hV).le
  dsimp [V,W,y,Δ,wn] at hfull hR hfrac ⊢
  exact hfull.trans (hR.trans hfrac)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceGridMainIdentity -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- The actual normalized last-prime PNT2 main term for a literal
ordered prime prefix, with NO asymptotic approximation. -/
noncomputable def normalizedSourceLastPrimeMain (L : ℝ) (pre : List ℕ) : ℝ :=
  (L / Real.exp L) *
    ((Real.exp L / (pre.prod : ℝ)) /
      Real.log (Real.exp L / (pre.prod : ℝ)))

theorem source_box_main_term_eq (d k : ℕ)
    (b δ a M L : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) (ps : Fin d → ℕ)
    (hL : 0 < L) (hb : 0 < b) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1 - b - δ)
    (hps : ps ∈ orderedPrimeGridTuples d k
      (fun j => actualPrimeCellSet L (u j) (v j)) S) :
    (1 - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
      (∏ i : Fin d, (ps i : ℝ)⁻¹) =
    normalizedSourceLastPrimeMain L (List.ofFn ps) := by
  have hpref := actual_box_prefix_in_truncated_source
    d k b δ a M L u v S hL hb hδ hba hM hcells hroom ps hps
  have hlegal := Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes_legal
    d b δ L (List.ofFn ps) hpref
  have hq : 0 < ((List.ofFn ps).prod : ℝ) := hlegal.1
  have hlogBound : Real.log ((List.ofFn ps).prod : ℝ) ≤
      (1 - b - δ) * L := by
    have hh := Real.log_le_log hq hlegal.2.1
    simpa only [Real.log_exp] using hh
  have hdenNat : 0 < L - Real.log ((List.ofFn ps).prod : ℝ) := by
    have hbd : 0 < (b+δ)*L := mul_pos (add_pos hb hδ) hL
    linarith
  have hden : L - Real.log (∏ i : Fin d, (ps i : ℝ)) ≠ 0 := by
    have hEq : ((List.ofFn ps).prod : ℝ) =
        ∏ i : Fin d, (ps i : ℝ) := by
      rw [List.prod_ofFn, Nat.cast_prod]
    rw [hEq] at hdenNat
    exact ne_of_gt hdenNat
  obtain ⟨c,hc,hbox⟩ := Finset.mem_biUnion.mp hps
  have hpr (i : Fin d) : 0 < ps i := by
    have hpc : ps i ∈ actualPrimeCellSet L (u (c i)) (v (c i)) :=
      (Fintype.mem_piFinset.mp hbox) i
    exact (Finset.mem_filter.mp hpc).2.pos
  simpa only [normalizedSourceLastPrimeMain,
    List.prod_ofFn, Nat.cast_prod] using
      (source_last_prime_main_kernel_identity d L ps (ne_of_gt hL) hpr hden)
/-- The exact arithmetic sum of weighted ordered prime prefixes is
the sum of the source PNT main term. The image List.ofFn is injective,
so repetitions among prime VALUES are retained while duplicate lists
are not introduced by the grid decomposition. -/
theorem source_grid_main_sum_identity (d k : ℕ)
    (b δ a M L : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hL : 0 < L) (hb : 0 < b) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1 - b - δ) :
    (∑ ps ∈ orderedPrimeGridTuples d k
       (fun j => actualPrimeCellSet L (u j) (v j)) S,
       (1 - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
         ∏ i : Fin d, (ps i : ℝ)⁻¹) =
    ∑ pre ∈ sourceGridPrefixLists d k L u v S,
      normalizedSourceLastPrimeMain L pre := by
  classical
  unfold sourceGridPrefixLists
  rw [Finset.sum_image List.ofFn_injective.injOn]
  apply Finset.sum_congr rfl
  intro ps hps
  exact source_box_main_term_eq d k b δ a M L u v S ps
    hL hb hδ hba hM hcells hroom hps

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceLastPrimePNTBridge -/

section

set_option maxHeartbeats 1800000
open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- An arbitrary genuine subfamily G of source δ-truncated ordered
prefixes satisfies the quantitative NORMALIZED last-prime PNT bound.
The total error is controlled by the already proved full source
aggregate error; it is not hypothesized to vanish. -/
theorem selected_prefix_PNT_normalized_lower
    (d : ℕ) (b δ C L : ℝ) (G : Finset (List ℕ))
    (hL : 0 < L) (hb : 0 < b) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hG : G ⊆ Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
      d b δ L)
    (hPNT : ∀ t, Real.exp (b*L) ≤ t →
      |primeRemainder t| ≤ C*t/(Real.log t)^2) :
    (∑ pre ∈ G, normalizedSourceLastPrimeMain L pre) ≤
    (L / Real.exp L) *
      ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) +
    Green64Analytic.LastPrimeErrors.normalizedActualAggregate
      (fun L' => Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
        d b δ L') b δ C L := by
  have _ := hb
  let x : ℝ := Real.exp L
  let z : ℝ := Real.exp (b*L)
  let main : List ℕ → ℝ := fun pre =>
    (x/(pre.prod:ℝ)) / Real.log (x/(pre.prod:ℝ))
  let err : List ℕ → ℝ := fun pre =>
    C * (x/(pre.prod:ℝ)) / (Real.log (x/(pre.prod:ℝ)))^2 + (z+1)
  have hsub : G ⊆ Green64Analytic.OrderedPrimeRough.allPrimeTuples
      d z x := by
    intro pre hpre
    exact (Finset.mem_filter.mp (hG hpre)).1
  have hroom : ∀ pre ∈ G,
      z ≤ x/(pre.prod:ℝ) ∧ z ≤ x/(pre.prod:ℝ) := by
    intro pre hpre
    have hh := truncated_prefix_true_last_prime_room
      d b δ L hL hδ pre (hG hpre)
    exact ⟨hh.1,hh.1⟩
  have hPNT2 : ∀ u : ℝ, z ≤ u →
      |(Nat.primeCounting (Nat.floor u):ℝ) - u/Real.log u| ≤
        C*u/(Real.log u)^2 := by
    intro t ht
    simpa only [primeRemainder, primeCountReal_eq] using hPNT t ht
  have hcount := Green64Analytic.OrderedPrimeRough.ordered_tuples_lower_from_PNT2
    d z x z C G (Real.exp_pos _).le (Real.exp_pos _).le
      hsub hroom hPNT2
  have hcount' :
      (∑ pre ∈ G, (main pre - err pre)) ≤
        ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
          (d+1) z x).card : ℝ) := by
    simpa only [main, err, x, z, sub_add_eq_sub_sub] using hcount
  have hnormMain :
      (∑ pre ∈ G, normalizedSourceLastPrimeMain L pre) =
        (L/x) * ∑ pre ∈ G, main pre := by
    dsimp [normalizedSourceLastPrimeMain, main, x]
    rw [Finset.mul_sum]
  have herr :
      (∑ pre ∈ G, err pre) ≤
      ∑ pre ∈ Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
        d b δ L, err pre := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hG
    intro pre hpre hnot
    dsimp [err]
    have hnon : 0 ≤ C * (x/(pre.prod:ℝ)) /
        (Real.log (x/(pre.prod:ℝ)))^2 := by
      have hcap : 0 ≤ x/(pre.prod:ℝ) := by positivity
      positivity
    have hz : 0 ≤ z+1 := by dsimp [z]; positivity
    linarith
  have hLx : 0 ≤ L / x := by dsimp [x]; positivity
  have herr' := mul_le_mul_of_nonneg_left herr hLx
  have hscaled := mul_le_mul_of_nonneg_left hcount' hLx
  have heq :
      (L/x) * (∑ pre ∈ G, (main pre - err pre)) =
        (L/x) * (∑ pre ∈ G, main pre) -
        (L/x) * (∑ pre ∈ G, err pre) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq] at hscaled
  have hfinal :
      (∑ pre ∈ G, normalizedSourceLastPrimeMain L pre) ≤
        (L/x) *
          ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
            (d+1) z x).card : ℝ) +
          (L/x) * (∑ pre ∈
            Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
              d b δ L, err pre) := by
    rw [hnormMain]
    linarith
  simpa only [Green64Analytic.LastPrimeErrors.normalizedActualAggregate,
    err, x, z, main] using hfinal

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceInnerBoxLimit -/

section

open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Frozen source-EXACT INNER rectangles lower-bound the normalized
last-prime main term, with their correct dt/t product mass and the
dependent last-prime kernel. Unlike a weak-convergence black box, this
uses only the proved uniform prime grid estimate and exact tuple boxes. -/
theorem source_inner_prime_boxes_eventual_lower
    (d k : ℕ) (a M b w C : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (ha : 0 < a) (haM : a ≤ M) (hC : 0 ≤ C) (hb : 0 < b)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i))
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (a * L) ≤ t →
         |primeRemainder t| ≤ C * t / (Real.log t) ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ c ∈ S,
        (w - ∑ i : Fin d, u (c i))⁻¹ *
         ∏ i : Fin d, logCell (u (c i)) (v (c i))) ≤
      (∑ ps ∈ orderedPrimeGridTuples d k
         (fun j => actualPrimeCellSet L (u j) (v j)) S,
         (w - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
           ∏ i : Fin d, (ps i : ℝ)⁻¹) + ε := by
  let cellW : (Fin d → Fin k) → ℝ :=
    fun c => (w - ∑ i : Fin d, u (c i))⁻¹
  let A : ℝ → ℝ := fun L =>
    ∑ c ∈ S, cellW c *
      ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))
  let I : ℝ := ∑ c ∈ S, cellW c *
    ∏ i : Fin d, logCell (u (c i)) (v (c i))
  let B : ℝ → ℝ := fun L =>
    ∑ ps ∈ orderedPrimeGridTuples d k
      (fun j => actualPrimeCellSet L (u j) (v j)) S,
      (w - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
        ∏ i : Fin d, (ps i : ℝ)⁻¹
  have hbound (c : Fin d → Fin k) (hc : c ∈ S) :
      0 ≤ cellW c ∧ cellW c ≤ b⁻¹ := by
    exact lowerCornerKernel_bounded d b w
      (fun i => u (c i)) (fun i => v (c i))
      hb (fun i => (hcells (c i)).2.1) (hroom c hc)
  have hConv : Tendsto (fun L : ℝ => A L - I)
      atTop (𝓝 0) := by
    simpa only [A, I, cellW] using
      (weighted_prime_grid_tendsto_zero d k a M C
        (b⁻¹) u v ha haM hC
        (inv_nonneg.mpr hb.le) hcells
        (fun _ => S) (fun _ c => cellW c)
        (fun _L c hc => (hbound c hc).1)
        (fun _L c hc => (hbound c hc).2) hPNT)
  have hsmall : ∀ᶠ L : ℝ in atTop, -ε < A L - I := by
    have hn : 0 ∈ Set.Ioi (-ε) := neg_lt_zero.mpr hε
    exact hConv.eventually (isOpen_Ioi.mem_nhds hn)
  filter_upwards [hsmall, eventually_gt_atTop (0:ℝ)] with L hnear hL
  have hbox : A L ≤ B L := by
    simpa only [A, B, cellW] using
      (actual_source_last_prime_kernel_box_lower
        d k L b w u v S hL hb hsep
        (fun j => (hcells j).2.1) hroom)
  change I ≤ B L + ε
  linarith

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceInnerPrimeCount -/

section

set_option maxHeartbeats 1800000
open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Source-exact finite INNER-RECTANGLE lower comparison.
The only external analytic assumption is the fully quantified PNT2'
with its elementary π(t)-t/log(t) remainder. Every other step is
derived: moving selected true prime cells, exact last-prime main
factor, summed PNT errors and true source ordered-tuples cardinal. -/
theorem source_inner_boxes_eventually_below_actual_prime_tuples
    (d k : ℕ) (a M b δ C : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (ha : 0 < a) (haM : a ≤ M)
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1) (hC : 0 ≤ C)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1-b-δ)
    (hPNT : ∀ᶠ L : ℝ in atTop, ∀ t, Real.exp (b*L) ≤ t →
      |primeRemainder t| ≤ C*t/(Real.log t)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ c ∈ S,
        (1 - ∑ i : Fin d, u (c i))⁻¹ *
          ∏ i : Fin d, logCell (u (c i)) (v (c i))) ≤
        (L/Real.exp L) *
          ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
            (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) + ε := by
  let E : ℝ → ℝ := fun L =>
    Green64Analytic.LastPrimeErrors.normalizedActualAggregate
      (fun L' => Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
        d b δ L') b δ C L
  have hPNTA : ∀ᶠ L : ℝ in atTop,
      ∀ t, Real.exp (a*L) ≤ t →
        |primeRemainder t| ≤ C*t/(Real.log t)^2 := by
    filter_upwards [hPNT, eventually_ge_atTop (0:ℝ)] with L hpn hL
    intro t ht
    have hh : Real.exp (b*L) ≤ Real.exp (a*L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hba hL)
    exact hpn t (hh.trans ht)
  have hsmallRoom : ∀ c ∈ S,
      b ≤ 1 - ∑ i : Fin d, v (c i) := by
    intro c hc
    have hh := hroom c hc
    linarith
  have hE : Tendsto E atTop (𝓝 0) :=
    Green64Analytic.LastPrimeErrors.actual_source_aggregate_PNT_error_tendsto_zero
      d b δ C hb hb1 hδ hC hPNT
  have hErrSmall : ∀ᶠ L : ℝ in atTop, E L < ε/2 := by
    exact hE.eventually (isOpen_Iio.mem_nhds (half_pos hε))
  have hInner :
      ∀ᶠ L : ℝ in atTop,
      (∑ c ∈ S,
        (1 - ∑ i : Fin d, u (c i))⁻¹ *
          ∏ i : Fin d, logCell (u (c i)) (v (c i))) ≤
      (∑ ps ∈ orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) S,
        (1 - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
          ∏ i : Fin d, (ps i : ℝ)⁻¹) + ε/2 :=
    source_inner_prime_boxes_eventual_lower d k a M b 1 C u v S
      ha haM hC hb hcells hsep hsmallRoom hPNTA
      (ε/2) (half_pos hε)
  filter_upwards [hInner, hErrSmall, hPNT,
      eventually_gt_atTop (0:ℝ)] with L hInner' hErr' hPNT' hL
  have hG :
      sourceGridPrefixLists d k L u v S ⊆
        Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
          d b δ L :=
    sourceGridPrefixLists_subset_truncated d k b δ a M L u v S
      hL hb hδ hba hM hcells hroom
  have hFinite :=
    selected_prefix_PNT_normalized_lower
      d b δ C L (sourceGridPrefixLists d k L u v S)
      hL hb hδ hC hG hPNT'
  have hEq := source_grid_main_sum_identity
    d k b δ a M L u v S hL hb hδ hba hM hcells hroom
  rw [hEq] at hInner'
  dsimp only [E] at hErr'
  linarith

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceInnerFactorial -/

section

set_option maxHeartbeats 1100000
open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Exact per-length factorial normalization, still using ACTUAL
ordered natural prime lists before the disjoint ell-sum is taken. -/
theorem source_inner_boxes_eventually_factorial_normalized
    (d k : ℕ) (a M b δ C : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (ha : 0 < a) (haM : a ≤ M)
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1) (hC : 0 ≤ C)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1-b-δ)
    (hPNT : ∀ᶠ L : ℝ in atTop, ∀ t, Real.exp (b*L) ≤ t →
      |primeRemainder t| ≤ C*t/(Real.log t)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ c ∈ S,
        (1 - ∑ i : Fin d, u (c i))⁻¹ *
          ∏ i : Fin d, logCell (u (c i)) (v (c i))) /
        (((d+1).factorial : ℕ) : ℝ) ≤
      (L/Real.exp L) *
        (((Green64Analytic.OrderedPrimeRough.allPrimeTuples
          (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) /
          (((d+1).factorial : ℕ) : ℝ)) + ε := by
  have hpre :=
    source_inner_boxes_eventually_below_actual_prime_tuples
      d k a M b δ C u v S ha haM hb hb1 hδ hba hM
        hC hcells hsep hroom hPNT ε hε
  filter_upwards [hpre] with L hpreL
  let f : ℝ := (((d+1).factorial : ℕ) : ℝ)
  have hf0 : 0 < f := by
    dsimp [f]
    exact_mod_cast Nat.factorial_pos (d+1)
  have hf1 : (1:ℝ) ≤ f := by
    have hnat : 1 ≤ (d+1).factorial :=
      Nat.succ_le_iff.mpr (Nat.factorial_pos (d+1))
    dsimp [f]
    exact_mod_cast hnat
  have herr : ε ≤ ε*f := by
    nlinarith [mul_le_mul_of_nonneg_left hf1 hε.le]
  apply (div_le_iff₀ hf0).mpr
  calc
    _ ≤ (L/Real.exp L) *
      ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) + ε := hpreL
    _ ≤ (L/Real.exp L) *
      ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) + ε*f := by
          linarith
    _ = ((L/Real.exp L) *
      (((Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (d+1) (Real.exp (b*L)) (Real.exp L)).card : ℝ) / f) + ε) * f := by
          field_simp

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceFiniteInnerSum -/

section

set_option maxHeartbeats 1700000
open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- All FROZEN inner simplex boxes from finitely many prefix
lengths are simultaneously dominated by the ONE original
rough-count, not the number of lengths times that count.
Repeated primes and the literal factorials are retained. -/
theorem finite_inner_simplex_boxes_rough_lower
    (D : Finset ℕ) (k : ℕ) (a M b δ C : ℝ)
    (u v : Fin k → ℝ)
    (S : ∀ d : ℕ, Finset (Fin d → Fin k))
    (ha : 0 < a) (haM : a ≤ M)
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1) (hC : 0 ≤ C)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ d ∈ D, ∀ c ∈ S d,
       (∑ i : Fin d, v (c i)) ≤ 1-b-δ)
    (hPNT : ∀ᶠ L : ℝ in atTop, ∀ t, Real.exp (b*L) ≤ t →
      |primeRemainder t| ≤ C*t/(Real.log t)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ d ∈ D,
        (∑ c ∈ S d,
          (1 - ∑ i : Fin d, u (c i))⁻¹ *
            ∏ i : Fin d, logCell (u (c i)) (v (c i))) /
          ((d+1).factorial : ℝ)) ≤
        (L / Real.exp L) *
          Green64Analytic.SmallB.roughCount b (Real.exp L) + ε := by
  let I : ℕ → ℝ := fun d =>
    (∑ c ∈ S d,
      (1 - ∑ i : Fin d, u (c i))⁻¹ *
        ∏ i : Fin d, logCell (u (c i)) (v (c i))) /
          ((d+1).factorial : ℝ)
  let A : ℕ → ℝ → ℝ := fun d L =>
    (L / Real.exp L) *
      (((Green64Analytic.OrderedPrimeRough.allPrimeTuples (d+1)
        (Real.exp (b*L)) (Real.exp L)).card : ℝ) /
          ((d+1).factorial : ℝ))
  let η : ℝ := ε / ((D.card : ℝ) + 1)
  have hden : 0 < (D.card : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hper : ∀ d ∈ D,
      ∀ᶠ L : ℝ in atTop, I d ≤ A d L + η := by
    intro d hd
    simpa only [I, A] using
      (source_inner_boxes_eventually_factorial_normalized
        d k a M b δ C u v (S d) ha haM hb hb1 hδ
        hba hM hC hcells hsep (hroom d hd) hPNT η hη)
  have hall : ∀ᶠ L : ℝ in atTop,
      ∀ d ∈ D, I d ≤ A d L + η :=
    (Filter.eventually_all_finset D).mpr hper
  filter_upwards [hall, eventually_gt_atTop (0:ℝ)] with L hallL hL
  have hsum : (∑ d ∈ D, I d) ≤
      (∑ d ∈ D, A d L) + (D.card : ℝ) * η := by
    calc
      _ ≤ ∑ d ∈ D, (A d L + η) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hallL d hd
      _ = (∑ d ∈ D, A d L) + (D.card : ℝ) * η := by
        rw [Finset.sum_add_distrib]
        simp
  have hzb : (Real.exp L)^b = Real.exp (b*L) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hx : 1 < Real.exp L := by
    simpa using (Real.exp_lt_exp.mpr hL : Real.exp 0 < Real.exp L)
  have hfac0 :=
    Green64Analytic.OrderedPrimeRough.all_lengths_factorial_sum_le_rough
      (D.image Nat.succ) ((Real.exp L)^b) (Real.exp L)
      (Real.exp_pos _).le
  have hrough :
      ((Green64Analytic.OrderedPrimeRough.roughSet
        ((Real.exp L)^b) (Real.exp L)).card : ℝ) =
      Green64Analytic.SmallB.roughCount b (Real.exp L) :=
    Green64Analytic.OrderedPrimeRough.roughSet_card_eq_source_roughCount
      b (Real.exp L) hb hx
  rw [hrough] at hfac0
  have hfac :
    (∑ d ∈ D,
      (((Green64Analytic.OrderedPrimeRough.allPrimeTuples (d+1)
        (Real.exp (b*L)) (Real.exp L)).card : ℝ) /
          ((d+1).factorial : ℝ))) ≤
      Green64Analytic.SmallB.roughCount b (Real.exp L) := by
    rw [hzb] at hfac0
    rw [Finset.sum_image] at hfac0
    · simpa only [Nat.succ_eq_add_one] using hfac0
    · intro x hx y hy h
      exact Nat.succ_injective h
  have hscale : 0 ≤ L / Real.exp L := by positivity
  have hA :
      (∑ d ∈ D, A d L) ≤
        (L / Real.exp L) *
          Green64Analytic.SmallB.roughCount b (Real.exp L) := by
    have hmul := mul_le_mul_of_nonneg_left hfac hscale
    simpa only [A, Finset.mul_sum] using hmul
  have herr : (D.card : ℝ) * η ≤ ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    have hb : (0:ℝ) ≤ (D.card:ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hε.le hb]
  change (∑ d ∈ D, I d) ≤
     (L / Real.exp L) *
          Green64Analytic.SmallB.roughCount b (Real.exp L) + ε
  linarith

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceGridPrimeRough -/

section

set_option maxHeartbeats 4000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Apply the predecessor's exact PNT2 finite-grid comparison to our
specific disjoint arithmetic grid and the original roughCount. -/
theorem source_fixed_grid_eventually_le_roughCount
    (N k : ℕ) (b δ C ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ)
    (hk : 0 < k) (hC : 0 ≤ C) (hε : 0 < ε)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2) :
    ∀ᶠ L : ℝ in atTop,
      (∑ d ∈ Finset.range (N+1), sourceGridLowerTerm d k b δ) ≤
        (L/Real.exp L)*Green64Analytic.SmallB.roughCount b (Real.exp L)+ε := by
  let h : ℝ := gridStep b k
  let u : Fin k → ℝ := gridLower b h k
  let v : Fin k → ℝ := gridUpper b h k
  let S : ∀ d : ℕ, Finset (Fin d → Fin k) :=
    fun d => admissibleGridCells d k b h δ
  have hh : 0 < h := gridStep_pos b k hb1 hk
  have hcell (j : Fin k) : b ≤ u j ∧ u j ≤ v j ∧ v j ≤ 1 := by
    have hb_u : b ≤ u j := by
      dsimp [u, gridLower]
      have hc : (0:ℝ) ≤ (j.val:ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hc hh.le]
    have huv : u j ≤ v j := gridLower_le_upper b h k j hh.le
    have hv_1 : v j ≤ 1 := gridStep_le b k hb1 hk j
    exact ⟨hb_u, huv, hv_1⟩
  have hsep (i j : Fin k) (hij : i < j) : v i ≤ u j :=
    grid_separated b h k hh.le i j hij
  have hroom (d : ℕ) (hd : d ∈ Finset.range (N+1))
      (c : Fin d → Fin k) (hc : c ∈ S d) :
      (∑ i : Fin d, v (c i)) ≤ 1-b-δ/2 := by
    simpa only [S, v, admissibleGridCells, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc
  have hhP := Green64Analytic.ReciprocalPrimeGrid.finite_inner_simplex_boxes_rough_lower
    (Finset.range (N+1)) k b 1 b (δ/2) C u v S
    hb hb1.le hb hb1.le (half_pos hδ) le_rfl le_rfl hC
    hcell hsep hroom hPNT ε hε
  simpa only [sourceGridLowerTerm,
    Green64Analytic.ReciprocalPrimeGrid.logCell, S, u, v, h]
      using hhP

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceDensityToRough -/

section

set_option maxHeartbeats 5000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- The *full exact* truncated source density lower bound by the
one original rough-number count, rather than separate counts by
prime-factor length. All factorials survive through the assembly. -/
theorem truncated_sourceDensity_eventually_le_rough
    (N : ℕ) (b δ C ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ)
    (hbd : b ≤ 1-δ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2) :
    ∀ᶠ L : ℝ in atTop,
      truncatedSourceDensity b δ ≤
       (L/Real.exp L)*Green64Analytic.SmallB.roughCount b (Real.exp L)+ε := by
  have hη : 0 < ε/2 := half_pos hε
  have hGridEv := truncatedSourceDensity_eventually_grid_lower
    N b δ (ε/2) hb hb1 hδ hbd hη hcut
  obtain ⟨k, hkpos, hmesh, hDarboux⟩ := hGridEv.exists
  have hPrime := source_fixed_grid_eventually_le_roughCount
    N k b δ C (ε/2) hb hb1 hδ hkpos hC hη hPNT
  filter_upwards [hPrime] with L hp
  linarith

/-- The actual full source density D_b(1), with unchanged last-prime
kernel and every prime-factor length, is bounded by the normalized
true roughCount eventually. Only a precisely quantified classical
PNT2' input remains. No conditional positive-prime-mass premise. -/
theorem sourceDensity_eventually_le_rough_of_PNT2
    (b C : ℝ) (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      Green64Analytic.SmallB.sourceDensity b 1 ≤
        (L/Real.exp L)*Green64Analytic.SmallB.roughCount b (Real.exp L)+ε := by
  have hη : 0 < ε/2 := half_pos hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1/b)
  have hbn : (1:ℝ) < (N:ℝ)*b := (div_lt_iff₀ hb).mp hN
  have hcut : 1 ≤ ((N+2:ℕ):ℝ)*b := by
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hb.le]
  have hδlimit := truncatedSourceDensity_eventual_lower b (ε/2) hb hη
  have hδsmall : ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)), δ < 1-b := by
    have hOpen : ∀ᶠ δ : ℝ in 𝓝 (0:ℝ), δ < 1-b :=
      isOpen_Iio.mem_nhds (by linarith : (0:ℝ) < 1-b)
    exact hOpen.filter_mono nhdsWithin_le_nhds
  have hPick : ∀ᶠ δ : ℝ in (𝓝[>] (0:ℝ)),
      0 < δ ∧ δ < 1-b ∧
       Green64Analytic.SmallB.sourceDensity b 1 ≤
          truncatedSourceDensity b δ + ε/2 := by
    filter_upwards [self_mem_nhdsWithin, hδsmall, hδlimit]
      with δ hδ hsmall hlimit
    exact ⟨hδ, hsmall, hlimit⟩
  obtain ⟨δ, hδ, hδbound, hDlower⟩ := hPick.exists
  have hbd : b ≤ 1-δ := by linarith
  have hRough := truncated_sourceDensity_eventually_le_rough
    N b δ C (ε/2) hb hb1 hδ hbd hC hη hcut hPNT
  filter_upwards [hRough] with L hL
  linarith

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceSmallBClosedFromPNT -/

section

set_option maxHeartbeats 4200000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Exact real-x statement required by the original SmallB theorem:
the density-to-rough lower bound is derived, not postulated. -/
theorem source_rough_lower_real_of_PNT2
    (b C : ℝ) (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2) :
    ∀ ε : ℝ, 0 < ε →
       ∀ᶠ x : ℝ in atTop,
         Green64Analytic.SmallB.sourceDensity b 1 ≤
           Real.log x * Green64Analytic.SmallB.roughCount b x / x + ε := by
  intro ε hε
  have hL := sourceDensity_eventually_le_rough_of_PNT2
    b C hb hb1 hC hPNT ε hε
  have hX := Real.tendsto_log_atTop.eventually hL
  filter_upwards [hX, eventually_gt_atTop (1:ℝ)] with x hLx hx
  have hxpos : 0 < x := by linarith
  have hexp : Real.exp (Real.log x) = x := Real.exp_log hxpos
  simpa only [hexp, div_mul_eq_mul_div] using hLx

/-- Small-b source density is now bounded with exact Mertens constant
from the literal sieve and actual roughCount, assuming *only*
a classical quantified PNT2' estimate for natural primes. -/
theorem source_small_b_exp_bound_of_PNT2
    (b C : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100) (hC : 0 ≤ C)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2) :
    Green64Analytic.SmallB.sourceDensity b 1 ≤
      Real.exp (-Real.eulerMascheroniConstant)/b *
        (1+Green64Analytic.SmallB.sieveC *
          Real.exp (-(1/(40*b)))) := by
  have hb1 : b < 1 := by linarith
  exact Green64Analytic.SmallB.source_small_b_exp_bound_of_rough_lower
    b hb hsmall (source_rough_lower_real_of_PNT2 b C hb hb1 hC hPNT)

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceUnconditionalPNT2 -/

section

open Filter Topology Asymptotics Real
open scoped Chebyshev
namespace Green64Analytic.SourcePNT2

theorem literal_density_rough_unconditional
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      Green64Analytic.SmallB.sourceDensity b 1 ≤
        (L/exp L) * Green64Analytic.SmallB.roughCount b (exp L) + ε := by
  obtain ⟨C, hC, hPNT⟩ := source_pnt2_unconditional b hb
  exact Green64Analytic.SourceSimplexGeometry.sourceDensity_eventually_le_rough_of_PNT2
    b C hb hb1 hC hPNT ε hε

theorem literal_small_b_exp_bound_unconditional
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100) :
    Green64Analytic.SmallB.sourceDensity b 1 ≤
      exp (-Real.eulerMascheroniConstant)/b *
        (1 + Green64Analytic.SmallB.sieveC *
          exp (-(1/(40*b)))) := by
  obtain ⟨C, hC, hPNT⟩ := source_pnt2_unconditional b hb
  exact Green64Analytic.SourceSimplexGeometry.source_small_b_exp_bound_of_PNT2
    b C hb hsmall hC hPNT

end Green64Analytic.SourcePNT2

end

/-! ## ActualFineProxyDensity -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.SmallB
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A fixed sharp density constant at the lower physical cofactor exponent.
It does not depend on the later logarithmic-cell precision. -/
def b647RoughDensityCap434 (b A : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant)/b *
    (1+sieveC*Real.exp (-(A/(40*b))))

/-- Literal full source density on every exponent w >= A. The cutoff
b/w lies in the actual small-b range, so no density bound is a premise. -/
theorem b647_source_density_sharp_window434
    (b A w : ℝ) (hb : 0 < b) (hsmall : b ≤ A/100) (hAw : A ≤ w) :
    sourceDensity b w ≤ b647RoughDensityCap434 b A := by
  have hA : 0 < A := by linarith
  have hw : 0 < w := hA.trans_le hAw
  have hbdiv : 0 < b/w := div_pos hb hw
  have hsmalldiv : b/w ≤ 1/100 := by
    apply (div_le_iff₀ hw).mpr
    linarith
  have h := Green64Analytic.SourcePNT2.literal_small_b_exp_bound_unconditional
    (b/w) hbdiv hsmalldiv
  rw [b647_source_density_rescale434 b w hw]
  calc
    _ ≤ w⁻¹*(Real.exp (-Real.eulerMascheroniConstant)/(b/w)*
        (1+sieveC*Real.exp (-(1/(40*(b/w)))))) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hw.le)
    _ = Real.exp (-Real.eulerMascheroniConstant)/b *
        (1+sieveC*Real.exp (-(w/(40*b)))) := by
      have he : 1/(40*(b/w)) = w/(40*b) := by
        field_simp
      rw [he]
      field_simp
    _ ≤ b647RoughDensityCap434 b A := by
      unfold b647RoughDensityCap434
      apply mul_le_mul_of_nonneg_left _ (div_pos (Real.exp_pos _) hb).le
      apply add_le_add (le_refl 1)
      apply mul_le_mul_of_nonneg_left _ sieveC_pos.le
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (div_le_div_of_nonneg_right hAw (by positivity))

/-- Genuine quantitative full-cell rough-proxy bound at every integer in
an entire compact physical cofactor window, including cut endpoint cells
and all multiplicity transitions. No count or density premise remains. -/
theorem b647_actual_rough_fine_proxy_sharp_density434
    (S b A B ε : ℝ) (hS : 0 < S) (hb : 0 < b) (hsmall : b ≤ A/100)
    (hAB : A ≤ B) (hB : B < 1) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (A*L) ≤ (n:ℝ) → (n:ℝ) ≤ Real.exp (B*L) →
      0 ≤ sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L))
        ((Real.exp L)^b) n ∧
      sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L))
        ((Real.exp L)^b) n ≤
      (b647RoughDensityCap434 b A+ε) /
        (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  have hbA : b < A := by linarith
  filter_upwards [sourceD29_original_full_proxy_pointwise_compact
      S b A B ε hS hb hbA hAB hB hε,
    eventually_gt_atTop (0:ℝ)] with L hpoint hL
  intro n hnlow hnhi
  have hV : 0 < sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (inv_pos.mpr (Real.exp_pos _)).trans_le
      (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hlog : A*L ≤ Real.log (n:ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hnlow
    simpa only [Real.log_exp] using hh
  have hAw : A ≤ Real.log (n:ℝ)/L := (le_div_iff₀ hL).mpr hlog
  have hD := b647_source_density_sharp_window434 b A
    (Real.log (n:ℝ)/L) hb hsmall hAw
  refine ⟨?_, (hpoint n hnlow hnhi).trans ?_⟩
  · unfold sourceD20FullProxy sourceD20CellProxy sourceD20CellRatio
    split_ifs <;> positivity
  · exact div_le_div_of_nonneg_right (add_le_add hD (le_refl ε)) (mul_pos hL hV).le

/-- The literal prime and rough proxies used by the SAME signed alpha. -/
def b647ActualFineProxy434 (prime : Bool) (L S b : ℝ) (n : ℕ) : ℝ :=
  if prime then b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n
  else sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^b) n

/-- One actual prime/rough density constant is chosen BEFORE every fine
precision S. Both branches use the full original cell normalizer. -/
theorem b647_actual_prime_or_rough_proxy_density434
    (b A B ε : ℝ) (hb : 0 < b) (hsmall : b ≤ A/100)
    (hAB : A ≤ B) (hB : B < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S →
      ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (n : ℕ),
        Real.exp (A*L) ≤ (n:ℝ) → (n:ℝ) ≤ Real.exp (B*L) →
        0 ≤ b647ActualFineProxy434 prime L S b n ∧
        b647ActualFineProxy434 prime L S b n ≤
          C/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  have hA : 0 < A := by linarith
  refine ⟨max (2/A) (b647RoughDensityCap434 b A+ε),
    (div_pos (by norm_num) hA).trans_le (le_max_left _ _), ?_⟩
  intro S hS
  filter_upwards [b631_actual_prime_fine_proxy_density434 S A 1 hS hA (by norm_num),
    b647_actual_rough_fine_proxy_sharp_density434 S b A B ε
      hS hb hsmall hAB hB hε,
    eventually_gt_atTop (0:ℝ)] with L hprime hrough hL
  intro prime n hnlow hnhi
  have hV : 0 < sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (inv_pos.mpr (Real.exp_pos _)).trans_le
      (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hden : 0 ≤ L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (mul_pos hL hV).le
  cases prime with
  | false =>
    obtain ⟨h0,h1⟩ := hrough n hnlow hnhi
    refine ⟨h0, h1.trans ?_⟩
    exact div_le_div_of_nonneg_right (le_max_right _ _) hden
  | true =>
    have hn1 : (1:ℝ) < n :=
      (Real.one_lt_exp_iff.mpr (mul_pos hA hL)).trans_le hnlow
    have hlog : A*L ≤ Real.log (n:ℝ) := by
      have hh := Real.log_le_log (Real.exp_pos _) hnlow
      simpa only [Real.log_exp] using hh
    have hp : b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n ≤
        2/(Real.log (n:ℝ)*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
      simpa only [show (1:ℝ)+1=2 by norm_num] using hprime n hnlow
    have hratio : 2/(Real.log (n:ℝ)*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ≤
        (2/A)/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
      apply (div_le_div_iff₀ (mul_pos (Real.log_pos hn1) hV) (mul_pos hL hV)).mpr
      calc
        _ = ((2/A)*(A*L))*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ := by
          rw [← mul_assoc (2/A) A L, div_mul_cancel₀ _ hA.ne', mul_assoc]
        _ ≤ ((2/A)*Real.log (n:ℝ))*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog (div_pos (by norm_num) hA).le) hV.le
        _ = _ := by ring
    refine ⟨?_, (hp.trans hratio).trans ?_⟩
    · change 0 ≤ b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n
      unfold b627PrimeFullProxy434
      split_ifs <;> positivity
    · exact div_le_div_of_nonneg_right (le_max_left _ _) hden
end Green64Analytic.SourceBlockSieve

end

end

/-! ## code.GcdReduction -/

section

namespace Green64Analytic.CorrelationD

theorem residual_gcd_unit (rprime r : ℕ) (hr : 0 < r) :
    Nat.Coprime (rprime / Nat.gcd rprime r) (r / Nat.gcd rprime r) := by
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_ne_zero_right (Nat.ne_of_gt hr)).bot_lt

theorem source_short_factor_unit (m rprime r : ℕ)
    (hr : 0 < r) (hm : Nat.Coprime m r) :
    Nat.Coprime m (r / Nat.gcd rprime r) := by
  apply hm.coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right rprime r)

theorem source_three_factor_units (m ps p rprime r : ℕ)
    (hr : 0 < r)
    (hm : Nat.Coprime m r) (hps : Nat.Coprime ps r)
    (hp : Nat.Coprime p r) :
    Nat.Coprime (m * ps * p * (rprime / Nat.gcd rprime r))
      (r / Nat.gcd rprime r) := by
  have hq := residual_gcd_unit rprime r hr
  have hm' := source_short_factor_unit m rprime r hr hm
  have hs' := source_short_factor_unit ps rprime r hr hps
  have hp' := source_short_factor_unit p rprime r hr hp
  exact ((hm'.mul_left hs').mul_left hp').mul_left hq

theorem source_prime_above_modulus_unit (p r : ℕ)
    (hp : p.Prime) (hr : 0 < r) (hsmall : r < p) :
    Nat.Coprime p r := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hh := Nat.le_of_dvd hr hd
  omega
end Green64Analytic.CorrelationD

end

/-! ## code.LiteralCoreDivisorBound -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators

namespace Green64Analytic.CorrelationSquare

noncomputable def sourceUnitTwist (n : ℕ) (σ : ℝ) : ℂ :=
  Complex.exp (((σ * Real.log (n:ℝ):ℝ):ℂ) * Complex.I)

/-- Literal three-factor invariant source core, indexed by all m,p such
    that m*p divides nStar and r=nStar/(m*p). -/
noncomputable def sourceCore (nStar : ℕ) (primeSlot : Finset ℕ)
    (α c : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) : ℂ :=
  ∑ m ∈ nStar.divisors, ∑ p ∈ nStar.divisors,
    if p ∈ primeSlot ∧ p.Prime ∧ m*p ∣ nStar then
      α m * χ m * sourceUnitTwist m σ₀ *
        sourceUnitTwist p σ₁ * c (nStar/(m*p))
    else 0

theorem sourceUnitTwist_norm (n : ℕ) (σ : ℝ) :
    ‖sourceUnitTwist n σ‖ = 1 := by
  simpa [sourceUnitTwist] using
    Complex.norm_exp_ofReal_mul_I (σ * Real.log (n:ℝ))

theorem sourceCore_term_norm_le
    (m p r q : ℕ) (χ : DirichletCharacter ℂ q)
    (α c : ℕ → ℂ) (σ₀ σ₁ A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hα : ‖α m‖ ≤ A) (hc : ‖c r‖ ≤ C) :
    ‖α m * χ m * sourceUnitTwist m σ₀ *
        sourceUnitTwist p σ₁ * c r‖ ≤ A*C := by
  have hχ : ‖χ m‖ ≤ 1 := χ.norm_le_one (m : ZMod q)
  have hfirst : ‖α m‖ * ‖χ m‖ ≤ A := by
    calc
      _ ≤ ‖α m‖ * 1 :=
        mul_le_mul_of_nonneg_left hχ (norm_nonneg _)
      _ ≤ A := by simpa using hα
  calc
    _ = (‖α m‖ * ‖χ m‖) * ‖c r‖ := by
      simp only [norm_mul, sourceUnitTwist_norm, mul_one]
    _ ≤ A * ‖c r‖ :=
        mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
    _ ≤ A*C := mul_le_mul_of_nonneg_left hc hA

theorem sourceCore_divisor_bound
    (nStar q : ℕ) (primeSlot : Finset ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hα : ∀ m, ‖α m‖ ≤ A)
    (hc : ∀ r, ‖c r‖ ≤ C) :
    ‖sourceCore nStar primeSlot α c q χ σ₀ σ₁‖ ≤
       A*C*((nStar.divisors.card : ℝ)^2) := by
  classical
  let D := nStar.divisors
  let f : ℕ → ℕ → ℂ := fun m p =>
    if p ∈ primeSlot ∧ p.Prime ∧ m*p ∣ nStar then
      α m * χ m * sourceUnitTwist m σ₀ *
        sourceUnitTwist p σ₁ * c (nStar/(m*p))
    else 0
  have hterm (m p : ℕ) : ‖f m p‖ ≤ A*C := by
    dsimp [f]
    split_ifs with h
    · exact sourceCore_term_norm_le m p (nStar/(m*p)) q χ α c
        σ₀ σ₁ A C hA hC (hα m) (hc _)
    · simpa using mul_nonneg hA hC
  unfold sourceCore
  change ‖∑ m ∈ D, ∑ p ∈ D, f m p‖ ≤ _
  calc
    _ ≤ ∑ m ∈ D, ‖∑ p ∈ D, f m p‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ D, ∑ p ∈ D, ‖f m p‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ D, ∑ p ∈ D, A*C := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro p hp
      exact hterm m p
    _ = A*C*((nStar.divisors.card : ℝ)^2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [D]
      push_cast
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.SmallMarkPeeling -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

def smallPrimeSupport (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter (fun p => p ∣ n)

def smallPrimeCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  (smallPrimeSupport S n).card

theorem smallPrimeSupport_div
    (S : Finset ℕ) (n p : ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hpS : p ∈ S) (hpn : p ∣ n)
    (hsquare : ¬ p^2 ∣ n) :
    smallPrimeSupport S (n/p) = (smallPrimeSupport S n).erase p := by
  classical
  have hmul : p * (n/p) = n := Nat.mul_div_cancel' hpn
  have hpprime := hprime p hpS
  have hpnot : ¬ p ∣ n/p := by
    rintro ⟨k,hk⟩
    apply hsquare
    refine ⟨k, ?_⟩
    calc
      n = p*(n/p) := hmul.symm
      _ = p*(p*k) := by rw [hk]
      _ = p^2*k := by ring
  ext q
  by_cases hqp : q = p
  · subst q
    have hleft : p ∉ smallPrimeSupport S (n/p) := by
      simpa only [smallPrimeSupport, Finset.mem_filter, hpS, true_and] using hpnot
    have hright : p ∉ (smallPrimeSupport S n).erase p := by simp
    exact iff_of_false hleft hright
  by_cases hqS : q ∈ S
  · have hqprime := hprime q hqS
    have hdiv : q ∣ (n/p) ↔ q ∣ n := by
      constructor
      · intro h
        rw [← hmul]
        exact dvd_mul_of_dvd_right h p
      · intro h
        rw [← hmul] at h
        rcases (hqprime.dvd_mul).mp h with hqpp | hqnp
        · exact (hqp ((Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hqpp)).elim
        · exact hqnp
    simp [smallPrimeSupport, hqS, hqp, hdiv]
  · simp [smallPrimeSupport, hqS]

theorem smallPrimeCount_div_succ
    (S : Finset ℕ) (n p : ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hpS : p ∈ S) (hpn : p ∣ n)
    (hsquare : ¬ p^2 ∣ n) :
    smallPrimeCount S (n/p) + 1 = smallPrimeCount S n := by
  classical
  unfold smallPrimeCount
  rw [smallPrimeSupport_div S n p hprime hpS hpn hsquare]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hpS, hpn⟩)

theorem descFactorial_peel (u t : ℕ) :
    u * (u-1).descFactorial t = u.descFactorial (t+1) := by
  cases u with
  | zero => simp
  | succ u => simpa using (Nat.succ_descFactorial_succ u t).symm

theorem smallMarkFactorialPeel
    (S : Finset ℕ) (n t : ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n) :
    (∑ p ∈ smallPrimeSupport S n,
         (smallPrimeCount S (n/p)).descFactorial t) =
    (smallPrimeCount S n).descFactorial (t+1) := by
  classical
  have hcount (p : ℕ) (hp : p ∈ smallPrimeSupport S n) :
      smallPrimeCount S (n/p) = smallPrimeCount S n - 1 := by
    obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
    have hh := smallPrimeCount_div_succ S n p hprime hpS hpn (hsquare p hpS)
    omega
  calc
    _ = ∑ p ∈ smallPrimeSupport S n,
        (smallPrimeCount S n - 1).descFactorial t := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hcount p hp]
    _ = smallPrimeCount S n * (smallPrimeCount S n - 1).descFactorial t := by
      simp [smallPrimeCount]
    _ = _ := descFactorial_peel _ _

end Green64Analytic.CorrelationD

end

/-! ## code.PeelingErrorCap -/

section

set_option maxHeartbeats 0
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

noncomputable def sourcePeelingError (S : Finset ℕ) (V : ℝ)
    (W_hi W_lo : ℕ → ℂ) (n : ℕ) : ℂ :=
  W_hi n - ((1/V:ℝ):ℂ) *
    ∑ p ∈ smallPrimeSupport S n, W_lo (n/p)

/-- Even on square-divisible inputs, the peeling expression is controlled
    by *two bounded* source marked weights and the true prime divisor count. -/
theorem peeling_error_norm_card_bound
    (S : Finset ℕ) (n : ℕ) (V B : ℝ)
    (W_hi W_lo : ℕ → ℂ)
    (hV : 0 < V) (hB : 0 ≤ B)
    (hhi : ‖W_hi n‖ ≤ B)
    (hlo : ∀ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ ≤ B) :
    ‖sourcePeelingError S V W_hi W_lo n‖ ≤
      B * (1 + ((smallPrimeSupport S n).card : ℝ)/V) := by
  have hsum : ‖∑ p ∈ smallPrimeSupport S n, W_lo (n/p)‖ ≤
      ((smallPrimeSupport S n).card : ℝ)*B := by
    calc
      _ ≤ ∑ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ smallPrimeSupport S n, B :=
        Finset.sum_le_sum (fun p hp => hlo p hp)
      _ = ((smallPrimeSupport S n).card : ℝ)*B := by simp [mul_comm]
  have hscalar : ‖((1/V:ℝ):ℂ)‖ = 1/V := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (one_div_pos.mpr hV)
  have hsumNonneg : 0 ≤ 1/V := le_of_lt (one_div_pos.mpr hV)
  unfold sourcePeelingError
  calc
    _ ≤ ‖W_hi n‖ + ‖((1/V:ℝ):ℂ) *
       (∑ p ∈ smallPrimeSupport S n, W_lo (n/p))‖ :=
      norm_sub_le _ _
    _ = ‖W_hi n‖ + (1/V) *
      ‖∑ p ∈ smallPrimeSupport S n, W_lo (n/p)‖ := by
        rw [norm_mul, hscalar]
    _ ≤ B + (1/V)*(((smallPrimeSupport S n).card:ℝ)*B) :=
      add_le_add hhi (mul_le_mul_of_nonneg_left hsum hsumNonneg)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.PeelingErrorLogCap -/

section

set_option maxHeartbeats 0
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- A logarithmic bound for the number of selected prime divisors,
    with no cardinality penalty proportional to the dyadic P. -/
theorem smallPrimeSupport_card_scale (S : Finset ℕ)
    (n N : ℕ) (L D vmin V : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hVmin : 0 < vmin) (hV : vmin ≤ V)
    (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hlogN : Real.log (N:ℝ) ≤ D*L) :
    ((smallPrimeSupport S n).card : ℝ)/V ≤
      D*L/(vmin*Real.log 2) := by
  have hvpos : 0 < V := lt_of_lt_of_le hVmin hV
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlogn : Real.log (n:ℝ) ≤ Real.log (N:ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN)
  have hnpos : 0 < n := by omega
  have hcount := smallPrimeSupport_card_log_le S n hnpos hS
  have hcard : ((smallPrimeSupport S n).card:ℝ) ≤ D*L/Real.log 2 :=
    (le_div_iff₀ hlog2).2
      (hcount.trans (hlogn.trans hlogN))
  calc
    _ ≤ ((smallPrimeSupport S n).card:ℝ)/vmin :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hVmin hV
    _ ≤ (D*L/Real.log 2)/vmin :=
      div_le_div_of_nonneg_right hcard (le_of_lt hVmin)
    _ = D*L/(vmin*Real.log 2) := by ring

/-- Pointwise log-power bound for the entire peeling *difference*,
    valid also on p²-divisible inputs where the exact equality fails. -/
theorem peeling_error_log_power
    (S : Finset ℕ) (n N : ℕ)
    (V vmin B L D : ℝ) (W_hi W_lo : ℕ → ℂ)
    (hS : ∀ p ∈ S, p.Prime)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hv : 0 < vmin) (hV : vmin ≤ V)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hlogN : Real.log (N:ℝ) ≤ D*L)
    (hB : 0 ≤ B) (hhi : ‖W_hi n‖ ≤ B)
    (hlo : ∀ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ ≤ B) :
    ‖sourcePeelingError S V W_hi W_lo n‖ ≤
       B*L*(1+D/(vmin*Real.log 2)) := by
  have hfrac := smallPrimeSupport_card_scale S n N L D vmin V
    hS hn hnN hv hV hD hL hlogN
  have hL1 : 0 ≤ L-1 := by linarith
  have hK0 : 0 ≤ D/(vmin*Real.log 2) := by
    positivity
  have hline : 1+((smallPrimeSupport S n).card:ℝ)/V ≤
      L*(1+D/(vmin*Real.log 2)) := by
    have htmp : D*L/(vmin*Real.log 2) =
        L*(D/(vmin*Real.log 2)) := by ring
    rw [htmp] at hfrac
    nlinarith [hfrac, mul_nonneg hL1 hK0]
  calc
    _ ≤ B*(1+((smallPrimeSupport S n).card:ℝ)/V) :=
      peeling_error_norm_card_bound S n V B W_hi W_lo
         (lt_of_lt_of_le hv hV) hB hhi hlo
    _ ≤ B*(L*(1+D/(vmin*Real.log 2))) :=
      mul_le_mul_of_nonneg_left hline hB
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## code.SmallMarkWeight -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

noncomputable def smallMarkKernel (S : Finset ℕ)
    (q0 : ℝ) (t n : ℕ) : ℝ :=
  q0 ^ ((smallPrimeCount S n : ℤ) - (t : ℤ)) *
   (smallPrimeCount S n).descFactorial t

theorem smallMarkExponentDiv
    (S : Finset ℕ) (n p t : ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hpS : p ∈ S) (hpn : p ∣ n)
    (hsquare : ¬ p^2 ∣ n) :
    ((smallPrimeCount S (n/p) : ℤ) - (t:ℤ)) =
      ((smallPrimeCount S n : ℤ) - ((t+1:ℕ):ℤ)) := by
  have hh := smallPrimeCount_div_succ S n p hprime hpS hpn hsquare
  omega

theorem smallMarkKernelPeel
    (S : Finset ℕ) (n t : ℕ) (q0 : ℝ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n) :
    (∑ p ∈ smallPrimeSupport S n, smallMarkKernel S q0 t (n/p)) =
      smallMarkKernel S q0 (t+1) n := by
  classical
  let z : ℝ := q0 ^ ((smallPrimeCount S n : ℤ) - ((t+1:ℕ):ℤ))
  have hfactor : (∑ p ∈ smallPrimeSupport S n,
    ((smallPrimeCount S (n/p)).descFactorial t : ℝ)) =
       ((smallPrimeCount S n).descFactorial (t+1) : ℝ) := by
    exact_mod_cast smallMarkFactorialPeel S n t hprime hsquare
  calc
    _ = ∑ p ∈ smallPrimeSupport S n,
        z * ((smallPrimeCount S (n/p)).descFactorial t : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpS,hpn⟩ := Finset.mem_filter.mp hp
      dsimp [smallMarkKernel, z]
      rw [smallMarkExponentDiv S n p t hprime hpS hpn (hsquare p hpS)]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = z * ∑ p ∈ smallPrimeSupport S n,
        ((smallPrimeCount S (n/p)).descFactorial t : ℝ) := by
      rw [Finset.mul_sum]
    _ = z * ((smallPrimeCount S n).descFactorial (t+1) : ℝ) := by rw [hfactor]
    _ = _ := rfl

noncomputable def smallMarkedWeight (S : Finset ℕ)
    (q0 V : ℝ) (t n : ℕ) : ℝ :=
  smallMarkKernel S q0 t n / V^t

theorem smallMarkedWeightPeel (S : Finset ℕ) (n t : ℕ)
    (q0 V : ℝ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n) :
    smallMarkedWeight S q0 V (t+1) n =
    (1/V) * (∑ p ∈ smallPrimeSupport S n,
                smallMarkedWeight S q0 V t (n/p)) := by
  unfold smallMarkedWeight
  rw [← smallMarkKernelPeel S n t q0 hprime hsquare]
  rw [pow_succ, ← Finset.sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

noncomputable def decoratedSmallWeight (S : Finset ℕ) (q0 V : ℝ)
    (D : ℕ → ℂ) (t n : ℕ) : ℂ :=
  (smallMarkedWeight S q0 V t n : ℂ) * D n

theorem decoratedSmallWeightPeel
    (S : Finset ℕ) (n t : ℕ) (q0 V : ℝ)
    (D : ℕ → ℂ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n)
    (hD : ∀ p ∈ smallPrimeSupport S n, D (n/p) = D n) :
    decoratedSmallWeight S q0 V D (t+1) n =
    ((1/V:ℝ):ℂ) *
      (∑ p ∈ smallPrimeSupport S n,
          decoratedSmallWeight S q0 V D t (n/p)) := by
  have hs := smallMarkedWeightPeel S n t q0 V hprime hsquare
  have hsC := congrArg (fun x : ℝ => (x:ℂ)) hs
  push_cast at hsC
  unfold decoratedSmallWeight
  rw [hsC]
  rw [mul_assoc, Finset.sum_mul]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [hD p hp]

end Green64Analytic.CorrelationD

end

/-! ## code.OtherMarkInvariance -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Removing p from n does not alter a disjoint prime group's support. -/
theorem disjointPrimeSupport_div
    (T : Finset ℕ) (n p : ℕ)
    (hprime : ∀ q ∈ T, q.Prime) (hpPrime : p.Prime)
    (hpNot : p ∉ T) (hpn : p ∣ n) :
    smallPrimeSupport T (n/p) = smallPrimeSupport T n := by
  classical
  have hmul : p * (n/p) = n := Nat.mul_div_cancel' hpn
  ext q
  by_cases hqT : q ∈ T
  · have hqPrime := hprime q hqT
    have hneq : q ≠ p := by
      intro he
      apply hpNot
      exact he ▸ hqT
    have hd : q ∣ n/p ↔ q ∣ n := by
      constructor
      · intro h
        rw [← hmul]
        exact dvd_mul_of_dvd_right h p
      · intro h
        rw [← hmul] at h
        rcases hqPrime.dvd_mul.mp h with hqp | hqr
        · exact (hneq ((Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hqp)).elim
        · exact hqr
    simp [smallPrimeSupport, hqT, hd]
  · simp [smallPrimeSupport, hqT]
theorem disjointPrimeCount_div
    (T : Finset ℕ) (n p : ℕ)
    (hprime : ∀ q ∈ T, q.Prime) (hpPrime : p.Prime)
    (hpNot : p ∉ T) (hpn : p ∣ n) :
    smallPrimeCount T (n/p) = smallPrimeCount T n := by
  unfold smallPrimeCount
  rw [disjointPrimeSupport_div T n p hprime hpPrime hpNot hpn]

theorem disjointMarkedWeight_div
    (T : Finset ℕ) (n p t : ℕ) (q0 V : ℝ)
    (hprime : ∀ q ∈ T, q.Prime) (hpPrime : p.Prime)
    (hpNot : p ∉ T) (hpn : p ∣ n) :
    smallMarkedWeight T q0 V t (n/p) = smallMarkedWeight T q0 V t n := by
  unfold smallMarkedWeight smallMarkKernel
  rw [disjointPrimeCount_div T n p hprime hpPrime hpNot hpn]
end Green64Analytic.CorrelationD

end

/-! ## code.OtherGroupsPeeling -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Product of the other groups' exact q0-damped normalized marked weights. -/
noncomputable def otherGroupWeight {ι : Type} [DecidableEq ι]
    (I : Finset ι) (T : ι → Finset ℕ)
    (q0 : ℝ) (V : ι → ℝ) (t : ι → ℕ) (n : ℕ) : ℂ :=
  ∏ g ∈ I, (smallMarkedWeight (T g) q0 (V g) (t g) n : ℂ)

theorem otherGroupWeight_div {ι : Type} [DecidableEq ι]
    (I : Finset ι) (T : ι → Finset ℕ)
    (q0 : ℝ) (V : ι → ℝ) (t : ι → ℕ)
    (S : Finset ℕ) (n p : ℕ)
    (hS : ∀ q ∈ S, q.Prime)
    (hT : ∀ g ∈ I, ∀ q ∈ T g, q.Prime)
    (hDisj : ∀ g ∈ I, ∀ q ∈ S, q ∉ T g)
    (hpS : p ∈ S) (hpn : p ∣ n) :
    otherGroupWeight I T q0 V t (n/p) =
    otherGroupWeight I T q0 V t n := by
  unfold otherGroupWeight
  apply Finset.prod_congr rfl
  intro g hg
  exact congrArg (fun u : ℝ => (u:ℂ))
    (disjointMarkedWeight_div (T g) n p (t g) q0 (V g)
       (hT g hg) (hS p hpS) (hDisj g hg p hpS) hpn)

/-- The full finite product, with one peeled small group and all other groups. -/
noncomputable def oneGroupInFullWeight {ι : Type} [DecidableEq ι]
    (S : Finset ℕ) (I : Finset ι) (T : ι → Finset ℕ)
    (q0 Vsmall : ℝ) (V : ι → ℝ) (t : ι → ℕ)
    (E : ℕ → ℂ) (k n : ℕ) : ℂ :=
  (smallMarkedWeight S q0 Vsmall k n : ℂ) *
  (otherGroupWeight I T q0 V t n * E n)

theorem oneGroupInFullWeight_peel {ι : Type} [DecidableEq ι]
    (S : Finset ℕ) (I : Finset ι) (T : ι → Finset ℕ)
    (q0 Vsmall : ℝ) (V : ι → ℝ) (t : ι → ℕ)
    (E : ℕ → ℂ) (k n : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ g ∈ I, ∀ p ∈ T g, p.Prime)
    (hDisj : ∀ g ∈ I, ∀ p ∈ S, p ∉ T g)
    (hsquare : ∀ p ∈ S, ¬ p^2 ∣ n)
    (hE : ∀ p ∈ smallPrimeSupport S n, E (n/p) = E n) :
    oneGroupInFullWeight S I T q0 Vsmall V t E (k+1) n =
    ((1/Vsmall : ℝ):ℂ) *
      (∑ p ∈ smallPrimeSupport S n,
        oneGroupInFullWeight S I T q0 Vsmall V t E k (n/p)) := by
  let D : ℕ → ℂ := fun z => otherGroupWeight I T q0 V t z * E z
  have hD : ∀ p ∈ smallPrimeSupport S n, D (n/p) = D n := by
    intro p hp
    obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
    dsimp [D]
    rw [otherGroupWeight_div I T q0 V t S n p hS hT hDisj hpS hpn,
        hE p hp]
  simpa only [oneGroupInFullWeight, decoratedSmallWeight, D] using
    (decoratedSmallWeightPeel S n k q0 Vsmall D hS hsquare hD)
end Green64Analytic.CorrelationD

end

/-! ## code.BigMarkLists -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators

namespace Green64Analytic.CorrelationD

/-- All ordered injective marks in a single big prime group. -/
noncomputable def orderedBigMarks (T : Finset ℕ) (k n : ℕ) :
    Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin k => smallPrimeSupport T n))
    |>.filter Function.Injective

theorem orderedBigMarks_div
    (T : Finset ℕ) (k n p : ℕ)
    (hT : ∀ q ∈ T, q.Prime) (hp : p.Prime)
    (hpNot : p ∉ T) (hpn : p ∣ n) :
    orderedBigMarks T k (n/p) = orderedBigMarks T k n := by
  classical
  unfold orderedBigMarks
  rw [disjointPrimeSupport_div T n p hT hp hpNot hpn]

/-- A family of ordered marked lists, one list per big group. -/
noncomputable def bigMarkLists {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ) (n : ℕ) :
    Finset (∀ g : β, Fin (t g) → ℕ) := by
  classical
  exact Fintype.piFinset (fun g => orderedBigMarks (T g) (t g) n)

theorem bigMarkLists_div {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hT : ∀ g : β, ∀ q ∈ T g, q.Prime)
    (hdisj : ∀ g : β, p ∉ T g) :
    bigMarkLists T t (n/p) = bigMarkLists T t n := by
  classical
  unfold bigMarkLists
  congr 1
  funext g
  exact orderedBigMarks_div (T g) (t g) n p (hT g) hp (hdisj g) hpn
end Green64Analytic.CorrelationD

end

/-! ## code.BigMarkDecoration -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Source q₀ damping and V_g^{-t_g} for all big groups, with no factorial
    duplicating the literal ordered-list sum. -/
noncomputable def bigMarkPrefactor {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ) (q0 : ℝ)
    (V : β → ℝ) (n : ℕ) : ℂ :=
  ∏ g : β, ((q0 ^ ((smallPrimeCount (T g) n : ℤ) - (t g : ℤ)) /
       (V g)^(t g) : ℝ) : ℂ)

noncomputable def actualBigMarkDecoration {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (q0 : ℝ) (V : β → ℝ)
    (b : (∀ g : β, Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  bigMarkPrefactor T t q0 V n *
    ∑ lists ∈ bigMarkLists T t n, b lists

theorem bigMarkPrefactor_div {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (q0 : ℝ) (V : β → ℝ) (n p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n)
    (hT : ∀ g : β, ∀ q ∈ T g, q.Prime)
    (hdisj : ∀ g : β, p ∉ T g) :
    bigMarkPrefactor T t q0 V (n/p) =
      bigMarkPrefactor T t q0 V n := by
  classical
  unfold bigMarkPrefactor
  apply Finset.prod_congr rfl
  intro g hg
  rw [disjointPrimeCount_div (T g) n p (hT g) hp (hdisj g) hpn]

theorem actualBigMarkDecoration_div {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ)
    (q0 : ℝ) (V : β → ℝ)
    (b : (∀ g : β, Fin (t g) → ℕ) → ℂ) (n p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n)
    (hT : ∀ g : β, ∀ q ∈ T g, q.Prime)
    (hdisj : ∀ g : β, p ∉ T g) :
    actualBigMarkDecoration T t q0 V b (n/p) =
      actualBigMarkDecoration T t q0 V b n := by
  unfold actualBigMarkDecoration
  rw [bigMarkPrefactor_div T t q0 V n p hp hpn hT hdisj,
    bigMarkLists_div T t n p hp hpn hT hdisj]
end Green64Analytic.CorrelationD

end

/-! ## code.MarkedListCount -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Ordered prime-mark lists are precisely embeddings of slots into the
    finite prime-divisor support, including empty and overfull lists. -/
noncomputable def orderedBigMarksEquiv
    (S : Finset ℕ) (k n : ℕ) :
    (↑(orderedBigMarks S k n)) ≃
      (Fin k ↪ (↑(smallPrimeSupport S n))) := by
  classical
  refine {
    toFun := fun f => {
      toFun := fun i => ⟨f.1 i,
        (Fintype.mem_piFinset.mp (Finset.mem_filter.mp f.2).1) i⟩
      inj' := fun i j h =>
        (Finset.mem_filter.mp f.2).2 (congrArg Subtype.val h)
    }
    invFun := fun e => ⟨fun i => (e i).val,
      Finset.mem_filter.mpr ⟨
        Fintype.mem_piFinset.mpr (fun i => (e i).property),
        fun i j h => e.injective (Subtype.ext h)⟩⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro e
      apply Function.Embedding.ext
      intro i
      apply Subtype.ext
      rfl
  }

theorem orderedBigMarks_card (S : Finset ℕ) (k n : ℕ) :
    (orderedBigMarks S k n).card =
      (smallPrimeCount S n).descFactorial k := by
  classical
  let e := orderedBigMarksEquiv S k n
  calc
    _ = Fintype.card (↑(orderedBigMarks S k n)) := by simp
    _ = Fintype.card (Fin k ↪ (↑(smallPrimeSupport S n))) := Fintype.card_congr e
    _ = _ := by
      simp [smallPrimeCount, Fintype.card_embedding_eq]

theorem bigMarkLists_card {β : Type} [Fintype β] [DecidableEq β]
    (T : β → Finset ℕ) (t : β → ℕ) (n : ℕ) :
    (bigMarkLists T t n).card =
      ∏ g : β, (smallPrimeCount (T g) n).descFactorial (t g) := by
  classical
  simp [bigMarkLists, Fintype.card_piFinset, orderedBigMarks_card]
end Green64Analytic.CorrelationD

end

