module

public import Green64.Library.Weights.Part035
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Weights.Part032
public import Green64.Library.Weights.Part033
public import Green64.Library.Analysis.Estimates.Part006
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Analysis.Estimates.Part003
public import Mathlib

@[expose] public section

/-!
# Weights / Part036

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD26CollarGeometry -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.SourceSimplexGeometry

/-- The affine sum hyperplane in positive dimension is Lebesgue-null. -/
theorem sourceD26_sum_hyperplane_null (n : ℕ) (c : ℝ) :
    (volume : Measure (Fin (n+1) → ℝ)) {x | (∑ j, x j) = c} = 0 := by
  let i : Fin (n+1) := 0
  let S : Set ((Fin n → ℝ) × ℝ) := {z | z.2 = c - ∑ j : Fin n, z.1 j}
  have hs : MeasurableSet S := by
    dsimp [S]
    measurability
  have hfiber (r : Fin n → ℝ) :
      (volume : Measure ℝ) (Prod.mk r ⁻¹' S) = 0 := by
    have hsub : Prod.mk r ⁻¹' S ⊆ {c - ∑ j : Fin n, r j} := by
      intro a ha
      exact ha
    exact MeasureTheory.measure_mono_null hsub (by simp)
  have hprod :
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) S = 0 :=
    MeasureTheory.Measure.measure_prod_null_of_ae_null hs
      (Filter.Eventually.of_forall hfiber)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  let F : (Fin (n+1) → ℝ) → ((Fin n → ℝ) × ℝ) :=
    fun x => ((e x).2,(e x).1)
  have he := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n+1) => ℝ) i
  have hswap := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
  have hF := hswap.comp he
  have hpre : (volume : Measure (Fin (n+1) → ℝ)) (F ⁻¹' S) = 0 := by
    have hmap : F = Prod.swap ∘ (⇑e) := by
      funext x
      rfl
    rw [hmap,hF.measure_preimage hs.nullMeasurableSet]
    exact hprod
  have heq : F ⁻¹' S = {x : Fin (n+1) → ℝ | (∑ j, x j)=c} := by
    ext x
    change x i = c - ∑ j : Fin n, x (i.succAbove j) ↔ (∑ j, x j)=c
    rw [Fin.sum_univ_succAbove (fun j => x j) i]
    constructor <;> intro hx <;> linarith
  rw [←heq]
  exact hpre

noncomputable def sourceD26Collar (d : ℕ) (b w δ : ℝ) : Set (Fin d → ℝ) :=
  sourceRegion d b w \ sourceRegion d b (w-δ)

lemma sourceD26_collar_measurable (d : ℕ) (b w δ : ℝ) :
    MeasurableSet (sourceD26Collar d b w δ) :=
  (sourceRegion_closed d b w).measurableSet.diff
    (sourceRegion_closed d b (w-δ)).measurableSet

lemma sourceD26_collar_antitone (d : ℕ) (b w : ℝ) :
    Antitone (fun n : ℕ => sourceD26Collar d b w (1/(n+1:ℝ))) := by
  intro n m hnm x hx
  rcases hx with ⟨hout,hin⟩
  refine ⟨hout,?_⟩
  intro hmIn
  apply hin
  refine ⟨hmIn.1,?_⟩
  have hnpos : 0<(n+1:ℝ) := by positivity
  have hden : (n+1:ℝ)≤(m+1:ℝ) := by exact_mod_cast Nat.succ_le_succ hnm
  have hδ : 1/(m+1:ℝ)≤1/(n+1:ℝ) :=
    one_div_le_one_div_of_le hnpos hden
  dsimp only [sourceRegion] at hmIn ⊢
  linarith [hmIn.2,hδ]

lemma sourceD26_iInter_collar_subset_boundary (n : ℕ) (b w : ℝ) :
    (⋂ m : ℕ, sourceD26Collar (n+1) b w (1/(m+1:ℝ))) ⊆
      {x : Fin (n+1) → ℝ | (∑ j, x j)=w-b} := by
  intro x hx
  have h0 := Set.mem_iInter.mp hx 0
  have hout := h0.1
  have hle : (∑ j, x j)≤w-b := hout.2
  have hge : w-b≤∑ j, x j := by
    by_contra hbad
    let gap : ℝ := (w-b) - ∑ j, x j
    have hgap : 0 < gap := by dsimp [gap]; exact sub_pos.mpr (lt_of_not_ge hbad)
    obtain ⟨N,hN⟩ := exists_nat_gt (1/gap)
    have hNpos : 0<(N+1:ℝ) := by positivity
    have hinv : 1/(N+1:ℝ)<gap := by
      apply (div_lt_iff₀ hNpos).mpr
      have hNN : (1/gap)<(N:ℝ) := hN
      have hgp : 0<gap := hgap
      have := (div_lt_iff₀ hgp).mp hNN
      nlinarith
    have hNcoll := Set.mem_iInter.mp hx N
    apply hNcoll.2
    refine ⟨hout.1,?_⟩
    dsimp [gap] at hinv
    linarith
  exact le_antisymm hle hge

theorem sourceD26_collar_measure_tendsto_zero
    (n : ℕ) (b w : ℝ) (hb : 0<b) :
    Tendsto (fun m : ℕ =>
      (volume : Measure (Fin (n+1) → ℝ))
        (sourceD26Collar (n+1) b w (1/(m+1:ℝ))))
      atTop (𝓝 0) := by
  let s : ℕ → Set (Fin (n+1) → ℝ) :=
    fun m => sourceD26Collar (n+1) b w (1/(m+1:ℝ))
  have hs : ∀ m, NullMeasurableSet (s m) volume :=
    fun m => (sourceD26_collar_measurable (n+1) b w _).nullMeasurableSet
  have hm : Antitone s := sourceD26_collar_antitone (n+1) b w
  have hfin : ∃ m, (volume : Measure (Fin (n+1) → ℝ)) (s m) ≠ ⊤ := by
    refine ⟨0,?_⟩
    have hsub : s 0 ⊆ sourceRegion (n+1) b w := fun x hx => hx.1
    exact ne_of_lt ((measure_mono hsub).trans_lt
      (sourceRegion_compact (n+1) b w hb.le).measure_lt_top)
  have ht := tendsto_measure_iInter_atTop hs hm hfin
  have hinter : (volume : Measure (Fin (n+1) → ℝ)) (⋂ m, s m)=0 := by
    apply measure_mono_null
      (sourceD26_iInter_collar_subset_boundary n b w)
      (sourceD26_sum_hyperplane_null n (w-b))
  change Tendsto ((volume : Measure (Fin (n+1) → ℝ)) ∘
    fun m : ℕ => sourceD26Collar (n+1) b w (1/(m+1:ℝ))) atTop (𝓝 0)
  simpa only [s,hinter] using ht

theorem sourceD26_collar_reciprocal_integral_tendsto_zero
    (n : ℕ) (b w : ℝ) (hb : 0<b) :
    Tendsto (fun m : ℕ =>
      ∫ t in sourceD26Collar (n+1) b w (1/(m+1:ℝ)),
        reciprocalProduct (n+1) t)
      atTop (𝓝 0) := by
  have hint : Integrable (fun t : Fin (n+1) → ℝ =>
      Set.indicator (sourceRegion (n+1) b w)
        (reciprocalProduct (n+1)) t) := by
    exact (reciprocalProduct_integrableOn_source (n+1) b w hb).integrable_indicator
      (sourceRegion_closed (n+1) b w).measurableSet
  have hs := sourceD26_collar_measure_tendsto_zero n b w hb
  have hsub (m : ℕ) :
      (∫ t in sourceD26Collar (n+1) b w (1/(m+1:ℝ)),
        reciprocalProduct (n+1) t) =
      ∫ t in sourceD26Collar (n+1) b w (1/(m+1:ℝ)),
        Set.indicator (sourceRegion (n+1) b w)
          (reciprocalProduct (n+1)) t := by
    apply setIntegral_congr_fun
      (sourceD26_collar_measurable (n+1) b w _)
    intro t ht
    simp [Set.indicator_of_mem ht.1]
  have hh := hint.tendsto_setIntegral_nhds_zero hs
  simpa only [Function.comp_apply,←hsub] using hh


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26BandGeometry -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.SourceSimplexGeometry

def sourceD26BoundaryBand (d : ℕ) (b w δ : ℝ) : Set (Fin d → ℝ) :=
  {t | (∀ i, b ≤ t i) ∧ w-b-δ < (∑ i, t i) ∧ (∑ i, t i) ≤ w-b+δ}

lemma sourceD26_band_measurable (d : ℕ) (b w δ : ℝ) :
    MeasurableSet (sourceD26BoundaryBand d b w δ) := by
  unfold sourceD26BoundaryBand
  measurability

lemma sourceD26_band_antitone (d : ℕ) (b w : ℝ) :
    Antitone (fun n : ℕ => sourceD26BoundaryBand d b w (1/(n+1:ℝ))) := by
  intro n m hnm t ht
  rcases ht with ⟨hcoord,hlo,hhi⟩
  have hnpos : 0<(n+1:ℝ) := by positivity
  have hden : (n+1:ℝ)≤(m+1:ℝ) := by exact_mod_cast Nat.succ_le_succ hnm
  have hδ : 1/(m+1:ℝ)≤1/(n+1:ℝ) :=
    one_div_le_one_div_of_le hnpos hden
  exact ⟨hcoord,by linarith,by linarith⟩

lemma sourceD26_iInter_band_subset_boundary (n : ℕ) (b w : ℝ) :
    (⋂ m : ℕ, sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ))) ⊆
      {x : Fin (n+1) → ℝ | (∑ j,x j)=w-b} := by
  intro x hx
  have hall := Set.mem_iInter.mp hx
  have hle : (∑ j,x j)≤w-b := by
    by_contra hbad
    let gap : ℝ := (∑ j,x j)-(w-b)
    have hgap : 0<gap := by dsimp [gap]; exact sub_pos.mpr (lt_of_not_ge hbad)
    obtain ⟨N,hN⟩ := exists_nat_gt (1/gap)
    have hNpos : 0<(N+1:ℝ) := by positivity
    have hinv : 1/(N+1:ℝ)<gap := by
      apply (div_lt_iff₀ hNpos).mpr
      have hNN : 1/gap<(N:ℝ) := hN
      have hh := (div_lt_iff₀ hgap).mp hNN
      nlinarith
    have hNband := hall N
    dsimp [gap] at hinv
    linarith [hNband.2.2]
  have hge : w-b≤∑ j,x j := by
    by_contra hbad
    let gap : ℝ := (w-b)-(∑ j,x j)
    have hgap : 0<gap := by dsimp [gap]; exact sub_pos.mpr (lt_of_not_ge hbad)
    obtain ⟨N,hN⟩ := exists_nat_gt (1/gap)
    have hNpos : 0<(N+1:ℝ) := by positivity
    have hinv : 1/(N+1:ℝ)<gap := by
      apply (div_lt_iff₀ hNpos).mpr
      have hNN : 1/gap<(N:ℝ) := hN
      have hh := (div_lt_iff₀ hgap).mp hNN
      nlinarith
    have hNband := hall N
    dsimp [gap] at hinv
    linarith [hNband.2.1]
  exact le_antisymm hle hge

theorem sourceD26_band_measure_tendsto_zero
    (n : ℕ) (b w : ℝ) (hb : 0<b) :
    Tendsto (fun m : ℕ =>
      (volume : Measure (Fin (n+1) → ℝ))
        (sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ))))
      atTop (𝓝 0) := by
  let s : ℕ → Set (Fin (n+1) → ℝ) :=
    fun m => sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ))
  have hs : ∀ m, NullMeasurableSet (s m) volume :=
    fun m => (sourceD26_band_measurable (n+1) b w _).nullMeasurableSet
  have hm : Antitone s := sourceD26_band_antitone (n+1) b w
  have hfin : ∃ m,(volume : Measure (Fin (n+1) → ℝ)) (s m)≠⊤ := by
    refine ⟨0,?_⟩
    have hsub : s 0 ⊆ sourceRegion (n+1) b (w+1) := by
      intro t ht
      exact ⟨ht.1,by linarith [ht.2.2]⟩
    exact ne_of_lt ((measure_mono hsub).trans_lt
      (sourceRegion_compact (n+1) b (w+1) hb.le).measure_lt_top)
  have ht := tendsto_measure_iInter_atTop hs hm hfin
  have hinter : (volume : Measure (Fin (n+1) → ℝ)) (⋂ m,s m)=0 := by
    apply measure_mono_null
      (sourceD26_iInter_band_subset_boundary n b w)
      (sourceD26_sum_hyperplane_null n (w-b))
  change Tendsto ((volume : Measure (Fin (n+1) → ℝ)) ∘
    fun m : ℕ => sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ)))
    atTop (𝓝 0)
  simpa only [s,hinter] using ht

theorem sourceD26_band_reciprocal_integral_tendsto_zero
    (n : ℕ) (b w : ℝ) (hb : 0<b) :
    Tendsto (fun m : ℕ =>
      ∫ t in sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ)),
        reciprocalProduct (n+1) t)
      atTop (𝓝 0) := by
  have hint0 := reciprocalProduct_integrableOn_source (n+1) b (w+1) hb
  have hint : Integrable (Set.indicator (sourceRegion (n+1) b (w+1))
      (reciprocalProduct (n+1))) :=
    hint0.integrable_indicator (sourceRegion_closed (n+1) b (w+1)).measurableSet
  have hs := sourceD26_band_measure_tendsto_zero n b w hb
  have hsub (m : ℕ) :
      (∫ t in sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ)),
        reciprocalProduct (n+1) t) =
      ∫ t in sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ)),
        Set.indicator (sourceRegion (n+1) b (w+1))
          (reciprocalProduct (n+1)) t := by
    apply setIntegral_congr_fun (sourceD26_band_measurable (n+1) b w _)
    intro t ht
    have hδ : 1/(m+1:ℝ) ≤ 1 := by
      have hm1 : (1:ℝ) ≤ m+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      exact (one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (by norm_num)
    have hmem : t∈sourceRegion (n+1) b (w+1) :=
      ⟨ht.1,by linarith [ht.2.2,hδ]⟩
    simp [Set.indicator_of_mem hmem]
  have hh := hint.tendsto_setIntegral_nhds_zero hs
  simpa only [←hsub] using hh


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26ArithmeticBand -/

section

open Filter Topology MeasureTheory Function
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

lemma sourceD26_grid_union_measurable
    (d k : ℕ) (u v : Fin k → ℝ) (C : Finset (Fin d → Fin k)) :
    MeasurableSet (sourceGridUnion d k u v C) := by
  unfold sourceGridUnion
  apply Finset.measurableSet_biUnion
  intro c hc
  exact sourceCellSet_measurable d (fun i => u (c i)) (fun i => v (c i))

lemma sourceD26_grid_reciprocal_integral_eq
    (d k : ℕ) (b w δ : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (hb : 0<b) (hu : ∀ j,b≤u j) (huv : ∀ j,u j≤v j)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j)
    (hband : sourceGridUnion d k u v C ⊆ sourceD26BoundaryBand d b w δ) :
    (∫ t in sourceGridUnion d k u v C, reciprocalProduct d t) =
      ∑ c∈C,∏ i : Fin d,Real.log (v (c i)/u (c i)) := by
  let cell : (Fin d → Fin k) → Set (Fin d → ℝ) :=
    fun c => sourceCellSet d (fun i => u (c i)) (fun i => v (c i))
  have hmeas (c : Fin d → Fin k) (hc : c∈C) : MeasurableSet (cell c) :=
    sourceCellSet_measurable d _ _
  have hdisj : Set.Pairwise (↑C) (Disjoint on cell) := by
    intro c hc c' hc' hne
    exact sourceGridCells_disjoint d k u v hsep c c' hne
  have hBandOuter : sourceD26BoundaryBand d b w δ ⊆ sourceRegion d b (w+δ) := by
    intro t ht
    exact ⟨ht.1,by linarith [ht.2.2]⟩
  have hint (c : Fin d → Fin k) (hc : c∈C) :
      IntegrableOn (reciprocalProduct d) (cell c) := by
    have hsubCell : cell c ⊆ sourceGridUnion d k u v C := by
      intro t ht
      unfold sourceGridUnion
      apply Set.mem_iUnion.mpr
      refine ⟨c,?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨hc,ht⟩
    exact (reciprocalProduct_integrableOn_source d b (w+δ) hb).mono_set
      (hsubCell.trans (hband.trans hBandOuter))
  change (∫ t in ⋃ c∈C,cell c,reciprocalProduct d t)=_
  rw [integral_biUnion_finset C hmeas hdisj hint]
  apply Finset.sum_congr rfl
  intro c hc
  exact sourceCellSet_reciprocal_integral d
    (fun i => u (c i)) (fun i => v (c i))
    (fun i => hb.trans_le (hu (c i))) (fun i => huv (c i))

/-- Continuum reciprocal mass of a selected grid lying in a boundary band
is bounded by the band integral itself. -/
theorem sourceD26_continuum_grid_le_band
    (d k : ℕ) (b w δ : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (hb : 0<b) (hu : ∀ j,b≤u j) (huv : ∀ j,u j≤v j)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j)
    (hband : sourceGridUnion d k u v C ⊆ sourceD26BoundaryBand d b w δ) :
    (∑ c∈C,∏ i : Fin d,Real.log (v (c i)/u (c i))) ≤
      ∫ t in sourceD26BoundaryBand d b w δ,reciprocalProduct d t := by
  have hEq := sourceD26_grid_reciprocal_integral_eq d k b w δ u v C
    hb hu huv hsep hband
  rw [←hEq]
  have hbandMeas := sourceD26_band_measurable d b w δ
  have hgridMeas := sourceD26_grid_union_measurable d k u v C
  have hIntBand : IntegrableOn (reciprocalProduct d)
      (sourceD26BoundaryBand d b w δ) := by
    have hsub : sourceD26BoundaryBand d b w δ ⊆ sourceRegion d b (w+δ) := by
      intro t ht
      exact ⟨ht.1,by linarith [ht.2.2]⟩
    exact (reciprocalProduct_integrableOn_source d b (w+δ) hb).mono_set hsub
  have hnonneg :
      0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict
        (sourceD26BoundaryBand d b w δ)] reciprocalProduct d := by
    filter_upwards [ae_restrict_mem hbandMeas] with t ht
    unfold reciprocalProduct
    exact Finset.prod_nonneg (fun i hi =>
      inv_nonneg.mpr (hb.le.trans (ht.1 i)))
  exact setIntegral_mono_set hIntBand hnonneg (Filter.Eventually.of_forall hband)

/-- Actual reciprocal-prime mass on any fixed grid contained in the collar
is eventually no larger than its vanishing continuum band mass plus ε. -/
theorem sourceD26_actual_grid_le_band
    (d k : ℕ) (a M b w δ ε : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (ha : 0<a) (haM : a≤M) (hb : 0<b) (hε : 0<ε)
    (hcells : ∀ j,a≤u j ∧ u j≤v j ∧ v j≤M)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j)
    (hbu : ∀ j,b≤u j)
    (hband : sourceGridUnion d k u v C ⊆ sourceD26BoundaryBand d b w δ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ ps∈orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) C,
        ∏ i : Fin d,(ps i:ℝ)⁻¹) ≤
      (∫ t in sourceD26BoundaryBand d b w δ,reciprocalProduct d t)+ε := by
  obtain ⟨K,hK,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  have hlim := actual_ordered_prime_grid_tendsto_zero d k a M K u v
    ha haM hK hcells hsep (fun _L => C) hPNT
  have hcont := sourceD26_continuum_grid_le_band d k b w δ u v C hb
    hbu (fun j => (hcells j).2.1) hsep hband
  have hsmall : ∀ᶠ L : ℝ in atTop,
      (∑ ps∈orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) C,
        ∏ i : Fin d,(ps i:ℝ)⁻¹) -
      (∑ c∈C,∏ i : Fin d,Real.log (v (c i)/u (c i))) < ε := by
    have hh := hlim.eventually (isOpen_Iio.mem_nhds hε)
    simpa only [logCell] using hh
  filter_upwards [hsmall] with L hL
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26GridSplit -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.SourceSimplexGeometry
open Green64Analytic.ReciprocalPrimeGrid

noncomputable def sourceD26InteriorCells
    (d k : ℕ) (b h w : ℝ) : Finset (Fin d → Fin k) :=
  Finset.univ.filter (fun c =>
    (∑ i : Fin d, gridUpper b h k (c i)) ≤ w-b)

noncomputable def sourceD26BandCells
    (d k : ℕ) (b h w : ℝ) : Finset (Fin d → Fin k) :=
  Finset.univ.filter (fun c =>
    w-b < (∑ i : Fin d, gridUpper b h k (c i)) ∧
    (∑ i : Fin d, gridLower b h k (c i)) ≤ w-b+h)

lemma sourceD26_sum_upper_le_lower_add
    (d k : ℕ) (b h : ℝ) (c : Fin d → Fin k) :
    (∑ i : Fin d, gridUpper b h k (c i)) ≤
      (∑ i : Fin d, gridLower b h k (c i)) + (d:ℝ)*h := by
  calc
    _ = ∑ i : Fin d,(gridLower b h k (c i)+h) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [gridUpper_eq_lower_add]
    _ = (∑ i : Fin d,gridLower b h k (c i)) + ∑ _i : Fin d,h := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin d,gridLower b h k (c i)) + (d:ℝ)*h := by
      simp
    _ ≤ (∑ i : Fin d,gridLower b h k (c i)) + (d:ℝ)*h := le_rfl

lemma sourceD26_band_cell_subset
    (d k : ℕ) (b h w : ℝ) (hh : 0≤h)
    (c : Fin d → Fin k) (hc : c∈sourceD26BandCells d k b h w) :
    sourceCellSet d (fun i => gridLower b h k (c i))
      (fun i => gridUpper b h k (c i)) ⊆
      sourceD26BoundaryBand d b w (((d:ℝ)+1)*h) := by
  intro t ht
  obtain ⟨_,hcHi,hcLo⟩ := Finset.mem_filter.mp hc
  have hsumLow : (∑ i : Fin d,gridLower b h k (c i)) ≤
      ∑ i : Fin d,t i :=
    Finset.sum_le_sum (fun i hi => (ht i).1.le)
  have hsumHigh : (∑ i : Fin d,t i) ≤
      ∑ i : Fin d,gridUpper b h k (c i) :=
    Finset.sum_le_sum (fun i hi => (ht i).2)
  have hgap := sourceD26_sum_upper_le_lower_add d k b h c
  have hcoord : ∀ i,b≤t i := by
    intro i
    have hlu : b≤gridLower b h k (c i) := by
      dsimp [gridLower]
      have hn : (0:ℝ)≤(c i).val := Nat.cast_nonneg _
      nlinarith [mul_nonneg hn hh]
    exact hlu.trans (le_of_lt (ht i).1)
  refine ⟨hcoord,?_,?_⟩
  · linarith
  · linarith

theorem sourceD26_band_grid_union_subset
    (d k : ℕ) (b h w : ℝ) (hh : 0≤h) :
    sourceGridUnion d k
      (gridLower b h k) (gridUpper b h k)
      (sourceD26BandCells d k b h w) ⊆
      sourceD26BoundaryBand d b w (((d:ℝ)+1)*h) := by
  intro t ht
  unfold sourceGridUnion at ht
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp ht
  obtain ⟨hcC,htC⟩ := Set.mem_iUnion.mp hc
  exact sourceD26_band_cell_subset d k b h w hh c hcC htC

lemma sourceD26_interior_room
    (d k : ℕ) (b h w : ℝ)
    (c : Fin d → Fin k) (hc : c∈sourceD26InteriorCells d k b h w) :
    b≤w-∑ i : Fin d,gridUpper b h k (c i) := by
  have hh := (Finset.mem_filter.mp hc).2
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26PrefixCoverage -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

lemma sourceD26_exists_ofFn_of_length
    (d : ℕ) (l : List ℕ) (hlen : l.length=d) :
    ∃ ps : Fin d → ℕ, List.ofFn ps=l := by
  subst d
  exact ⟨l.get,List.ofFn_get l⟩

lemma sourceD26_prime_exponent_gt_cutoff
    (L b : ℝ) (hL : 0<L) (p : ℕ) (hp0 : 0<p)
    (hpb : (Real.exp L)^b < (p:ℝ)) :
    b < primeExponent L p := by
  have _ := hp0
  have hpow : (Real.exp L)^b=Real.exp (b*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  rw [hpow] at hpb
  have hlog := Real.log_lt_log (Real.exp_pos _) hpb
  rw [Real.log_exp] at hlog
  unfold primeExponent
  exact (lt_div_iff₀ hL).mpr (by simpa [mul_comm] using hlog)

lemma sourceD26_prime_exponent_le_one
    (L : ℝ) (hL : 0<L) (p : ℕ) (hp0 : 0<p)
    (hp : (p:ℝ)≤Real.exp L) :
    primeExponent L p≤1 := by
  have hlog := Real.log_le_log (by exact_mod_cast hp0) hp
  rw [Real.log_exp] at hlog
  unfold primeExponent
  exact (div_le_iff₀ hL).mpr (by simpa using hlog)

lemma sourceD26_actual_cell_of_exponent
    (L u v : ℝ) (hL : 0<L) (p : ℕ) (hp : p.Prime)
    (hlo : u<primeExponent L p) (hhi : primeExponent L p≤v) :
    p∈actualPrimeCellSet L u v := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_pos _).le).mpr
    have hlog : u*L<Real.log (p:ℝ) := by
      unfold primeExponent at hlo
      exact (lt_div_iff₀ hL).mp hlo
    have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have hexp : Real.exp (u*L)<(p:ℝ) := by
      rw [←Real.exp_log hp0]
      exact Real.exp_lt_exp.mpr hlog
    exact hexp
  · apply Nat.le_floor
    have hlog : Real.log (p:ℝ)≤v*L := by
      unfold primeExponent at hhi
      exact (div_le_iff₀ hL).mp hhi
    have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have hexp : (p:ℝ)≤Real.exp (v*L) := by
      rw [←Real.exp_log hp0]
      exact Real.exp_le_exp.mpr hlog
    exact hexp

/-- Every contributing literal ordered prefix is captured by either the
interior fixed grid or the one-cell-thick boundary band. -/
theorem sourceD26_contributing_prefix_covered
    (d k : ℕ) (S b L w : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1) (hL : 0<L) (hk : 0<k)
    (hscale : L^(-S)+w*L≤L)
    (hzeta : L^(-S-1)≤gridStep b k)
    (pre : List ℕ)
    (hpre : pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
      d ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L)))
    (hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^b) (Real.exp (w*L)/(pre.prod:ℝ)))
      ((Real.exp (L^(-S))*Real.exp (w*L))/(pre.prod:ℝ))).Nonempty) :
    pre∈sourceGridPrefixLists d k L
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26InteriorCells d k b (gridStep b k) w) ∨
    pre∈sourceGridPrefixLists d k L
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26BandCells d k b (gridStep b k) w) := by
  have _ := hS
  have _ := hb
  have hZ : 0≤Real.exp (L^(-S))*Real.exp (w*L) := by positivity
  have hinfo := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
    d ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L)) hZ pre).mp hpre
  obtain ⟨ps,hpsEq⟩ := sourceD26_exists_ofFn_of_length d pre hinfo.1
  have hpr (i : Fin d) : (ps i).Prime := by
    have hmem : ps i∈pre := by
      rw [←hpsEq]
      exact (List.mem_ofFn' ps (ps i)).mpr ⟨i,rfl⟩
    exact (hinfo.2.1 (ps i) hmem).1
  have hpbig (i : Fin d) : (Real.exp L)^b < (ps i:ℝ) := by
    have hmem : ps i∈pre := by
      rw [←hpsEq]
      exact (List.mem_ofFn' ps (ps i)).mpr ⟨i,rfl⟩
    exact (hinfo.2.1 (ps i) hmem).2
  have hprodEq : (∏ i : Fin d,(ps i:ℝ))=(pre.prod:ℝ) := by
    rw [←hpsEq,List.prod_ofFn,Nat.cast_prod]
  have hprodUpper : (pre.prod:ℝ)≤Real.exp L := by
    have hExpEq :
        Real.exp (L^(-S))*Real.exp (w*L)=Real.exp (L^(-S)+w*L) := by
      rw [←Real.exp_add]
    rw [hExpEq] at hinfo
    exact hinfo.2.2.2.trans (Real.exp_le_exp.mpr hscale)
  have hpUpper (i : Fin d) : (ps i:ℝ)≤Real.exp L := by
    have hdiv : ps i ∣ pre.prod := by
      rw [←hpsEq,List.prod_ofFn]
      exact Finset.dvd_prod_of_mem (fun j : Fin d => ps j) (Finset.mem_univ i)
    have hprepos : 0<pre.prod := hinfo.2.2.1
    have hpNat : ps i≤pre.prod := Nat.le_of_dvd hprepos hdiv
    exact (Nat.cast_le.mpr hpNat).trans hprodUpper
  let h : ℝ := gridStep b k
  have hh : 0<h := gridStep_pos b k hb1 hk
  have hscaleGrid : b+(k:ℝ)*h=1 := gridStep_scale b k hk
  have ht (i : Fin d) :
      b<primeExponent L (ps i) ∧ primeExponent L (ps i)≤1 := by
    exact ⟨sourceD26_prime_exponent_gt_cutoff L b hL (ps i) (hpr i).pos (hpbig i),
      sourceD26_prime_exponent_le_one L hL (ps i) (hpr i).pos (hpUpper i)⟩
  have hchoice (i : Fin d) :=
    grid_cover_coordinate b h (primeExponent L (ps i)) k hh
      (ht i).1 (by simpa [hscaleGrid] using (ht i).2)
  let c : Fin d→Fin k := fun i => (hchoice i).choose
  have hcell (i : Fin d) :
      gridLower b h k (c i)<primeExponent L (ps i) ∧
      primeExponent L (ps i)≤gridUpper b h k (c i) ∧
      gridUpper b h k (c i)≤primeExponent L (ps i)+h :=
    (hchoice i).choose_spec
  have hpsBox :
      ps∈orderedPrimeBox d k
        (fun j => actualPrimeCellSet L (gridLower b h k j) (gridUpper b h k j)) c := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact sourceD26_actual_cell_of_exponent L
      (gridLower b h k (c i)) (gridUpper b h k (c i))
      hL (ps i) (hpr i) (hcell i).1 (hcell i).2.1
  have hsumUpper :
      (∑ i : Fin d,gridUpper b h k (c i))≤
        (∑ i : Fin d,primeExponent L (ps i))+(d:ℝ)*h := by
    calc
      _ ≤ ∑ i : Fin d,(primeExponent L (ps i)+h) :=
        Finset.sum_le_sum (fun i hi => (hcell i).2.2)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hsumLower :
      (∑ i : Fin d,gridLower b h k (c i))≤
        ∑ i : Fin d,primeExponent L (ps i) :=
    Finset.sum_le_sum (fun i hi => (hcell i).1.le)
  have hsumExp :
      (∑ i : Fin d,primeExponent L (ps i))=Real.log (pre.prod:ℝ)/L := by
    have hhlog := sourceD25_log_product_exponents d L ps hL (fun i => (hpr i).pos)
    rw [hprodEq] at hhlog
    exact hhlog.symm
  by_cases hint : c∈sourceD26InteriorCells d k b h w
  · left
    unfold sourceGridPrefixLists
    apply Finset.mem_image.mpr
    refine ⟨ps,?_,?_⟩
    · unfold orderedPrimeGridTuples
      apply Finset.mem_biUnion.mpr
      exact ⟨c,hint,hpsBox⟩
    · exact hpsEq
  · right
    have hcHi : w-b < ∑ i : Fin d,gridUpper b h k (c i) := by
      have hnot := hint
      simp only [sourceD26InteriorCells,Finset.mem_filter,Finset.mem_univ,true_and,
        not_le] at hnot
      exact hnot
    have hQ : 0<(pre.prod:ℝ) := by exact_mod_cast hinfo.2.2.1
    have hdep := sourceD26_nonempty_window_lower_exponent
      S b L w (pre.prod:ℝ) hL hQ hne
    have hcLo : (∑ i : Fin d,gridLower b h k (c i))≤w-b+h := by
      rw [hsumExp] at hsumLower
      linarith
    have hcBand : c∈sourceD26BandCells d k b h w := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ c,hcHi,hcLo⟩
    unfold sourceGridPrefixLists
    apply Finset.mem_image.mpr
    refine ⟨ps,?_,hpsEq⟩
    unfold orderedPrimeGridTuples
    apply Finset.mem_biUnion.mpr
    exact ⟨c,hcBand,hpsBox⟩


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26PrefixSplit -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

lemma sourceD26_grid_prefix_prod_pos
    (d k : ℕ) (L : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k)) {pre : List ℕ}
    (hpre : pre∈sourceGridPrefixLists d k L u v C) :
    0 < pre.prod := by
  unfold sourceGridPrefixLists at hpre
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hpre
  rw [List.prod_ofFn]
  apply Finset.prod_pos
  intro i hi
  obtain ⟨c,hc,hbox⟩ := Finset.mem_biUnion.mp hps
  have hp : ps i∈actualPrimeCellSet L (u (c i)) (v (c i)) :=
    (Fintype.mem_piFinset.mp hbox) i
  exact (Finset.mem_filter.mp hp).2.pos

/-- Active D24 prefix mass splits between the proved interior grid and the
one-cell boundary band, with no uncovered contributing prefix. -/
theorem sourceD26_prefix_sum_split
    (d k : ℕ) (S b L w : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1) (hL : 1<L) (hk : 0<k)
    (hscale : L^(-S)+w*L≤L)
    (hzeta : L^(-S-1)≤gridStep b k)
    (hhb : gridStep b k<b) :
    (∑ pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
      d ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L)),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) ≤
    (∑ pre∈sourceGridPrefixLists d k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26InteriorCells d k b (gridStep b k) w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) +
    (∑ pre∈sourceGridPrefixLists d k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26BandCells d k b (gridStep b k) w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) := by
  let A := Green64Analytic.OrderedPrimeRough.allPrimeTuples
    d ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L))
  let I := sourceGridPrefixLists d k L
    (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
    (sourceD26InteriorCells d k b (gridStep b k) w)
  let B := sourceGridPrefixLists d k L
    (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
    (sourceD26BandCells d k b (gridStep b k) w)
  let active : List ℕ → Prop := fun pre =>
    (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^b) (Real.exp (w*L)/(pre.prod:ℝ)))
      ((Real.exp (L^(-S))*Real.exp (w*L))/(pre.prod:ℝ))).Nonempty
  let F := A.filter active
  let FI := F.filter (fun pre => pre∈I)
  let FB := F.filter (fun pre => pre∉I)
  have hFA : F ⊆ A := by
    intro pre hp
    exact (Finset.mem_filter.mp hp).1
  have hAeq :
      (∑ pre∈A,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) =
      ∑ pre∈F,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre := by
    have hzero : (∑ pre∈A \ F,
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre)=0 := by
      apply Finset.sum_eq_zero
      intro pre hp
      have hpA : pre∈A := (Finset.mem_sdiff.mp hp).1
      have hpF : pre∉F := (Finset.mem_sdiff.mp hp).2
      have hnotActive : ¬active pre := by
        intro ha
        exact hpF (Finset.mem_filter.mpr ⟨hpA,ha⟩)
      have hne : ¬(Green64Analytic.OrderedPrimeRough.primeWindow
          (max ((Real.exp L)^b) (Real.exp (w*L)/(pre.prod:ℝ)))
          ((Real.exp (L^(-S))*Real.exp (w*L))/(pre.prod:ℝ))).Nonempty := hnotActive
      rw [sourceD24PrefixKernel,ite_eq_right hne]
    have hdecomp := Finset.sum_sdiff hFA
      (f:=fun pre => sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre)
    rw [hzero,zero_add] at hdecomp
    exact hdecomp.symm
  have hsplitF :
      (∑ pre∈F,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) =
      (∑ pre∈FI,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) +
      (∑ pre∈FB,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) := by
    have hd : Disjoint FI FB := by
      apply Finset.disjoint_left.mpr
      intro pre hfi hfb
      have hi := (Finset.mem_filter.mp hfi).2
      have hni := (Finset.mem_filter.mp hfb).2
      exact hni hi
    have hu : FI∪FB=F := by
      ext pre
      simp [FI,FB]
      tauto
    rw [←Finset.sum_union hd,hu]
  have hFI : FI⊆I := by
    intro pre hp
    exact (Finset.mem_filter.mp hp).2
  have hFB : FB⊆B := by
    intro pre hp
    obtain ⟨hpF,hnotI⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA,hactive⟩ := Finset.mem_filter.mp hpF
    have hcov := sourceD26_contributing_prefix_covered d k S b L w
      hS hb hb1 (by linarith) hk hscale hzeta pre hpA hactive
    exact hcov.resolve_left hnotI
  have hnonnegI : ∀ pre∈I,
      0 ≤ sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre := by
    intro pre hp
    have hprod := sourceD26_grid_prefix_prod_pos d k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26InteriorCells d k b (gridStep b k) w) hp
    -- eventual use has bL>1; infer directly from active branch or zero branch below
    by_cases hact : active pre
    · have hQ : 0<(pre.prod:ℝ) := by exact_mod_cast hprod
      have hdep := sourceD26_nonempty_window_lower_exponent S b L w (pre.prod:ℝ)
        (by linarith) hQ hact
      rw [sourceD24PrefixKernel,ite_eq_left hact]
      have hr : 0 < w-Real.log (pre.prod:ℝ)/L := by
        have hbh : 0 < b-gridStep b k := sub_pos.mpr hhb
        nlinarith
      have hlog : 0<Real.log (Real.exp (w*L)/(pre.prod:ℝ)) := by
        have hident : Real.log (Real.exp (w*L)/(pre.prod:ℝ)) =
            L*(w-Real.log (pre.prod:ℝ)/L) := by
          rw [Real.log_div (Real.exp_pos _).ne' hQ.ne',Real.log_exp]
          field_simp [show L ≠ 0 by linarith]
        rw [hident]
        exact mul_pos (by linarith) hr
      exact inv_nonneg.mpr (mul_nonneg hQ.le hlog.le)
    · rw [sourceD24PrefixKernel,ite_eq_right hact]
  have hnonnegB : ∀ pre∈B,
      0 ≤ sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre := by
    intro pre hp
    have hprod := sourceD26_grid_prefix_prod_pos d k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26BandCells d k b (gridStep b k) w) hp
    by_cases hact : active pre
    · have hQ : 0<(pre.prod:ℝ) := by exact_mod_cast hprod
      have hdep := sourceD26_nonempty_window_lower_exponent S b L w (pre.prod:ℝ)
        (by linarith) hQ hact
      rw [sourceD24PrefixKernel,ite_eq_left hact]
      have hr : 0 < w-Real.log (pre.prod:ℝ)/L := by
        have hbh : 0 < b-gridStep b k := sub_pos.mpr hhb
        nlinarith
      have hlog : 0<Real.log (Real.exp (w*L)/(pre.prod:ℝ)) := by
        have hident : Real.log (Real.exp (w*L)/(pre.prod:ℝ)) =
            L*(w-Real.log (pre.prod:ℝ)/L) := by
          rw [Real.log_div (Real.exp_pos _).ne' hQ.ne',Real.log_exp]
          field_simp [show L ≠ 0 by linarith]
        rw [hident]
        exact mul_pos (by linarith) hr
      exact inv_nonneg.mpr (mul_nonneg hQ.le hlog.le)
    · rw [sourceD24PrefixKernel,ite_eq_right hact]
  have hIbound :
      (∑ pre∈FI,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) ≤
      ∑ pre∈I,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre :=
    Finset.sum_le_sum_of_subset_of_nonneg hFI (fun p hp hnot => hnonnegI p hp)
  have hBbound :
      (∑ pre∈FB,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) ≤
      ∑ pre∈B,sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre :=
    Finset.sum_le_sum_of_subset_of_nonneg hFB (fun p hp hnot => hnonnegB p hp)
  change (∑ pre∈A,_)≤(∑ pre∈I,_)+(∑ pre∈B,_)
  rw [hAeq,hsplitF]
  exact add_le_add hIbound hBbound

/-- The band PrefixKernel is controlled by reciprocal-prime tuple mass,
with denominator loss only from the tiny L^{-S-1} shift. -/
theorem sourceD26_band_prefix_le_reciprocal
    (d k : ℕ) (S b L w : ℝ)
    (hS : 0<S) (hb : 0<b) (hL : 0<L)
    (hzeta : L^(-S-1)≤gridStep b k)
    (hhb : gridStep b k<b) :
    L*(∑ pre∈sourceGridPrefixLists d k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26BandCells d k b (gridStep b k) w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre) ≤
    (b-gridStep b k)⁻¹ *
      (∑ ps∈orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L
          (gridLower b (gridStep b k) k j)
          (gridUpper b (gridStep b k) k j))
        (sourceD26BandCells d k b (gridStep b k) w),
        ∏ i : Fin d,(ps i:ℝ)⁻¹) := by
  have _ := hS
  have _ := hb
  unfold sourceGridPrefixLists
  rw [Finset.sum_image List.ofFn_injective.injOn,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ps hps
  obtain ⟨c,hc,hbox⟩ := Finset.mem_biUnion.mp hps
  have hp (i : Fin d) :
      ps i∈actualPrimeCellSet L
        (gridLower b (gridStep b k) k (c i))
        (gridUpper b (gridStep b k) k (c i)) :=
    (Fintype.mem_piFinset.mp hbox) i
  have hpr (i : Fin d) : 0<ps i := (Finset.mem_filter.mp (hp i)).2.pos
  have hQ : 0<((List.ofFn ps).prod:ℝ) := by
    rw [List.prod_ofFn,Nat.cast_prod]
    exact Finset.prod_pos (fun i hi => by exact_mod_cast hpr i)
  by_cases hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^b) (Real.exp (w*L)/((List.ofFn ps).prod:ℝ)))
      ((Real.exp (L^(-S))*Real.exp (w*L))/((List.ofFn ps).prod:ℝ))).Nonempty
  · have hdep := sourceD26_nonempty_window_lower_exponent
      S b L w ((List.ofFn ps).prod:ℝ) hL hQ hne
    have hsum := sourceD25_log_product_exponents d L ps hL hpr
    have hprod : ((List.ofFn ps).prod:ℝ)=
        ∏ i : Fin d,(ps i:ℝ) := by rw [List.prod_ofFn,Nat.cast_prod]
    rw [hprod] at hdep
    have hden : 0<w-∑ i : Fin d,primeExponent L (ps i) := by
      rw [←hsum]
      have hhpos : 0<b-gridStep b k := sub_pos.mpr hhb
      nlinarith
    have hpoint := sourceD25_prefix_kernel_pointwise d S b L w ps hL hpr hden
    have hinv : (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ ≤
        (b-gridStep b k)⁻¹ := by
      apply inv_anti₀ (sub_pos.mpr hhb)
      rw [←hsum]
      nlinarith
    have hprodNonneg : 0≤∏ i : Fin d,(ps i:ℝ)⁻¹ :=
      Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (by exact_mod_cast (hpr i).le))
    exact hpoint.trans (mul_le_mul_of_nonneg_right hinv hprodNonneg)
  · rw [sourceD24PrefixKernel,ite_eq_right hne,mul_zero]
    exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hhb.le))
      (Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (by exact_mod_cast (hpr i).le)))


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26BandSmall -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

lemma sourceD26_boundary_band_mono
    (d : ℕ) (b w δ₁ δ₂ : ℝ) (hδ : δ₁ ≤ δ₂) :
    sourceD26BoundaryBand d b w δ₁ ⊆ sourceD26BoundaryBand d b w δ₂ := by
  intro t ht
  exact ⟨ht.1,by linarith [ht.2.1,hδ],by linarith [ht.2.2,hδ]⟩

lemma sourceD26_grid_cells_basic
    (k : ℕ) (b : ℝ) (hb : 0<b) (hb1 : b<1) (hk : 0<k) :
    let h := gridStep b k
    ∀ j : Fin k,
      b ≤ gridLower b h k j ∧
      gridLower b h k j ≤ gridUpper b h k j ∧
      gridUpper b h k j ≤ 1 := by
  have _ := hb
  dsimp
  intro j
  have hh : 0 < gridStep b k := gridStep_pos b k hb1 hk
  constructor
  · dsimp [gridLower]
    have hn : (0:ℝ)≤(j.val:ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn hh.le]
  constructor
  · exact gridLower_le_upper b (gridStep b k) k j hh.le
  · exact gridStep_le b k hb1 hk j

/-- For each positive prefix dimension, the complete one-cell-thick
boundary-band PrefixKernel mass is arbitrarily small after choosing
one fixed sufficiently fine grid and then taking L large. -/
theorem sourceD26_exists_band_prefix_small
    (n : ℕ) (S b w ε τ : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1) (hε : 0<ε) (hτ : 0<τ) :
    ∃ k : ℕ, 0<k ∧ gridStep b k < b ∧ gridStep b k ≤ τ ∧
      ∀ᶠ L : ℝ in atTop,
        L*(∑ pre∈sourceGridPrefixLists (n+1) k L
          (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
            ((Real.exp L)^b) pre) ≤ ε := by
  let η : ℝ := ε*b/8
  have hη : 0<η := by dsimp [η]; positivity
  have hIntT := sourceD26_band_reciprocal_integral_tendsto_zero n b w hb
  have hIntEv : ∀ᶠ m : ℕ in atTop,
      (∫ t in sourceD26BoundaryBand (n+1) b w (1/(m+1:ℝ)),
        reciprocalProduct (n+1) t) < η := by
    exact hIntT.eventually (isOpen_Iio.mem_nhds hη)
  obtain ⟨m,hmInt⟩ := hIntEv.exists
  let δ0 : ℝ := 1/(m+1:ℝ)
  have hδ0 : 0<δ0 := by dsimp [δ0]; positivity
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
      gridUpper b (gridStep b k) k i ≤ gridLower b (gridStep b k) k j :=
    grid_separated b (gridStep b k) k hh.le
  have hbw' : (((n+1:ℕ):ℝ)+1)*gridStep b k ≤ δ0 := by
    have heq : ((n+1:ℕ):ℝ)+1 = (n:ℝ)+2 := by
      push_cast
      ring
    rw [heq]
    exact hbandwidth
  have hbandSmall :
      sourceGridUnion (n+1) k
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26BandCells (n+1) k b (gridStep b k) w) ⊆
      sourceD26BoundaryBand (n+1) b w δ0 := by
    exact (sourceD26_band_grid_union_subset (n+1) k b (gridStep b k) w hh.le).trans
      (sourceD26_boundary_band_mono (n+1) b w
        ((((n+1:ℕ):ℝ)+1)*gridStep b k) δ0 hbw')
  have hActual := sourceD26_actual_grid_le_band
    (n+1) k b 1 b w δ0 η
    (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
    (sourceD26BandCells (n+1) k b (gridStep b k) w)
    hb hb1.le hb hη
    (fun j => hcells j) hsep
    (fun j => (hcells j).1) hbandSmall
  have hzetaT := tendsto_rpow_neg_atTop (show 0<S+1 by linarith)
  have hzeta : ∀ᶠ L : ℝ in atTop, L^(-S-1) ≤ gridStep b k := by
    have hzraw := hzetaT.eventually (Iic_mem_nhds hh)
    filter_upwards [hzraw] with L hLz
    simpa only [show -(S+1) = -S-1 by ring] using hLz
  refine ⟨k,hk,hhb,hhτ,?_⟩
  filter_upwards [hActual,hzeta,eventually_gt_atTop (1:ℝ)] with L hact hz hL1
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
        ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) < 2*η := by
    have hi : (∫ t in sourceD26BoundaryBand (n+1) b w δ0,
      reciprocalProduct (n+1) t) < η := by simpa only [δ0] using hmInt
    linarith [hact,hi]
  have hMul := mul_le_mul_of_nonneg_right hInv hMass0
  have htarget : (2/b)*(2*η) = ε/2 := by
    dsimp [η]
    field_simp [hb.ne']
    ring
  have hlt : L*(∑ pre∈sourceGridPrefixLists (n+1) k L
      (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
      (sourceD26BandCells (n+1) k b (gridStep b k) w),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) < ε := by
    calc
      _ ≤ (b-gridStep b k)⁻¹ *
        (∑ ps∈orderedPrimeGridTuples (n+1) k
          (fun j => actualPrimeCellSet L
            (gridLower b (gridStep b k) k j)
            (gridUpper b (gridStep b k) k j))
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) := hBandPrefix
      _ ≤ (2/b) *
        (∑ ps∈orderedPrimeGridTuples (n+1) k
          (fun j => actualPrimeCellSet L
            (gridLower b (gridStep b k) k j)
            (gridUpper b (gridStep b k) k j))
          (sourceD26BandCells (n+1) k b (gridStep b k) w),
          ∏ i : Fin (n+1),(ps i:ℝ)⁻¹) := hMul
      _ < (2/b)*(2*η) := mul_lt_mul_of_pos_left hMass (div_pos (by norm_num) hb)
      _ = ε/2 := htarget
      _ < ε := by linarith
  exact hlt.le


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26FullPrefixUpper -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

/-- Complete fixed-dimensional D24 PrefixKernel upper, including the
boundary collar. Dimension is positive (n+1); the prime-only dimension
is handled separately by D22. -/
theorem sourceD26_full_prefix_to_simplex
    (n : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbw : b<w) (hw1 : w<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      L*(∑ pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (n+1) ((Real.exp L)^b)
        (Real.exp (L^(-S))*Real.exp (w*L)),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) ≤
      (∫ t in sourceRegion (n+1) b w,
        sourceKernel (n+1) w t) + ε := by
  let dR : ℝ := ∫ t in sourceRegion (n+1) b w,
    reciprocalProduct (n+1) t
  have hR0 : 0≤dR := by
    dsimp [dR]
    apply setIntegral_nonneg (sourceRegion_closed (n+1) b w).measurableSet
    intro t ht
    exact reciprocalProduct_nonneg_source (n+1) b w hb t ht
  have hD : 0<((n+1:ℕ):ℝ) := by positivity
  let τ0 : ℝ := ε*b^2/(16*((n+1:ℕ):ℝ)*(dR+1))
  have hτ0 : 0<τ0 := by
    dsimp [τ0]
    positivity
  let τ : ℝ := min (b/4) τ0
  have hτ : 0<τ := lt_min (by positivity) hτ0
  obtain ⟨k,hk,hhb,hkτ,hBandSmall⟩ :=
    sourceD26_exists_band_prefix_small n S b w (ε/4) τ
      hS hb hb1 (by positivity) hτ
  have hh : 0<gridStep b k := gridStep_pos b k hb1 hk
  have hcells := sourceD26_grid_cells_basic k b hb hb1 hk
  have hsep : ∀ i j : Fin k, i<j →
      gridUpper b (gridStep b k) k i ≤ gridLower b (gridStep b k) k j :=
    grid_separated b (gridStep b k) k hh.le
  have hwidth : ∀ j : Fin k,
      gridUpper b (gridStep b k) k j -
        gridLower b (gridStep b k) k j ≤ gridStep b k := by
    intro j
    rw [gridUpper_eq_lower_add]
    linarith
  have hroom : ∀ c∈sourceD26InteriorCells (n+1) k b (gridStep b k) w,
      b≤w-∑ i : Fin (n+1),gridUpper b (gridStep b k) k (c i) :=
    fun c hc => sourceD26_interior_room (n+1) k b (gridStep b k) w c hc
  have hInterior := sourceD25_selected_prefix_to_simplex
    (n+1) k S b b 1 w (gridStep b k) (ε/4)
    (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
    (sourceD26InteriorCells (n+1) k b (gridStep b k) w)
    hS hb hb hb1.le hh.le (by positivity)
    (fun j => hcells j) hwidth hsep hroom
  have hkτ0 : gridStep b k≤τ0 := hkτ.trans (min_le_right _ _)
  have hden : 0<16*((n+1:ℕ):ℝ)*(dR+1) := by positivity
  have hτalg : 16*((n+1:ℕ):ℝ)*(dR+1)*gridStep b k ≤ ε*b^2 := by
    have hkτ0' : gridStep b k ≤
        ε*b^2/(16*((n+1:ℕ):ℝ)*(dR+1)) := by
      simpa only [τ0] using hkτ0
    have hm := (le_div_iff₀ hden).mp hkτ0'
    nlinarith
  have hmeshNum : ((n+1:ℕ):ℝ)*gridStep b k*dR ≤ ε*b^2/16 := by
    have hR1 : dR≤dR+1 := by linarith
    have hm1 := mul_le_mul_of_nonneg_left hR1
      (mul_nonneg hD.le hh.le)
    have hm2 : ((n+1:ℕ):ℝ)*gridStep b k*(dR+1) ≤ ε*b^2/16 := by
      nlinarith [hτalg]
    exact hm1.trans hm2
  have hmesh :
      (((n+1:ℕ):ℝ)*gridStep b k/b^2)*dR ≤ ε/16 := by
    have hb2 : 0<b^2 := sq_pos_of_pos hb
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hb2).mpr
    nlinarith [hmeshNum]
  have hzetaT := tendsto_rpow_neg_atTop (show 0<S+1 by linarith)
  have hzeta : ∀ᶠ L : ℝ in atTop,
      L^(-S-1)≤gridStep b k := by
    have hzraw := hzetaT.eventually (Iic_mem_nhds hh)
    filter_upwards [hzraw] with L hLz
    simpa only [show -(S+1)=-S-1 by ring] using hLz
  have hScaleEv : ∀ᶠ L : ℝ in atTop,
      1<L ∧ L^(-S)+w*L≤L := by
    let q : ℝ := 1-w
    have hq : 0<q := sub_pos.mpr hw1
    filter_upwards [eventually_gt_atTop (max 1 (1/q))] with L hL
    have hL1 : 1<L := (le_max_left (1:ℝ) (1/q)).trans_lt hL
    have hLp : 0<L := by linarith
    have hpow : L^(-S)≤1 := by
      have hLle : 1≤L := hL1.le
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hLle (show -S≤0 by linarith)
    have hqL : 1≤q*L := by
      have hhq := mul_le_mul_of_nonneg_left
        ((le_max_right (1:ℝ) (1/q)).trans (le_of_lt hL)) hq.le
      have hcancel : q*(1/q)=1 := by simpa [one_div] using mul_inv_cancel₀ hq.ne'
      linarith
    refine ⟨hL1,?_⟩
    dsimp [q] at hqL
    linarith
  filter_upwards [hBandSmall,hInterior,hzeta,hScaleEv]
      with L hBand hInt hz hScale
  obtain ⟨hL1,hscale⟩ := hScale
  have hSplit := sourceD26_prefix_sum_split
    (n+1) k S b L w hS hb hb1 hL1 hk hscale hz hhb
  have hL0 : 0≤L := le_of_lt (by linarith : 0<L)
  have hSplitL := mul_le_mul_of_nonneg_left hSplit hL0
  rw [mul_add] at hSplitL
  have hInt' :
      L*(∑ pre∈sourceGridPrefixLists (n+1) k L
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26InteriorCells (n+1) k b (gridStep b k) w),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) ≤
      (∫ t in sourceRegion (n+1) b w,sourceKernel (n+1) w t)+
        ε/16+ε/4 := by
    have hi := hInt
    dsimp [dR] at hmesh
    nlinarith [hi,hmesh]
  calc
    _ ≤ L*(∑ pre∈sourceGridPrefixLists (n+1) k L
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26InteriorCells (n+1) k b (gridStep b k) w),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) +
      L*(∑ pre∈sourceGridPrefixLists (n+1) k L
        (gridLower b (gridStep b k) k) (gridUpper b (gridStep b k) k)
        (sourceD26BandCells (n+1) k b (gridStep b k) w),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) := hSplitL
    _ ≤ ((∫ t in sourceRegion (n+1) b w,sourceKernel (n+1) w t)+
          ε/16+ε/4) + ε/4 := add_le_add hInt' hBand
    _ ≤ (∫ t in sourceRegion (n+1) b w,sourceKernel (n+1) w t)+ε := by
      linarith [hε]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27HigherLayer -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

lemma sourceD27_simplex_nonneg (n : ℕ) (b w : ℝ) (hb : 0<b) :
    0 ≤ ∫ t in Green64Analytic.SourceSimplexGeometry.sourceRegion (n+1) b w,
      Green64Analytic.SourceSimplexGeometry.sourceKernel (n+1) w t := by
  apply setIntegral_nonneg
    (Green64Analytic.SourceSimplexGeometry.sourceRegion_closed (n+1) b w).measurableSet
  intro t ht
  exact (Green64Analytic.SourceSimplexGeometry.sourceKernel_bound (n+1) b w hb t ht).1

lemma sourceD27_budget_choice (J ε : ℝ) (hJ : 0≤J) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/4 ∧
      (1+δ)^2*(J+ε/4) ≤ J+ε := by
  let δ := min (1/4 : ℝ) (ε/(16*(J+ε+1)))
  have hd : 0<16*(J+ε+1) := by positivity
  have hdpos : 0<δ := lt_min (by norm_num) (div_pos hε hd)
  have hdquarter : δ≤1/4 := min_le_left _ _
  have hdfrac : δ≤ε/(16*(J+ε+1)) := min_le_right _ _
  have hratio : δ*(J+ε+1)≤ε/16 := by
    have hm := mul_le_mul_of_nonneg_right hdfrac (by linarith : 0≤J+ε+1)
    have heq : (ε/(16*(J+ε+1)))*(J+ε+1)=ε/16 := by
      field_simp
    linarith [hm]
  have hprod : δ*(J+ε/4)≤ε/16 := by
    have hm := mul_le_mul_of_nonneg_left
      (show J+ε/4≤J+ε+1 by linarith) hdpos.le
    linarith
  refine ⟨δ,hdpos,hdquarter,?_⟩
  have hδ2 : δ^2≤δ := by nlinarith [hdquarter,hdpos.le]
  have hExp : (1+δ)^2*(J+ε/4) ≤
      (J+ε/4)+3*δ*(J+ε/4) := by
    have hj : 0≤J+ε/4 := by positivity
    nlinarith [mul_nonneg hj (sub_nonneg.mpr hδ2)]
  linarith

/-- Each higher Ω layer of the actual full-cell numerator has its
unaltered factorial-normalized source simplex main term. -/
theorem sourceD27_higher_length_cell_upper
    (n : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hbw : b<w) (hw1 : w<1)
    (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
          (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
        ((n+2).factorial:ℝ) ≤
      (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+ε) := by
  let J : ℝ := ∫ t in Green64Analytic.SourceSimplexGeometry.sourceRegion (n+1) b w,
      Green64Analytic.SourceSimplexGeometry.sourceKernel (n+1) w t
  have hJ : 0≤J := sourceD27_simplex_nonneg n b w hb
  have hεfact : 0<ε*((n+2).factorial:ℝ) := by positivity
  let η : ℝ := ε*((n+2).factorial:ℝ)
  obtain ⟨δ,hδ,hδsmall,hbudget⟩ :=
    sourceD27_budget_choice J η hJ hεfact
  have hpnt := sourceD24_ordered_cell_prefix_kernel_upper (n+1) S b δ hS hb hδ
  have hsimplex := sourceD26_full_prefix_to_simplex n S b w (η/4)
    hS hb (by linarith) hbw hw1 (by positivity)
  have hlimit : Tendsto (fun L : ℝ => Real.exp (L^(-S))) atTop (𝓝 (1:ℝ)) := by
    have hpow : Tendsto (fun L : ℝ => L^(-S)) atTop (𝓝 (0:ℝ)) :=
      tendsto_rpow_neg_atTop hS
    simpa only [Function.comp_def,Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp hpow)
  have hexp : ∀ᶠ L : ℝ in atTop,
      Real.exp (L^(-S))≤1+δ := by
    have he := hlimit.eventually (isOpen_Iio.mem_nhds (show (1:ℝ)<1+δ by linarith))
    filter_upwards [he] with L h
    exact h.le
  filter_upwards [hpnt,hsimplex,hexp,eventually_gt_atTop (0:ℝ)]
    with L hpn hs hex hL
  let H : ℝ := (Real.exp (L^(-S))-1)*Real.exp (w*L)
  let K : ℝ := ∑ pre ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
    (n+1) ((Real.exp L)^b) (Real.exp (L^(-S))*Real.exp (w*L)),
    sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b) pre
  let A : ℝ := ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
      (L^(-S)) ((Real.exp L)^b)).card:ℝ)
  have hH : 0≤H := by
    dsimp [H]
    have hΔ : 0<L^(-S) := Real.rpow_pos_of_pos hL _
    exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp hΔ.le)) (Real.exp_pos _).le
  have hfactor : 0≤(1+δ)*Real.exp (L^(-S))*H := by positivity
  have hfirst : A≤(1+δ)*Real.exp (L^(-S))*H*K := by
    simpa only [A,K,H,mul_assoc] using hpn (Real.exp (w*L)) (Real.exp_pos _).le
  have hsecond : L*K ≤ J+η/4 := by simpa only [J,K] using hs
  have hmain : L*A ≤ H*(J+η) := by
    have hbound : (1+δ)*Real.exp (L^(-S)) ≤ (1+δ)^2 := by
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_left hex (show (0:ℝ) ≤ 1+δ by linarith [hδ])
    have hjp : 0 ≤ J+η/4 := by positivity
    calc
      L*A ≤ L*((1+δ)*Real.exp (L^(-S))*H*K) :=
        mul_le_mul_of_nonneg_left hfirst hL.le
      _ = ((1+δ)*Real.exp (L^(-S))*H)*(L*K) := by ring
      _ ≤ ((1+δ)*Real.exp (L^(-S))*H)*(J+η/4) :=
        mul_le_mul_of_nonneg_left hsecond hfactor
      _ = ((1+δ)*Real.exp (L^(-S)))*(H*(J+η/4)) := by ring
      _ ≤ (1+δ)^2*(H*(J+η/4)) :=
        mul_le_mul_of_nonneg_right hbound (mul_nonneg hH hjp)
      _ = H*((1+δ)^2*(J+η/4)) := by ring
      _ ≤ H*(J+η) :=
        mul_le_mul_of_nonneg_left hbudget hH
  have hfac : (0:ℝ)<((n+2).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos (n+2)
  have hsource : Green64Analytic.SmallB.sourceSimplexTerm n b w =
      J / ((n+2).factorial:ℝ) := rfl
  rw [hsource]
  have hA : A ≤ (H/L)*(J+η) := by
    have hbase : A ≤ H*(J+η)/L :=
      (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hmain)
    calc
      A ≤ H*(J+η)/L := hbase
      _ = (H/L)*(J+η) := by ring
  apply (div_le_iff₀ hfac).mpr
  have hrewrite : (H/L)*(J/((n+2).factorial:ℝ)+ε)*
      ((n+2).factorial:ℝ) = (H/L)*(J+η) := by
    dsimp [η]
    field_simp [hfac.ne']
  rw [hrewrite]
  exact hA


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27OrderedLayerUpper -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.SourceSimplexGeometry

/-- Two independently checked bounds compose for EVERY genuine ordered
prime tuple length at least two, with the original full-cell normalization. -/
theorem sourceD27_ordered_layer_integral_upper
    (n : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbw : b<w) (hw1 : w<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
          (L^(-S)) ((Real.exp L)^b)).card:ℝ) ≤
      (1+ε)*Real.exp (L^(-S))*
        ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L) *
        ((∫ t in sourceRegion (n+1) b w,
          sourceKernel (n+1) w t) + ε) := by
  have hpref := sourceD26_full_prefix_to_simplex n S b w ε
    hS hb hb1 hbw hw1 hε
  have htuple := sourceD24_ordered_cell_prefix_kernel_upper
    (n+1) S b ε hS hb hε
  filter_upwards [hpref,htuple,eventually_gt_atTop (1:ℝ)]
    with L hprefL htupleL hL
  have hL0 : 0<L := by linarith
  let R : ℝ := ∫ t in sourceRegion (n+1) b w, sourceKernel (n+1) w t
  have hfactor : 0≤(1+ε)*Real.exp (L^(-S))*
      (Real.exp (L^(-S))-1)*Real.exp (w*L) := by
    have hpow : 0<L^(-S) := Real.rpow_pos_of_pos hL0 _
    have he : 0≤Real.exp (L^(-S))-1 :=
      sub_nonneg.mpr (Real.one_le_exp hpow.le)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) he)
      (Real.exp_pos _).le
  have hprefix : (∑ pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
      (n+1) ((Real.exp L)^b)
      (Real.exp (L^(-S))*Real.exp (w*L)),
      sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^b) pre) ≤ (R+ε)/L := by
    exact (le_div_iff₀ hL0).mpr (by simpa only [R,mul_comm] using hprefL)
  have htimes := mul_le_mul_of_nonneg_left hprefix hfactor
  have htuple' := htupleL (Real.exp (w*L)) (Real.exp_pos _).le
  dsimp [R] at *
  calc
    _ ≤ (1+ε)*Real.exp (L^(-S))*(Real.exp (L^(-S))-1)*
      Real.exp (w*L)*
      (∑ pre∈Green64Analytic.OrderedPrimeRough.allPrimeTuples
        (n+1) ((Real.exp L)^b)
        (Real.exp (L^(-S))*Real.exp (w*L)),
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^b) pre) := htuple'
    _ ≤ (1+ε)*Real.exp (L^(-S))*
        ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L)*
          ((∫ t in sourceRegion (n+1) b w,
            sourceKernel (n+1) w t)+ε) := by
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htimes


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27FactorialLayer -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false
open Green64Analytic.SourceSimplexGeometry

/-- Preserve the exact factorial (n+2)! on each original prime-factor
length, before summing the finitely many length classes. -/
theorem sourceD27_factorial_layer_integral_upper
    (n : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbw : b<w) (hw1 : w<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
          (L^(-S)) ((Real.exp L)^b)).card:ℝ) / ((n+2).factorial:ℝ) ≤
      (1+ε)*Real.exp (L^(-S))*
        ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L) *
        (((∫ t in sourceRegion (n+1) b w,
          sourceKernel (n+1) w t) + ε) / ((n+2).factorial:ℝ)) := by
  filter_upwards [sourceD27_ordered_layer_integral_upper
    n S b w ε hS hb hb1 hbw hw1 hε] with L h
  have hf : (0:ℝ) < ((n+2).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos (n+2)
  have hh := div_le_div_of_nonneg_right h hf.le
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27TermIdentity -/

section

open MeasureTheory
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

theorem sourceD27_simplex_term_identity (n : ℕ) (b w : ℝ) :
    (∫ t in Green64Analytic.SourceSimplexGeometry.sourceRegion (n+1) b w,
      Green64Analytic.SourceSimplexGeometry.sourceKernel (n+1) w t) /
        ((n+2).factorial:ℝ) =
      Green64Analytic.SmallB.sourceSimplexTerm n b w := by
  rfl


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27FiniteLayers -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

theorem sourceD27_finite_composite_layers_upper
    (K : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hb1 : b<1)
    (hbw : b<w) (hw1 : w<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ n∈Finset.range K,
        ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
            (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
              ((n+2).factorial:ℝ)) ≤
      (1+ε)*Real.exp (L^(-S))*
        ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L) *
        (∑ n∈Finset.range K,
          (Green64Analytic.SmallB.sourceSimplexTerm n b w+
            ε/((n+2).factorial:ℝ))) := by
  have hAll : ∀ᶠ L : ℝ in atTop, ∀ n∈Finset.range K,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ) / ((n+2).factorial:ℝ) ≤
      (1+ε)*Real.exp (L^(-S))*
        ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L) *
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+
          ε/((n+2).factorial:ℝ)) := by
    rw [Filter.eventually_all_finset]
    intro n hn
    filter_upwards [sourceD27_factorial_layer_integral_upper
      n S b w ε hS hb hb1 hbw hw1 hε] with L hL
    have heq := sourceD27_simplex_term_identity n b w
    convert hL using 1
    simp only [heq,add_div]
  filter_upwards [hAll] with L hL
  calc
    _ ≤ ∑ n∈Finset.range K,
          (1+ε)*Real.exp (L^(-S))*
            ((Real.exp (L^(-S))-1)*Real.exp (w*L)/L) *
            (Green64Analytic.SmallB.sourceSimplexTerm n b w+
              ε/((n+2).factorial:ℝ)) := Finset.sum_le_sum hL
    _ = _ := by rw [←Finset.mul_sum]


end Green64Analytic.SourceBlockSieve

end

