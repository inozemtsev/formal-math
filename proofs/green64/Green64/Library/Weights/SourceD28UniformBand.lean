module

public import Green64.Library.Analysis.Estimates.Part008
public import Green64.Library.Weights.Part036
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-!
# Weights / SourceD28UniformBand

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD28UniformBand -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

private theorem finite_positive_radius
    {α : Type*} (T : Finset α) (r : α → ℝ)
    (hr : ∀ a∈T, 0< r a) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ a∈T, ρ≤ r a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a T ha ih =>
      have hrT : ∀ x∈T, 0< r x := by
        intro x hx
        exact hr x (Finset.mem_insert_of_mem hx)
      obtain ⟨ρ,hρ,hρT⟩ := ih hrT
      have hra : 0< r a := hr a (Finset.mem_insert_self a T)
      refine ⟨min ρ (r a), lt_min hρ hra,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hmem
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hρT x hmem)

/-- UNIFORM smallness of the genuine geometric collar for every
moving exponent w on a fixed compact interval, rather than only
pointwise w. Uses zero measure of all affine sum hyperplanes, finite
subcover, and positivity of the original reciprocal-product mass. -/
theorem sourceD28_uniform_band_integral_small
    (n : ℕ) (b A B ε : ℝ)
    (hb : 0<b) (hε : 0<ε) :
    ∃ ρ : ℝ, 0<ρ ∧
      ∀ w∈Set.Icc A B,
        (∫ t in sourceD26BoundaryBand (n+1) b w ρ,
          Green64Analytic.SourceSimplexGeometry.reciprocalProduct (n+1) t)
          ≤ ε := by
  let I : Set ℝ := Set.Icc A B
  have hlocal : ∀ w∈I, ∃ m : ℕ,
      (∫ t in sourceD26BoundaryBand (n+1) b w (1/((m+1:ℕ):ℝ)),
        Green64Analytic.SourceSimplexGeometry.reciprocalProduct (n+1) t)
      < ε := by
    intro w hw
    have hlim := sourceD26_band_reciprocal_integral_tendsto_zero n b w hb
    have hEv := hlim.eventually (isOpen_Iio.mem_nhds hε)
    simpa only [Nat.cast_add,Nat.cast_one] using hEv.exists
  choose m hm using hlocal
  let r : {w // w∈I} → ℝ := fun a => 1/(2*((m a.val a.property+1:ℕ):ℝ))
  have hr (a : {w // w∈I}) : 0< r a := by dsimp [r]; positivity
  let U : ∀ w, w∈I → Set ℝ := fun w hw =>
    Set.Ioo (w-r ⟨w,hw⟩) (w+r ⟨w,hw⟩)
  have hU : ∀ (w:ℝ) (hw:w∈I), U w hw ∈ 𝓝 w := by
    intro w hw
    exact Ioo_mem_nhds (by have := hr ⟨w,hw⟩; linarith)
      (by have := hr ⟨w,hw⟩; linarith)
  obtain ⟨T,hcover⟩ := isCompact_Icc.elim_nhds_subcover' U hU
  obtain ⟨ρ,hρ,hρT⟩ := finite_positive_radius T r (by
    intro a ha
    exact hr a)
  refine ⟨ρ,hρ,?_⟩
  intro w hw
  obtain ⟨a,ha,hwa⟩ := Set.mem_iUnion₂.mp (hcover hw)
  have hclose : |w-a.val| ≤ r a := by
    have hio : a.val-r a < w ∧ w < a.val+r a := hwa
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hδ : ρ+r a ≤ 1/((m a.val a.property+1:ℕ):ℝ) := by
    have hrho := hρT a ha
    have htwo : 2*r a = 1/((m a.val a.property+1:ℕ):ℝ) := by
      dsimp [r]
      field_simp
    linarith
  have hmono :
      sourceD26BoundaryBand (n+1) b w ρ ⊆
        sourceD26BoundaryBand (n+1) b a.val
          (1/((m a.val a.property+1:ℕ):ℝ)) :=
    (sourceD28_band_shift_subset (n+1) b w a.val ρ (r a) hclose).trans
      (sourceD26_boundary_band_mono (n+1) b a.val
        (ρ+r a) (1/((m a.val a.property+1:ℕ):ℝ)) hδ)
  have hmass := sourceD28_band_integral_mono
    (n+1) b w a.val ρ (1/((m a.val a.property+1:ℕ):ℝ)) hb hmono
  exact hmass.trans (hm a.val a.property).le


end Green64Analytic.SourceBlockSieve

end

