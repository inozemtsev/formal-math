module

public import Green64.Library.Sieve.Foundations.Part054
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-!
# Sieve / Foundations / FrozenDensityMesh

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FrozenDensityMesh -/

section

set_option maxHeartbeats 1600000
open Set
namespace Green64Analytic.FrozenBins

/-- The mesh is fixed by continuity data; it is independent of every later
large analytic parameter (in particular, independent of x). -/
noncomputable def affineGrid (b c : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  b + (c - b) * (i : ℝ) / (N : ℝ)

theorem affineGrid_zero (b c : ℝ) (N : ℕ) :
    affineGrid b c N 0 = b := by simp [affineGrid]

theorem affineGrid_last (b c : ℝ) (N : ℕ) (hN : 0 < N) :
    affineGrid b c N N = c := by
  have hNe : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [affineGrid, hNe]

theorem affineGrid_step (b c : ℝ) (N i : ℕ) (hN : 0 < N) :
    affineGrid b c N (i+1) - affineGrid b c N i =
      (c - b) / (N : ℝ) := by
  have hNe : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [affineGrid, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem affineGrid_mem (b c : ℝ) (N i : ℕ)
    (hbc : b < c) (hN : 0 < N) (hi : i ≤ N) :
    affineGrid b c N i ∈ Set.Icc b c := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hir : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hiNr : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hbcr : 0 ≤ c-b := sub_nonneg.mpr hbc.le
  have hlow : 0 ≤ (c-b) * (i : ℝ) / (N : ℝ) :=
    div_nonneg (mul_nonneg hbcr hir) hNr.le
  have hupp : (c-b) * (i : ℝ) / (N : ℝ) ≤ c-b := by
    apply (div_le_iff₀ hNr).2
    nlinarith [mul_le_mul_of_nonneg_left hiNr hbcr]
  simp only [affineGrid, Set.mem_Icc]
  constructor <;> linarith

/-- Finite fixed-grid domination on every bin: neither a moving mesh
nor an unproved simplex limit appears in the statement. -/
theorem exists_frozen_density_grid (F : ℝ × ℝ → ℝ)
    {b c η : ℝ} (hbc : b < c) (hη : 0 < η)
    (hF : ContinuousOn F (Set.Icc b c ×ˢ Set.Icc b c)) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i : ℕ, i ≤ N → affineGrid b c N i ∈ Set.Icc b c) ∧
      (∀ i : ℕ, i < N →
         ∀ s ∈ Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1)),
         ∀ t ∈ Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1)),
            F (affineGrid b c N i, s) ≤ F (t,t) + η) := by
  let K := Set.Icc b c ×ˢ Set.Icc b c
  have hc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ,hδ,hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hc.uniformContinuousOn_of_continuous hF) η hη
  obtain ⟨N,hNgt⟩ := exists_nat_gt ((c-b)/δ)
  have hNpos : 0 < N := by
    by_contra hn
    have hn0 : N = 0 := Nat.eq_zero_of_not_pos hn
    have hq : 0 < (c-b)/δ := div_pos (sub_pos.mpr hbc) hδ
    simp [hn0] at hNgt
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmesh : (c-b) / (N : ℝ) < δ := by
    apply (div_lt_iff₀ hNr).2
    have hh := (div_lt_iff₀ hδ).mp hNgt
    nlinarith
  refine ⟨N,hNpos,fun i hi => affineGrid_mem b c N i hbc hNpos hi,?_⟩
  intro i hi s hs t ht
  have hri := affineGrid_mem b c N i hbc hNpos (Nat.le_of_lt hi)
  have hrj' : i+1 ≤ N := Nat.succ_le_of_lt hi
  have hrj := affineGrid_mem b c N (i+1) hbc hNpos hrj'
  have hsbc : s ∈ Set.Icc b c :=
    ⟨hri.1.trans hs.1, hs.2.trans hrj.2⟩
  have htbc : t ∈ Set.Icc b c :=
    ⟨hri.1.trans ht.1, ht.2.trans hrj.2⟩
  have hp : (affineGrid b c N i, s) ∈ K := ⟨hri, hsbc⟩
  have hq : (t,t) ∈ K := ⟨htbc, htbc⟩
  have hstep := affineGrid_step b c N i hNpos
  have hd : dist (affineGrid b c N i, s) (t,t) < δ := by
    have hb : dist (affineGrid b c N i, s) (t,t) ≤
        affineGrid b c N (i+1)-affineGrid b c N i := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
      constructor
      · apply abs_le.mpr
        constructor <;> linarith [ht.1,ht.2]
      · apply abs_le.mpr
        constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    exact lt_of_le_of_lt hb (hstep.symm ▸ hmesh)
  have hh := hmod _ hp _ hq hd
  rw [Real.dist_eq] at hh
  have hle : F (affineGrid b c N i, s) - F (t,t) < η :=
    lt_of_le_of_lt (le_abs_self _) hh
  linarith

end Green64Analytic.FrozenBins



set_option maxHeartbeats 1400000
open Set
namespace Green64Analytic.FrozenBins

/-- Literal upper envelope over each frozen band, evaluated at
the band LEFT endpoint in the first density coordinate. -/
noncomputable def upperBin (F : ℝ × ℝ → ℝ)
    (b c : ℝ) (N i : ℕ) : ℝ :=
  sSup ((fun s : ℝ => F (affineGrid b c N i, s)) ''
    Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1)))

theorem upperBin_le_of_local (F : ℝ × ℝ → ℝ) (b c η : ℝ) (N i : ℕ)
    (hlocal : ∀ s ∈ Set.Icc (affineGrid b c N i)
                                  (affineGrid b c N (i+1)),
              ∀ t ∈ Set.Icc (affineGrid b c N i)
                                  (affineGrid b c N (i+1)),
                F (affineGrid b c N i, s) ≤ F (t,t) + η)
    (t : ℝ)
    (ht : t ∈ Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1))) :
    upperBin F b c N i ≤ F (t,t) + η := by
  apply csSup_le
  · exact ⟨F (affineGrid b c N i, t), ⟨t, ht, rfl⟩⟩
  · rintro y ⟨s, hs, rfl⟩
    exact hlocal s hs t ht


end Green64Analytic.FrozenBins



set_option maxHeartbeats 1800000
open Set
namespace Green64Analytic.FrozenBins

private theorem integral_const_inv (a z k : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in a..z, k * t⁻¹) = k * Real.log (z/a) := by
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hz]

private theorem diagonal_continuousOn
    (F : ℝ × ℝ → ℝ) (b c : ℝ)
    (hF : ContinuousOn F (Set.Icc b c ×ˢ Set.Icc b c)) :
    ContinuousOn (fun t : ℝ => F (t,t)) (Set.Icc b c) := by
  exact hF.comp ((continuous_id.prodMk continuous_id).continuousOn)
    (fun _ ht => ⟨ht,ht⟩)

private theorem diagonal_weight_continuousOn
    (F : ℝ × ℝ → ℝ) (b c : ℝ) (hb : 0 < b)
    (hF : ContinuousOn F (Set.Icc b c ×ˢ Set.Icc b c)) :
    ContinuousOn (fun t : ℝ => F (t,t) * t⁻¹) (Set.Icc b c) := by
  exact (diagonal_continuousOn F b c hF).mul
    (continuousOn_id.inv₀ (fun t ht => ne_of_gt (hb.trans_le ht.1)))

/-- Logarithmically weighted actual upper-bin sum, as an ordinary
finite sum of supremal source envelopes. -/
theorem frozen_upper_log_sum (F : ℝ × ℝ → ℝ) {b c η : ℝ}
    (hb : 0 < b) (hbc : b < c)
    (hF : ContinuousOn F (Set.Icc b c ×ˢ Set.Icc b c))
    (N : ℕ) (hN : 0 < N)
    (hlocal : ∀ i : ℕ, i < N →
       ∀ s ∈ Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1)),
       ∀ t ∈ Set.Icc (affineGrid b c N i) (affineGrid b c N (i+1)),
         F (affineGrid b c N i, s) ≤ F (t,t) + η) :
    (∑ i ∈ Finset.range N,
      upperBin F b c N i *
        Real.log (affineGrid b c N (i+1) / affineGrid b c N i)) ≤
    (∫ t in b..c, F (t,t) * t⁻¹) + η * Real.log (c/b) := by
  let a : ℕ → ℝ := affineGrid b c N
  have hNreal : (0:ℝ) < N := by exact_mod_cast hN
  have hwidth (i : ℕ) : a i < a (i+1) := by
    rw [← sub_pos, affineGrid_step b c N i hN]
    exact div_pos (sub_pos.mpr hbc) hNreal
  have hrange (i : ℕ) (hi : i ≤ N) : a i ∈ Set.Icc b c :=
    affineGrid_mem b c N i hbc hN hi
  have hsubset (i : ℕ) (hi : i < N) :
      Set.uIcc (a i) (a (i+1)) ⊆ Set.uIcc b c := by
    rw [uIcc_of_le (hwidth i).le, uIcc_of_le hbc.le]
    exact Icc_subset_Icc (hrange i (Nat.le_of_lt hi)).1
      (hrange (i+1) (Nat.succ_le_of_lt hi)).2
  let g : ℝ → ℝ := fun t => F (t,t)*t⁻¹
  have hg : IntervalIntegrable g MeasureTheory.volume b c :=
    (diagonal_weight_continuousOn F b c hb hF).intervalIntegrable_of_Icc hbc.le
  have hCI : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc b c) :=
    continuousOn_id.inv₀ (fun t ht => ne_of_gt (hb.trans_le ht.1))
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume b c :=
    hCI.intervalIntegrable_of_Icc hbc.le
  have hGsum :
      (∑ i ∈ Finset.range N,
        ∫ t in a i..a (i+1), g t) = ∫ t in b..c, g t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun i hi => hg.mono_set (hsubset i hi))]
    simp [a, affineGrid_zero, affineGrid_last b c N hN]
  have hlogsum :
      (∑ i ∈ Finset.range N, Real.log (a (i+1)/a i)) =
          Real.log (c/b) := by
    calc
      _ = ∑ i ∈ Finset.range N, ∫ t in a i..a (i+1), t⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hai : 0 < a i :=
          hb.trans_le (hrange i (Nat.le_of_lt (Finset.mem_range.mp hi))).1
        have haj : 0 < a (i+1) :=
          hb.trans_le (hrange (i+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).1
        exact (integral_inv_of_pos hai haj).symm
      _ = ∫ t in b..c, t⁻¹ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals
          (fun i hi => hinv.mono_set (hsubset i hi))]
        simp [a, affineGrid_zero, affineGrid_last b c N hN]
      _ = Real.log (c/b) := integral_inv_of_pos hb (hb.trans hbc)
  have hBin (i : ℕ) (hi : i < N) :
      upperBin F b c N i * Real.log (a (i+1)/a i) ≤
      (∫ t in a i..a (i+1), g t) +
          η * Real.log (a (i+1)/a i) := by
    have hai : 0 < a i := hb.trans_le (hrange i (Nat.le_of_lt hi)).1
    have haj : 0 < a (i+1) :=
      hb.trans_le (hrange (i+1) (Nat.succ_le_of_lt hi)).1
    have hgi : IntervalIntegrable g MeasureTheory.volume (a i) (a (i+1)) :=
      hg.mono_set (hsubset i hi)
    have hii : IntervalIntegrable (fun t : ℝ => t⁻¹)
        MeasureTheory.volume (a i) (a (i+1)) :=
      hinv.mono_set (hsubset i hi)
    have hp (t : ℝ) (ht : t ∈ Set.Icc (a i) (a (i+1))) :
        upperBin F b c N i * t⁻¹ ≤ g t + η*t⁻¹ := by
      have hle := upperBin_le_of_local F b c η N i
        (hlocal i hi) t ht
      have htpos : 0 ≤ t⁻¹ := inv_nonneg.mpr (hai.trans_le ht.1).le
      calc
        _ ≤ (F (t,t)+η)*t⁻¹ := mul_le_mul_of_nonneg_right hle htpos
        _ = g t + η*t⁻¹ := by dsimp [g]; ring
    calc
      upperBin F b c N i * Real.log (a (i+1)/a i) =
          ∫ t in a i..a (i+1), upperBin F b c N i * t⁻¹ :=
            (integral_const_inv (a i) (a (i+1)) (upperBin F b c N i) hai haj).symm
      _ ≤ ∫ t in a i..a (i+1), g t + η*t⁻¹ :=
        intervalIntegral.integral_mono_on (hwidth i).le
          (hii.const_mul (upperBin F b c N i))
          (hgi.add (hii.const_mul η)) hp
      _ = (∫ t in a i..a (i+1), g t) +
          η * Real.log (a (i+1)/a i) := by
        rw [intervalIntegral.integral_add hgi (hii.const_mul η),
          integral_const_inv (a i) (a (i+1)) η hai haj]
  calc
    _ ≤ ∑ i ∈ Finset.range N,
       ((∫ t in a i..a (i+1), g t) +
          η * Real.log (a (i+1)/a i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hBin i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range N, ∫ t in a i..a (i+1), g t) +
        η * (∑ i ∈ Finset.range N, Real.log (a (i+1)/a i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∫ t in b..c, F (t,t) * t⁻¹) + η * Real.log (c/b) := by
      rw [hGsum, hlogsum]

end Green64Analytic.FrozenBins

end

