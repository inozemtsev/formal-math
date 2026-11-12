module

public import Green64.Sieve.DyadicCounting

@[expose] public section

/-!
# Partition a finite weighted sum into active rectangles

Partition the active positive factor pairs by their binary dyad labels.
The finite sum identities retain the original smooth cutoff and give
exact decompositions used by the rectangle estimates.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem positive_log_bin_iff (m k : ℕ) (hm : 0 < m) :
    Nat.log 2 m = k ↔ 2 ^ k ≤ m ∧ m < 2 ^ (k + 1) := by
  constructor
  · intro h
    rw [← h]
    exact positive_binary_log_bounds m hm
  · intro h
    exact Nat.log_eq_of_pow_le_of_lt_pow h.1 h.2

/-- Exact positive shifted fibres, including every endpoint and diagonal.
No replacement of the source weight or roughness tests is involved. -/
theorem binary_fibre_eq_label_filter
    (K N : Finset ℕ) (u : ℕ) (s : ℕ × ℕ) :
    parityOriginalShiftTwoPositivePairFibre434
        (parityOriginalTypeIIBinaryDyadCut434 K s.1)
        (parityOriginalTypeIIBinaryDyadCut434 N s.2) u =
      (parityOriginalShiftTwoPositivePairFibre434 K N u).filter
        (fun xy => (Nat.log 2 xy.1, Nat.log 2 xy.2) = s) := by
  ext xy
  constructor
  · intro h
    have hp := Finset.mem_filter.mp h
    have hKN := Finset.mem_product.mp hp.1
    have hm := Finset.mem_filter.mp hKN.1
    have hn := Finset.mem_filter.mp hKN.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.1, hn.1⟩, hp.2⟩, ?_⟩
    apply Prod.ext
    · exact (positive_log_bin_iff xy.1 s.1 hp.2.1).mpr hm.2
    · exact (positive_log_bin_iff xy.2 s.2 hp.2.2.1).mpr hn.2
  · intro h
    have hl := Finset.mem_filter.mp h
    have hp := Finset.mem_filter.mp hl.1
    have hKN := Finset.mem_product.mp hp.1
    have hmEq := congrArg (fun z : ℕ × ℕ => z.1) hl.2
    have hnEq := congrArg (fun z : ℕ × ℕ => z.2) hl.2
    have hm : 2 ^ s.1 ≤ xy.1 ∧ xy.1 < 2 ^ (s.1 + 1) :=
      (positive_log_bin_iff xy.1 s.1 hp.2.1).mp
        hmEq
    have hn : 2 ^ s.2 ≤ xy.2 ∧ xy.2 < 2 ^ (s.2 + 1) :=
      (positive_log_bin_iff xy.2 s.2 hp.2.2.1).mp
        hnEq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hKN.1, hm⟩, Finset.mem_filter.mpr ⟨hKN.2, hn⟩⟩, hp.2⟩

theorem nonzero_fibre_label_active
    (L : ℝ) (Psi : ℝ → ℝ) (K N : Finset ℕ) (Y u : ℕ)
    (hu : u ∈ Finset.range (Y + 1)) (hPsi : Psi ((u : ℝ) / Real.exp L) ≠ 0)
    (xy : ℕ × ℕ) (hxy : xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u) :
    (Nat.log 2 xy.1, Nat.log 2 xy.2) ∈
      psiActiveDyadLabels L Psi K N Y := by
  apply Finset.mem_image.mpr
  refine ⟨xy, ?_, rfl⟩
  have hp := Finset.mem_filter.mp hxy
  simp only [psiActiveBoxPairs, Finset.mem_filter]
  exact ⟨hp.1, ⟨u, hu, hp.2.1, hp.2.2.1, hp.2.2.2, hPsi⟩⟩

/-- Per-u exact weighted partition. The Psi=0 branch is discharged
before using active-label membership, so inactive pairs are not dropped. -/
theorem weighted_fibre_active_partition
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (W : ℝ)
    (K N : Finset ℕ) (Y u : ℕ) (hu : u ∈ Finset.range (Y + 1)) :
    (parityWeight d L rho u * Psi ((u : ℝ) / Real.exp L)) *
        (∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
          if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0) =
      ∑ s ∈ psiActiveDyadLabels L Psi K N Y,
        (parityWeight d L rho u * Psi ((u : ℝ) / Real.exp L)) *
          ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434
              (parityOriginalTypeIIBinaryDyadCut434 K s.1)
              (parityOriginalTypeIIBinaryDyadCut434 N s.2) u,
            if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0 := by
  by_cases hPsi : Psi ((u : ℝ) / Real.exp L) = 0
  · simp only [hPsi, mul_zero, zero_mul, Finset.sum_const_zero]
  have hmap : ∀ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
      (Nat.log 2 xy.1, Nat.log 2 xy.2) ∈
        psiActiveDyadLabels L Psi K N Y :=
    fun xy hxy => nonzero_fibre_label_active L Psi K N Y u hu hPsi xy hxy
  have hpart :
      (∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
        if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0) =
      ∑ s ∈ psiActiveDyadLabels L Psi K N Y,
        ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434
            (parityOriginalTypeIIBinaryDyadCut434 K s.1)
            (parityOriginalTypeIIBinaryDyadCut434 N s.2) u,
          if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap
      (fun xy => if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [binary_fibre_eq_label_filter]
  rw [hpart, Finset.mul_sum]

/-- Exact weighted source identity, not an asserted model
identification. The same A_rho, Psi, both rough tests, positive fibre,
outer cutoff and each binary interval occur on both sides. -/
theorem source_rough_box_active_partition
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (W : ℝ)
    (K N : Finset ℕ) (Y : ℕ) :
    sourceRoughBox d L rho Psi W K N Y =
      ∑ s ∈ psiActiveDyadLabels L Psi K N Y,
        sourceRoughBox d L rho Psi W
          (parityOriginalTypeIIBinaryDyadCut434 K s.1)
          (parityOriginalTypeIIBinaryDyadCut434 N s.2) Y := by
  unfold sourceRoughBox
  calc
    _ = ∑ u ∈ Finset.range (Y + 1),
        ∑ s ∈ psiActiveDyadLabels L Psi K N Y,
          (parityWeight d L rho u * Psi ((u : ℝ) / Real.exp L)) *
            ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434
                (parityOriginalTypeIIBinaryDyadCut434 K s.1)
                (parityOriginalTypeIIBinaryDyadCut434 N s.2) u,
              if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact weighted_fibre_active_partition d L rho Psi W K N Y u hu
    _ = _ := Finset.sum_comm

end Green64Analytic.Parity

end
