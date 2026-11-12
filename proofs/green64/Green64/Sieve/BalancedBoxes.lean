module

public import Green64.Sieve.DyadicPartition

@[expose] public section

/-!
# Sum the positive bounds over balanced rectangles

Sum the positive rectangle estimates over the active balanced dyads.
The linear bound on their number yields a uniform estimate for rough
factor pairs.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem localizedMass_eventually_nonneg
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∀ᶠ L : ℝ in atTop, ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      0 ≤ localizedMass Psi rho L := by
  obtain ⟨c0, hc0, hmass⟩ := box_strong_mass_shared
    Psi hCont hSupport hNonneg hInterior
  filter_upwards [hmass] with L hm
  have hHQ := box_HQ_nonneg 20 (sourceOriginalLiteralDepth 20 L) L
  have hlower : 0 ≤ c0 * (Real.exp L / L) *
      (sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
        sourceLiteralHP (sourceOriginalPAllActualBands 20 L)) :=
    mul_nonneg (mul_nonneg hc0.le (div_nonneg (Real.exp_pos _).le hm.1.le))
      (mul_nonneg hHQ (by linarith [hm.2.1]))
  intro rho hRho
  rcases hRho with rfl | rfl
  · simpa [parityOriginalParitySign434] using hlower.trans (hm.2.2 true)
  · simpa [parityOriginalParitySign434] using hlower.trans (hm.2.2 false)

/-- Original6.10 from the proved source box sieve and the exact active
weighted partition. The constant and L threshold precede kappa,
both parity signs, both factor carriers, and the outer source cutoff. -/
theorem balanced_box_bound_uniform
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ kappa : ℝ, 0 ≤ kappa → kappa ≤ 1 / 50 →
      ∀ (K N : Finset ℕ) (Y : ℕ),
      (∀ m ∈ K, balancedFactor L kappa m) →
      (∀ n ∈ N, balancedFactor L kappa n) →
      sourceRoughBox (sourceOriginalLiteralDepth 20 L)
        L rho Psi (Real.exp (Real.sqrt L)) K N Y ≤
        C1 * (kappa * L + 1) * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 := by
  obtain ⟨Cbox, hCbox, hbox⟩ := weighted_box_bound
    Psi hCont hSupport hNonneg hOne hInterior 4 2 (by norm_num) (by norm_num)
  refine ⟨Cbox * balancedDyadCountConstant,
    mul_pos hCbox balanced_dyad_count_constant_pos, ?_⟩
  filter_upwards [hbox, localizedMass_eventually_nonneg
    Psi hCont hSupport hNonneg hInterior, eventually_ge_atTop (0 : ℝ)]
    with L hb hx hL
  intro rho hRho kappa hk0 hk K N Y hK hN
  let labels := psiActiveDyadLabels L Psi K N Y
  have hcard := active_balanced_dyads_card
    L kappa hL hk0 Psi hSupport K N Y hK hN
  have hscale : 0 ≤ Cbox * localizedMass Psi rho L *
      (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 :=
    mul_nonneg (mul_nonneg hCbox.le (hx rho hRho)) (sq_nonneg _)
  have heach : ∀ s ∈ labels,
      sourceRoughBox (sourceOriginalLiteralDepth 20 L)
        L rho Psi (Real.exp (Real.sqrt L))
          (parityOriginalTypeIIBinaryDyadCut434 K s.1)
          (parityOriginalTypeIIBinaryDyadCut434 N s.2) Y ≤
      Cbox * localizedMass Psi rho L *
        (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 := by
    intro s hs
    have hg := active_balanced_box_geometry
      L kappa hL hk Psi hSupport K N Y hK hN s hs
    exact hb rho hRho _ _ (2 ^ s.1) (2 ^ (s.1 + 1)) (2 ^ s.2) (2 ^ (s.2 + 1)) Y
      (binary_cut_subset_box K s.1)
      (binary_cut_subset_box N s.2)
      (binary_box_ordered s.1)
      (binary_box_ordered s.2) hg.1 hg.2
  rw [source_rough_box_active_partition]
  calc
    _ ≤ ∑ s ∈ labels, Cbox * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 :=
      Finset.sum_le_sum heach
    _ = (labels.card : ℝ) * (Cbox * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (balancedDyadCountConstant * (kappa * L + 1)) *
        (Cbox * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hscale
    _ = _ := by ring

/-- The literal balanced rough-pair mass in the sieve source,
at h=-2 and literal depth, satisfies the sieve estimate with no assumed sieve bound. -/
theorem balanced_rough_pair_bound
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ kappa : ℝ, 0 ≤ kappa → kappa ≤ 1 / 50 →
      ∀ Y : ℕ,
      balancedRoughPairMass (sourceOriginalLiteralDepth 20 L)
        L rho Psi kappa Y ≤
        C1 * (kappa * L + 1) * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 := by
  obtain ⟨C1, hC1, hbound⟩ := balanced_box_bound_uniform
    Psi hCont hSupport hNonneg hOne hInterior
  refine ⟨C1, hC1, ?_⟩
  filter_upwards [hbound] with L hb
  intro rho hRho kappa hk0 hk Y
  rw [balanced_double_rough_eq_box]
  exact hb rho hRho kappa hk0 hk _ _ Y
    (fun m hm => (Finset.mem_filter.mp hm).2)
    (fun n hn => (Finset.mem_filter.mp hn).2)

end Green64Analytic.Parity

end
