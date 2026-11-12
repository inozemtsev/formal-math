module

public import Green64.Sieve.BoxError
public import Green64.Library.Sieve.Foundations.Part056

@[expose] public section

/-!
# A uniform bound for positive weighted factor pairs

Apply the finite weighted rectangle sieve and compare its main term
with the localized mass. Control the finite remainder uniformly in the
rectangle and in the roughness cutoff.
-/

section

set_option maxHeartbeats 1600000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

/-- The literal weighted positive shifted-fibre sum. This is
the unchanged left side of the proved normalized finite box theorem. -/
noncomputable def sourceRoughBox
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (W : ℝ)
    (K N : Finset ℕ) (Y : ℕ) : ℝ :=
  ∑ u ∈ Finset.range (Y + 1),
    (parityWeight d L rho u * Psi ((u : ℝ) / Real.exp L)) *
      ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
        if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0

theorem source_rough_box_nonneg
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (W : ℝ)
    (K N : Finset ℕ) (Y : ℕ)
    (hRho : |rho| ≤ 1) (hNonneg : ∀ t, 0 ≤ Psi t) :
    0 ≤ sourceRoughBox d L rho Psi W K N Y := by
  unfold sourceRoughBox
  apply Finset.sum_nonneg
  intro u hu
  apply mul_nonneg
  · exact mul_nonneg (parity_original_parity_A_nonneg434 d L rho hRho u) (hNonneg _)
  · apply Finset.sum_nonneg
    intro xy hxy
    split_ifs <;> norm_num

theorem balanced_double_rough_eq_box
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (kappa : ℝ) (Y : ℕ) :
    balancedRoughPairMass d L rho Psi kappa Y =
      sourceRoughBox d L rho Psi (Real.exp (Real.sqrt L))
        ((Finset.Icc 1 (Y + 2)).filter (balancedFactor L kappa))
        ((Finset.Icc 1 (Y + 2)).filter (balancedFactor L kappa)) Y := rfl

/-- the sieve estimate, in the stronger uniform roughness range.
The box constant precedes both parity signs, all physical rectangles
and every outer cutoff. The source error is discharged by its proved
uniform little-o estimate, not supplied as an assumption. -/
theorem weighted_box_bound_uniform
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t)
    (Carea Cside : ℝ) (hCarea : 0 < Carea) (hCside : 0 < Cside) :
    ∃ Cbox : ℝ, 0 < Cbox ∧ ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ W : ℝ, 2 ≤ W → W ≤ Real.exp (parityOriginalAssignmentTheta434 * L) →
      ∀ (K N : Finset ℕ) (A B C E Y : ℕ),
      K ⊆ Finset.Ico A B → N ⊆ Finset.Ico C E → A ≤ B → C ≤ E →
      (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ)) ≤ Carea * Real.exp L →
      (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) ≤ Cside * Real.exp ((27 / 50 : ℝ) * L) →
      sourceRoughBox (sourceOriginalLiteralDepth 20 L) L rho Psi W K N Y ≤
        Cbox * localizedMass Psi rho L * (sourceNaturalEuler ⌊W⌋₊) ^ 2 := by
  obtain ⟨Cmain, hCmain, hmain⟩ := box_main_Xrho_eventually
    Psi hCont hSupport hNonneg hInterior Carea hCarea
  have herr := box_error_uniform_little_o
    Psi hCont hSupport hNonneg hInterior Cside hCside 1 (by norm_num)
  have hPsi0 : Psi 0 = 0 := by
    by_contra h
    have hh := hSupport (show (0 : ℝ) ∈ Function.support Psi from h)
    norm_num at hh
  refine ⟨Cmain + 1, by linarith, ?_⟩
  filter_upwards [hmain, herr, parity_original_literal_weighted_box_normalized434]
    with L hm he hsource
  intro rho hRho W hW hWz K N A B C E Y hK hN hAB hCE harea hside
  have hflag : ∃ flag : Bool, rho = parityOriginalParitySign434 flag := by
    rcases hRho with rfl | rfl
    · exact ⟨true, by simp [parityOriginalParitySign434]⟩
    · exact ⟨false, by simp [parityOriginalParitySign434]⟩
  obtain ⟨flag, rfl⟩ := hflag
  have hAbs : |parityOriginalParitySign434 flag| ≤ 1 := by
    cases flag <;> norm_num [parityOriginalParitySign434]
  obtain ⟨J, hsource⟩ := hsource
  have hb := hsource (parityOriginalParitySign434 flag) hAbs
    Psi hPsi0 hNonneg hOne W hW hWz K N A B C E Y hK hN hAB hCE
  change sourceRoughBox (sourceOriginalLiteralDepth 20 L)
      L (parityOriginalParitySign434 flag) Psi W K N Y ≤
    parityOriginalNormalizedBoxMainBound434 (sourceOriginalLiteralDepth 20 L) L W A B C E +
      boxFiniteError L (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) at hb
  have herror := he flag W (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ))
    hWz (by positivity) hside
  calc
    _ ≤ _ := hb
    _ ≤ Cmain * localizedMass Psi (parityOriginalParitySign434 flag) L *
          (sourceNaturalEuler ⌊W⌋₊) ^ 2 +
        1 * (localizedMass Psi (parityOriginalParitySign434 flag) L *
          (sourceNaturalEuler ⌊W⌋₊) ^ 2) :=
      add_le_add (hm flag W A B C E harea) herror
    _ = _ := by ring

/-- subpower W=exp(sqrt L) specialization of the sieve estimate for h=-2,
with both parity signs and all source cutoffs after one threshold. -/
theorem weighted_box_bound
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t)
    (Carea Cside : ℝ) (hCarea : 0 < Carea) (hCside : 0 < Cside) :
    ∃ Cbox : ℝ, 0 < Cbox ∧ ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ (K N : Finset ℕ) (A B C E Y : ℕ),
      K ⊆ Finset.Ico A B → N ⊆ Finset.Ico C E → A ≤ B → C ≤ E →
      (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ)) ≤ Carea * Real.exp L →
      (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) ≤ Cside * Real.exp ((27 / 50 : ℝ) * L) →
      sourceRoughBox (sourceOriginalLiteralDepth 20 L)
        L rho Psi (Real.exp (Real.sqrt L)) K N Y ≤
        Cbox * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2 := by
  obtain ⟨Cbox, hCbox, hbox⟩ := weighted_box_bound_uniform
    Psi hCont hSupport hNonneg hOne hInterior Carea Cside hCarea hCside
  refine ⟨Cbox, hCbox, ?_⟩
  filter_upwards [hbox, box_subpower_cutoff_eventually] with L hb hW
  intro rho hRho K N A B C E Y hK hN hAB hCE harea hside
  exact hb rho hRho _ hW.1 hW.2 K N A B C E Y hK hN hAB hCE harea hside

end Green64Analytic.Parity

end
