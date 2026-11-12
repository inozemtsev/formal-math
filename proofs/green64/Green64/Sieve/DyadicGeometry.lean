module

public import Green64.Sieve.WeightedBoxes
public import Green64.Library.Sieve.Foundations.Part044

@[expose] public section

/-!
# Geometry of rectangles meeting the localized support

Locate every active factor pair in its binary dyadic rectangle. The
cutoff support bounds the product of the two dyadic scales; balanced
factors also give separate upper bounds for the side lengths.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

/-- positive pairs for which the compact Psi is active.
No positivity of A_rho or source witness is inferred from this geometry. -/
noncomputable def psiActiveBoxPairs
    (L : ℝ) (Psi : ℝ → ℝ) (K N : Finset ℕ) (Y : ℕ) : Finset (ℕ × ℕ) :=
  (K.product N).filter (fun xy =>
    ∃ u ∈ Finset.range (Y + 1),
      0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 * xy.2 = u + 2 ∧
        Psi ((u : ℝ) / Real.exp L) ≠ 0)

noncomputable def psiActiveDyadLabels
    (L : ℝ) (Psi : ℝ → ℝ) (K N : Finset ℕ) (Y : ℕ) : Finset (ℕ × ℕ) :=
  (psiActiveBoxPairs L Psi K N Y).image
    (fun xy => (Nat.log 2 xy.1, Nat.log 2 xy.2))

theorem positive_binary_log_bounds (m : ℕ) (hm : 0 < m) :
    2 ^ (Nat.log 2 m) ≤ m ∧ m < 2 ^ (Nat.log 2 m + 1) :=
  (parity_original_actual_binary_dyadic_scale_iff434 m (Nat.log 2 m) hm).mp rfl

/-- Psi/product localization is imposed before dyadic counting. -/
theorem active_dyad_product_window
    (L : ℝ) (hL : 0 ≤ L) (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (K N : Finset ℕ) (Y : ℕ) (s : ℕ × ℕ)
    (hs : s ∈ psiActiveDyadLabels L Psi K N Y) :
    Real.exp L / 4 < (2 : ℝ) ^ s.1 * (2 : ℝ) ^ s.2 ∧
      (2 : ℝ) ^ s.1 * (2 : ℝ) ^ s.2 ≤ 4 * Real.exp L := by
  unfold psiActiveDyadLabels at hs
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hs
  have hactive : xy ∈ K.product N ∧ (∃ u ∈ Finset.range (Y + 1),
      0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 * xy.2 = u + 2 ∧ Psi ((u : ℝ) / Real.exp L) ≠ 0) := by
    simpa only [psiActiveBoxPairs, Finset.mem_filter] using hxy
  obtain ⟨u, hu, hm, hn, hprod, hPsi⟩ := hactive.2
  have hloc := hSupport (show (u : ℝ) / Real.exp L ∈ Function.support Psi from hPsi)
  have hx := Real.exp_pos L
  have hx1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hul : Real.exp L ≤ (u : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hx).mp hloc.1
  have huu : (u : ℝ) ≤ 2 * Real.exp L := (div_le_iff₀ hx).mp hloc.2
  have hp : (xy.1 : ℝ) * (xy.2 : ℝ) = (u : ℝ) + 2 := by exact_mod_cast hprod
  have hpl : Real.exp L ≤ (xy.1 : ℝ) * (xy.2 : ℝ) := by nlinarith
  have hpu : (xy.1 : ℝ) * (xy.2 : ℝ) ≤ 4 * Real.exp L := by nlinarith
  have hmB := positive_binary_log_bounds xy.1 hm
  have hnB := positive_binary_log_bounds xy.2 hn
  have hml : (2 : ℝ) ^ (Nat.log 2 xy.1) ≤ (xy.1 : ℝ) := by exact_mod_cast hmB.1
  have hnl : (2 : ℝ) ^ (Nat.log 2 xy.2) ≤ (xy.2 : ℝ) := by exact_mod_cast hnB.1
  have hmu : (xy.1 : ℝ) < (2 : ℝ) ^ (Nat.log 2 xy.1 + 1) := by exact_mod_cast hmB.2
  have hnu : (xy.2 : ℝ) < (2 : ℝ) ^ (Nat.log 2 xy.2 + 1) := by exact_mod_cast hnB.2
  have htop : (xy.1 : ℝ) * (xy.2 : ℝ) <
      4 * ((2 : ℝ) ^ (Nat.log 2 xy.1) * (2 : ℝ) ^ (Nat.log 2 xy.2)) := by
    calc
      _ < (2 : ℝ) ^ (Nat.log 2 xy.1 + 1) * (xy.2 : ℝ) :=
        mul_lt_mul_of_pos_right hmu (by exact_mod_cast hn)
      _ < (2 : ℝ) ^ (Nat.log 2 xy.1 + 1) * (2 : ℝ) ^ (Nat.log 2 xy.2 + 1) :=
        mul_lt_mul_of_pos_left hnu (pow_pos (by norm_num) _)
      _ = _ := by rw [pow_succ, pow_succ]; ring
  constructor
  · dsimp only
    nlinarith
  · exact (mul_le_mul hml hnl (by positivity) (Nat.cast_nonneg _)).trans hpu

/-- Both closed balanced restrictions constrain the attained
binary labels; the lower scale endpoint is strictly one dyad below. -/
theorem active_dyad_balanced_ranges
    (L kappa : ℝ) (Psi : ℝ → ℝ) (K N : Finset ℕ) (Y : ℕ)
    (hK : ∀ m ∈ K, balancedFactor L kappa m)
    (hN : ∀ n ∈ N, balancedFactor L kappa n)
    (s : ℕ × ℕ)
    (hs : s ∈ psiActiveDyadLabels L Psi K N Y) :
    (Real.exp (((1 / 2 : ℝ) - 2 * kappa) * L) < (2 : ℝ) ^ (s.1 + 1) ∧
      (2 : ℝ) ^ s.1 ≤ Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L)) ∧
    (Real.exp (((1 / 2 : ℝ) - 2 * kappa) * L) < (2 : ℝ) ^ (s.2 + 1) ∧
      (2 : ℝ) ^ s.2 ≤ Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L)) := by
  unfold psiActiveDyadLabels at hs
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hs
  have hactive : xy ∈ K.product N ∧ (∃ u ∈ Finset.range (Y + 1),
      0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 * xy.2 = u + 2 ∧ Psi ((u : ℝ) / Real.exp L) ≠ 0) := by
    simpa only [psiActiveBoxPairs, Finset.mem_filter] using hxy
  obtain ⟨u, hu, hm, hn, hprod, hPsi⟩ := hactive.2
  have hKN := Finset.mem_product.mp hactive.1
  have hmb := hK xy.1 hKN.1
  have hnb := hN xy.2 hKN.2
  have hmB := positive_binary_log_bounds xy.1 hm
  have hnB := positive_binary_log_bounds xy.2 hn
  have hml : (2 : ℝ) ^ (Nat.log 2 xy.1) ≤ (xy.1 : ℝ) := by exact_mod_cast hmB.1
  have hnl : (2 : ℝ) ^ (Nat.log 2 xy.2) ≤ (xy.2 : ℝ) := by exact_mod_cast hnB.1
  have hmu : (xy.1 : ℝ) < (2 : ℝ) ^ (Nat.log 2 xy.1 + 1) := by exact_mod_cast hmB.2
  have hnu : (xy.2 : ℝ) < (2 : ℝ) ^ (Nat.log 2 xy.2 + 1) := by exact_mod_cast hnB.2
  exact ⟨⟨hmb.1.trans_lt hmu, hml.trans hmb.2⟩,
    ⟨hnb.1.trans_lt hnu, hnl.trans hnb.2⟩⟩

theorem binary_cut_subset_box (K : Finset ℕ) (k : ℕ) :
    parityOriginalTypeIIBinaryDyadCut434 K k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
  intro m hm
  exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hm).2

theorem binary_box_length (k : ℕ) :
    2 ^ (k + 1) - 2 ^ k = (2 ^ k : ℕ) := by
  rw [pow_succ]
  omega

theorem binary_box_ordered (k : ℕ) :
    (2 ^ k : ℕ) ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

/-- Every actually attained balanced dyad satisfies the fixed box
constants Carea=4,Cside=2, uniformly before kappa is chosen. -/
theorem active_balanced_box_geometry
    (L kappa : ℝ) (hL : 0 ≤ L) (hkappa : kappa ≤ 1 / 50)
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (K N : Finset ℕ) (Y : ℕ)
    (hK : ∀ m ∈ K, balancedFactor L kappa m)
    (hN : ∀ n ∈ N, balancedFactor L kappa n)
    (s : ℕ × ℕ) (hs : s ∈ psiActiveDyadLabels L Psi K N Y) :
    (((2 ^ (s.1 + 1) - 2 ^ s.1 : ℕ) : ℝ) *
      ((2 ^ (s.2 + 1) - 2 ^ s.2 : ℕ) : ℝ)) ≤ 4 * Real.exp L ∧
    (((2 ^ (s.1 + 1) - 2 ^ s.1 : ℕ) : ℝ) +
      ((2 ^ (s.2 + 1) - 2 ^ s.2 : ℕ) : ℝ)) ≤ 2 * Real.exp ((27 / 50 : ℝ) * L) := by
  rw [binary_box_length, binary_box_length]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hprod := active_dyad_product_window L hL Psi hSupport K N Y s hs
  have hr := active_dyad_balanced_ranges L kappa Psi K N Y hK hN s hs
  have he : Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L) ≤ Real.exp ((27 / 50 : ℝ) * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hL)
  constructor
  · exact hprod.2
  · simpa only [two_mul] using add_le_add (hr.1.2.trans he) (hr.2.2.trans he)

end Green64Analytic.Parity

end
