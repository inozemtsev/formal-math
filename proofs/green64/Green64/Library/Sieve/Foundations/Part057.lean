module

public import Green64.Library.Sieve.Foundations.Part056
public import Green64.Library.Weights.Part108

@[expose] public section

/-!
# Sieve / Foundations / Part057

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalAssignmentBoxErrors -/

section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
open SourceCRT

/-- Actual source assignments and uniform Boolean masks, with the exact
product-two sieve error at each assignment. -/
noncomputable def parityOriginalAssignmentBoxErrorAverage434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ)
    (J A B C E : ℕ) (rough : ℕ → Bool) : ℝ :=
  ∑ a : (j : T) → Fin r → {p // p ∈ Q j},
    ∑ marks : (g : G) → {p // p ∈ P g},
      parityAssignmentNormalization434 T r P *
        ∑ S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
          (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
            (parityAssignmentModulus434 r Q P a marks)).card *
          parityOriginalShiftTwoSieveError434 2
            (parityAssignmentModulus434 r Q P a marks) A B C E z
            (Finset.univ.biUnion (fun j : Fin J =>
              sourceNaturalOddPrimeBlock (parityAssignmentModulus434 r Q P a marks) z j.val))
            rough
            (fun p => decide (p ∈
              parityAssignmentDetBans434 z (Finset.univ.biUnion P)
                (parityAssignmentModulus434 r Q P a marks) ∪
              (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S)))

/-- Uniform mask averaging spends no factor equal to the number of masks.
The statement uses the actual finite error support, not an assumed ledger. -/
theorem parity_assignment_box_error_average_two_moments434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ) (hz : 1 < z)
    (J A B C E : ℕ) (rough : ℕ → Bool) (hAB : A ≤ B) (hCE : C ≤ E)
    (hD : ∀ (a : (j : T) → Fin r → {p // p ∈ Q j})
      (marks : (g : G) → {p // p ∈ P g}),
      0 < parityAssignmentModulus434 r Q P a marks ∧
        Nat.Coprime 2 (parityAssignmentModulus434 r Q P a marks))
    (hTwo : ∀ (a : (j : T) → Fin r → {p // p ∈ Q j})
      (marks : (g : G) → {p // p ∈ P g})
      S, S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset →
      2 ∉ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
        (parityAssignmentModulus434 r Q P a marks) ∪
        (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S))
    (M0 M1 : ℝ)
    (hm0 : (∑ _a : (j : T) → Fin r → {p // p ∈ Q j},
      ∑ _marks : (g : G) → {p // p ∈ P g}, parityAssignmentNormalization434 T r P) ≤ M0)
    (hm1 : (∑ a : (j : T) → Fin r → {p // p ∈ Q j},
      ∑ marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 T r P *
          (parityAssignmentModulus434 r Q P a marks : ℝ)) ≤ M1) :
    let Z := ⌊z^(10 : ℝ)⌋₊
    parityOriginalAssignmentBoxErrorAverage434 r Q P z J A B C E rough ≤
      (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) * M0 +
        4 * (Z : ℝ)^2 * M1) * (1+Real.log (Z : ℝ))^3 := by
  classical
  dsimp only
  let Z := ⌊z^(10 : ℝ)⌋₊
  let eta := parityAssignmentNormalization434 T r P
  let c0 : ℝ := 2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ)
  let c1 : ℝ := 4 * (Z : ℝ)^2
  let F : ℝ := (1+Real.log (Z : ℝ))^3
  have hzpow : 1 ≤ z^(10 : ℝ) := Real.one_le_rpow hz.le (by norm_num)
  have hZ : 1 ≤ Z := Nat.le_floor
    (show ((1 : ℕ) : ℝ) ≤ z^(10 : ℝ) by simpa only [Nat.cast_one] using hzpow)
  have hZR : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hF : 0 ≤ F := pow_nonneg (by linarith [Real.log_nonneg hZR]) _
  have he : 0 ≤ eta := parity_assignment_normalization_nonneg434 T r P
  have havg (a : (j : T) → Fin r → {p // p ∈ Q j})
      (marks : (g : G) → {p // p ∈ P g}) :
      (∑ S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
        (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
          (parityAssignmentModulus434 r Q P a marks)).card *
        parityOriginalShiftTwoSieveError434 2
          (parityAssignmentModulus434 r Q P a marks) A B C E z
          (Finset.univ.biUnion (fun j : Fin J =>
            sourceNaturalOddPrimeBlock (parityAssignmentModulus434 r Q P a marks) z j.val))
          rough (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
            (parityAssignmentModulus434 r Q P a marks) ∪
              (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S)))) ≤
      (c0 + c1*(parityAssignmentModulus434 r Q P a marks : ℝ))*F := by
    calc
      _ ≤ ∑ _S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
          (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
            (parityAssignmentModulus434 r Q P a marks)).card *
          ((c0+c1*(parityAssignmentModulus434 r Q P a marks : ℝ))*F) := by
        apply Finset.sum_le_sum
        intro S hS
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hb := parity_original_shift_two_box_sieve_error_bound434 2 J
          (parityAssignmentModulus434 r Q P a marks) A B C E z hz
          (hD a marks).1 (hD a marks).2 rough
          (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
            (parityAssignmentModulus434 r Q P a marks) ∪
              (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S)))
          (by simp only [hTwo a marks S hS, decide_false]) hAB hCE
        dsimp only at hb
        norm_num only [Nat.cast_ofNat] at hb
        calc
          _ ≤ (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) +
              4 * (parityAssignmentModulus434 r Q P a marks : ℝ) * (Z : ℝ)^2) * F := hb
          _ = _ := by dsimp [c0,c1]; ring
      _ = _ := by rw [← Finset.sum_mul, parity_uniform_half_mask_normalized434, one_mul]
  have htotal :
      parityOriginalAssignmentBoxErrorAverage434 r Q P z J A B C E rough ≤
      ∑ a : (j : T) → Fin r → {p // p ∈ Q j},
        ∑ marks : (g : G) → {p // p ∈ P g},
          eta * ((c0+c1*(parityAssignmentModulus434 r Q P a marks : ℝ))*F) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro marks hm
    exact mul_le_mul_of_nonneg_left (havg a marks) he
  have halgebra :
      (∑ a : (j : T) → Fin r → {p // p ∈ Q j},
        ∑ marks : (g : G) → {p // p ∈ P g},
          eta * ((c0+c1*(parityAssignmentModulus434 r Q P a marks : ℝ))*F)) =
      (c0*(∑ _a : (j : T) → Fin r → {p // p ∈ Q j},
          ∑ _marks : (g : G) → {p // p ∈ P g}, eta) +
       c1*(∑ a : (j : T) → Fin r → {p // p ∈ Q j},
          ∑ marks : (g : G) → {p // p ∈ P g},
            eta*(parityAssignmentModulus434 r Q P a marks : ℝ)))*F := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro marks hm
    ring
  rw [halgebra] at htotal
  exact htotal.trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hm0 (by dsimp [c0]; positivity))
      (mul_le_mul_of_nonneg_left hm1 (by dsimp [c1]; positivity))) hF)

/-- Actual original6.9 assignment/mask error aggregation at literal depth.
Every assignment premise comes from the source; both factor lengths remain. -/
theorem parity_original_literal_assignment_box_errors434 :
    ∀ᶠ L : ℝ in atTop, ∀ (J A B C E : ℕ) (rough : ℕ → Bool),
      A ≤ B → C ≤ E →
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434 * L)
      let Z := ⌊z^(10 : ℝ)⌋₊
      parityOriginalAssignmentBoxErrorAverage434 20 Q P z J A B C E rough ≤
        (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L *
          (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) * Real.exp (L/20) +
            4 * (Z : ℝ)^2 * Real.exp (L/10)) * (1+Real.log (Z : ℝ))^3 := by
  filter_upwards [parity_original_literal_assignment_three_moments434,
    parity_original_literal_assignment_CRT_inputs_eventually434,
    eventually_gt_atTop (0 : ℝ)] with L hm hc hL
  intro J A B C E rough hAB hCE
  dsimp only at hm hc ⊢
  have htheta : 0 < parityOriginalAssignmentTheta434 := by
    norm_num [parityOriginalAssignmentTheta434]
  have hz : 1 < Real.exp (parityOriginalAssignmentTheta434*L) :=
    Real.one_lt_exp_iff.mpr (mul_pos htheta hL)
  have h := parity_assignment_box_error_average_two_moments434 20
    (fun j : parityOriginalAssignmentTail434 (sourceOriginalLiteralDepth 20 L) =>
      sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L j.val)
    (sourceOriginalPAllActualBands 20 L)
    (Real.exp (parityOriginalAssignmentTheta434*L)) hz J A B C E rough hAB hCE
    (fun a marks => ⟨(hc a marks).1,(hc a marks).2.1⟩)
    (by
      intro a marks S hS htwo
      have h3 := ((hc a marks).2.2 S hS 2 htwo).2.1
      omega)
    _ _ hm.2.2.1 hm.2.2.2
  convert h using 1 <;> ring

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalWeightedBoxSieveJoin -/

section

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

/-- Exact main terms from the actual assignment-by-assignment product-two
box sieve, with the same source half masks. -/
noncomputable def parityOriginalAssignmentBoxMainAverage434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z W : ℝ)
    (J A B C E : ℕ) : ℝ :=
  ∑ a : (j : T) → Fin r → {p // p ∈ Q j},
    ∑ marks : (g : G) → {p // p ∈ P g},
      parityAssignmentNormalization434 T r P *
        ∑ S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
          (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
            (parityAssignmentModulus434 r Q P a marks)).card *
          (parityOriginalShiftTwoBoxMass434 (parityAssignmentModulus434 r Q P a marks) A B C E *
            (∏ p ∈ Finset.univ.biUnion (fun j : Fin J =>
              sourceNaturalOddPrimeBlock (parityAssignmentModulus434 r Q P a marks) z j.val),
              (1-parityOriginalShiftTwoBoxDensity434
                (fun p => decide ((p : ℝ) ≤ W))
                (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
                  (parityAssignmentModulus434 r Q P a marks) ∪
                  (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S))) p)) *
            Real.exp (parityOriginalShiftTwoSieveRho434 2))

theorem parity_assignment_rough_pairs_le_actual_box_sieve434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z W : ℝ) (hz : 1 < z)
    (K N : Finset ℕ) (J A B C E : ℕ)
    (hK : K ⊆ Finset.Ico A B) (hN : N ⊆ Finset.Ico C E)
    (hD : ∀ (a : (j : T) → Fin r → {p // p ∈ Q j})
      (marks : (g : G) → {p // p ∈ P g}), 0 < parityAssignmentModulus434 r Q P a marks) :
    parityOriginalAssignmentPairBound434 r Q P z K N
      (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) ≤
    parityOriginalAssignmentBoxMainAverage434 r Q P z W J A B C E +
    parityOriginalAssignmentBoxErrorAverage434 r Q P z J A B C E
      (fun p => decide ((p : ℝ) ≤ W)) := by
  classical
  unfold parityOriginalAssignmentPairBound434 parityOriginalAssignmentBoxMainAverage434
    parityOriginalAssignmentBoxErrorAverage434
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro marks hm
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (parity_assignment_normalization_nonneg434 T r P)
  apply Finset.sum_le_sum
  intro S hS
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let D := parityAssignmentModulus434 r Q P a marks
  let Bans := parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪
    (parityAssignmentMaskUniverse434 P D \ S)
  let PP := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
  have hpp (p : ℕ) (hp : p ∈ PP) : p.Prime := by
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    exact (source_natural_block_prime D z j.val p hpj).1
  have hs :
      ((parityOriginalAssignmentSiftedPairs434 K N
        (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) D Bans).card : ℝ) ≤
      (parityOriginalShiftTwoBoxSifted434 D A B C E PP
        (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans))).card := by
    exact_mod_cast Finset.card_le_card
      (parity_original_assignment_pairs_subset_box434 K N A B C E D W Bans PP hK hN hpp)
  exact hs.trans (parity_original_shift_two_box_sieve434 2 J D A B C E z hz
    (by norm_num) (by norm_num) (hD a marks)
    (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans)))

/-- Genuine weighted Parity source in arbitrary unchanged integer rectangles.
The exact source-to-sieve chain and all assignment/mask errors are discharged.
Only the explicit Euler main term is left for the subsequent analytic bound. -/
theorem parity_original_literal_weighted_box_sieve434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (rho : ℝ), |rho| ≤ 1 →
      ∀ (Psi : ℝ → ℝ), Psi 0 = 0 → (∀ x, 0 ≤ Psi x) → (∀ x, Psi x ≤ 1) →
      ∀ (W : ℝ) (K N : Finset ℕ) (J A B C E Y : ℕ),
      K ⊆ Finset.Ico A B → N ⊆ Finset.Ico C E → A ≤ B → C ≤ E →
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434 * L)
      let Z := ⌊z^(10 : ℝ)⌋₊
      (∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u : ℝ)/Real.exp L)) *
          ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
            if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0) ≤
      parityOriginalAssignmentBoxMainAverage434 20 Q P z W J A B C E +
      (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L *
        (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) * Real.exp (L/20) +
          4 * (Z : ℝ)^2 * Real.exp (L/10)) * (1+Real.log (Z : ℝ))^3 := by
  filter_upwards [parity_original_literal_assignment_box_errors434,
    parity_original_literal_assignment_CRT_inputs_eventually434,
    eventually_gt_atTop (0 : ℝ)] with L herr hcrt hL
  intro rho hrho Psi hPsi0 hPsiNonneg hPsiOne W K N J A B C E Y hK hN hAB hCE
  dsimp only at hcrt ⊢
  have htheta : 0 < parityOriginalAssignmentTheta434 := by norm_num [parityOriginalAssignmentTheta434]
  have hz : 1 < Real.exp (parityOriginalAssignmentTheta434*L) :=
    Real.one_lt_exp_iff.mpr (mul_pos htheta hL)
  have hs := parity_original_weighted_fibre_le_assignment_pairs434
    (sourceOriginalLiteralDepth 20 L) L hL rho hrho Psi hPsi0 hPsiNonneg hPsiOne K N
    (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) Y
  have hb := parity_assignment_rough_pairs_le_actual_box_sieve434 20
    (fun j : parityOriginalAssignmentTail434 (sourceOriginalLiteralDepth 20 L) =>
      sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L j.val)
    (sourceOriginalPAllActualBands 20 L) (Real.exp (parityOriginalAssignmentTheta434*L)) W hz
    K N J A B C E hK hN (fun a marks => (hcrt a marks).1)
  have hfinal := (hs.trans hb).trans
    (add_le_add le_rfl (herr J A B C E (fun p => decide ((p : ℝ) ≤ W)) hAB hCE))
  refine le_trans ?_ hfinal
  apply Finset.sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg
    (parity_original_parity_A_nonneg434 (sourceOriginalLiteralDepth 20 L) L rho hrho u)
    (hPsiNonneg _))
  apply Finset.sum_le_sum
  intro xy hxy
  by_cases hr : sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2
  · simp only [hr, ite_true, le_refl]
  · simp only [hr, ite_false, le_refl]

end Green64Analytic.Parity

end

/-! ## OriginalMaskEulerAverage -/

section

set_option maxHeartbeats 1400000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- The actual half-mask expectation of the allowed-prime Euler correction,
with S interpreted as allowed (not banned), is an exact finite product. -/
theorem parity_original_mask_euler_average_exact434
    (U : Finset ℕ) (hU : ∀ p ∈ U, 3 ≤ p) :
    (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
      ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹) =
    ∏ p ∈ U, sourceGroupEulerF p := by
  classical
  calc
    _ = ∑ S ∈ U.powerset,
        (∏ p ∈ S, (1/2 : ℝ)*(1-(p : ℝ)⁻¹)⁻¹) *
          (∏ _p ∈ U \ S, (1/2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [parity_uniform_half_mask_factor_weight434 U S (Finset.mem_powerset.mp hS),
        Finset.prod_mul_distrib]
      ring
    _ = ∏ p ∈ U, ((1/2 : ℝ)*(1-(p : ℝ)⁻¹)⁻¹ + 1/2) :=
      (Finset.prod_add (fun p : ℕ => (1/2 : ℝ)*(1-(p : ℝ)⁻¹)⁻¹)
        (fun _ => (1/2 : ℝ)) U).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hU p hp
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
      have hi : (1-(p : ℝ)⁻¹)⁻¹ = (p : ℝ)/((p : ℝ)-1) := by
        have hh : 1-(p : ℝ)⁻¹ = ((p : ℝ)-1)/(p : ℝ) := by
          field_simp <;> ring
        rw [hh, inv_div]
      rw [hi]
      unfold sourceGroupEulerF
      field_simp <;> ring

/-- The random mask domain is the original group union with assignment
primes erased. Its Euler expectation is bounded by the original full H_P. -/
theorem parity_original_assignment_mask_euler_le_HP434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (D : ℕ)
    (hP : ∀ g p, p ∈ P g → 3 ≤ p) (hPn : ∀ g, (P g).Nonempty) :
    (∑ S ∈ (parityAssignmentMaskUniverse434 P D).powerset,
      (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P D).card *
        ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹) ≤ sourceLiteralHP P := by
  classical
  let Pall := Finset.univ.biUnion P
  let U := parityAssignmentMaskUniverse434 P D
  have hsub : U ⊆ Pall := Finset.filter_subset _ _
  have h3 (p : ℕ) (hp : p ∈ Pall) : 3 ≤ p := by
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hP g p hpg
  rw [parity_original_mask_euler_average_exact434 U (fun p hp => h3 p (hsub hp))]
  have hprod : (∏ p ∈ U, sourceGroupEulerF p) ≤ ∏ p ∈ Pall, sourceGroupEulerF p := by
    calc
      _ = (∏ p ∈ U, sourceGroupEulerF p)*1 := by ring
      _ ≤ (∏ p ∈ U, sourceGroupEulerF p) *
          (∏ p ∈ Pall \ U, sourceGroupEulerF p) :=
        mul_le_mul_of_nonneg_left
          (Finset.one_le_prod₀ (fun p hp => source_group_euler_factor_one_le p
            (h3 p (Finset.mem_sdiff.mp hp).1)))
          (Finset.prod_nonneg (fun p hp =>
            (show (0 : ℝ) ≤ 1 by norm_num).trans (source_group_euler_factor_one_le p (h3 p (hsub hp)))))
      _ = _ := by
        rw [mul_comm]
        exact Finset.prod_sdiff hsub
  exact hprod.trans (source_literal_hp_ge_base P hP hPn)

/-- Source-facing actual P-groups, uniform in the assignment modulus and
all L-dependent group counts. No number-of-masks loss is paid. -/
theorem parity_original_actual_mask_euler_le_HP_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℕ,
      (∑ S ∈ (parityAssignmentMaskUniverse434 (sourceOriginalPAllActualBands 20 L) D).powerset,
        (1/2 : ℝ)^(parityAssignmentMaskUniverse434 (sourceOriginalPAllActualBands 20 L) D).card *
          ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹) ≤
      sourceLiteralHP (sourceOriginalPAllActualBands 20 L) := by
  filter_upwards [source_original_P_all_actual_local_eventually 20] with L hL
  intro D
  exact parity_original_assignment_mask_euler_le_HP434 _ D
    (fun g p hp => le_trans (by norm_num) (hL.2.1 g p hp)) hL.1

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalAssignmentEulerCorrection -/

section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Every prime divisor of the actual assignment product belongs to one
of its genuine selected Q or P factors, including repeated Q selections. -/
theorem parity_assignment_prime_divisor_alphabet434
    {T G : Type} [Fintype T] [Fintype G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ)
    (a : (j : T) → Fin r → {p // p ∈ Q j})
    (marks : (g : G) → {p // p ∈ P g})
    (hQ : ∀ j p, p ∈ Q j → p.Prime) (hP : ∀ g p, p ∈ P g → p.Prime)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ parityAssignmentModulus434 r Q P a marks) :
    (∃ j i, p = (a j i).val) ∨ (∃ g, p = (marks g).val) := by
  classical
  rcases (Nat.Prime.dvd_mul hp).mp hd with hq | hg
  · obtain ⟨j,hj,hjd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun j : T => ∏ i : Fin r, (a j i).val)).mp hq
    obtain ⟨i,hi,hid⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun i : Fin r => (a j i).val)).mp hjd
    exact Or.inl ⟨j,i,(Nat.prime_dvd_prime_iff_eq hp (hQ j _ (a j i).property)).mp hid⟩
  · obtain ⟨g,hg,hgd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun g : G => (marks g).val)).mp hg
    exact Or.inr ⟨g,(Nat.prime_dvd_prime_iff_eq hp (hP g _ (marks g).property)).mp hgd⟩

noncomputable def parityAssignmentEulerCorrection434 (D : ℕ) : ℝ :=
  ∏ p ∈ D.primeFactors, ((1-(p : ℝ)⁻¹)⁻¹)^3

theorem parity_assignment_euler_correction_le_exp434 (D : ℕ) :
    parityAssignmentEulerCorrection434 D ≤
      Real.exp (3 * ∑ p ∈ D.primeFactors, ((p : ℝ)-1)⁻¹) := by
  have hpoint (p : ℕ) (hp : p ∈ D.primeFactors) :
      ((1-(p : ℝ)⁻¹)⁻¹)^3 ≤ Real.exp (3*((p : ℝ)-1)⁻¹) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
    have hi : (1-(p : ℝ)⁻¹)⁻¹ = 1+((p : ℝ)-1)⁻¹ := by
      have hh : 1-(p : ℝ)⁻¹ = ((p : ℝ)-1)/(p : ℝ) := by
        field_simp <;> ring
      rw [hh, inv_div]
      field_simp <;> ring
    rw [hi]
    have hn : 0 ≤ 1+((p : ℝ)-1)⁻¹ := by
      exact add_nonneg (by norm_num) (inv_nonneg.mpr (by linarith))
    have he : 1+((p : ℝ)-1)⁻¹ ≤ Real.exp (((p : ℝ)-1)⁻¹) := by
      simpa only [add_comm] using Real.add_one_le_exp (((p : ℝ)-1)⁻¹)
    have hh := pow_le_pow_left₀ hn he 3
    convert hh using 1
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (((p : ℝ)-1)⁻¹) 3)
  calc
    _ ≤ ∏ p ∈ D.primeFactors, Real.exp (3*((p : ℝ)-1)⁻¹) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hunit : 0 ≤ 1-(p : ℝ)⁻¹ := by
          have h : (p : ℝ)⁻¹ ≤ (1 : ℝ)⁻¹ :=
            inv_anti₀ (by norm_num) (by linarith : (1 : ℝ) ≤ p)
          norm_num at h
          linarith
        exact pow_nonneg (inv_nonneg.mpr hunit) _
      · exact hpoint
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- The original rough integer reciprocal estimate makes the cubic
assignment Euler correction absolutely bounded already for L>=2. -/
theorem parity_rough_assignment_euler_correction_le_e434
    (D : ℕ) (L : ℝ) (hD : D ≠ 0) (hL : 2 ≤ L)
    (hupper : (D : ℝ) ≤ 2*Real.exp L)
    (hrough : ∀ p ∈ D.primeFactors, L^20 ≤ (p : ℝ)) :
    parityAssignmentEulerCorrection434 D ≤ Real.exp 1 := by
  have hrec := shift_two_prime_reciprocal_rough_bound D L hD hL hupper hrough
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog0 : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) hlog
  have hc : (12 : ℝ)/Real.log 2 ≤ 24 := (div_le_iff₀ hlog0).mpr (by linarith)
  have hp : (24 : ℝ) ≤ L^19 := by
    calc
      24 ≤ (2 : ℝ)^19 := by norm_num
      _ ≤ L^19 := pow_le_pow_left₀ (by norm_num) hL 19
  have hratio : ((12 : ℝ)/Real.log 2)*L/L^20 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hL0 20)).mpr
    calc
      _ ≤ 24*L := mul_le_mul_of_nonneg_right hc hL0.le
      _ ≤ L^19*L := mul_le_mul_of_nonneg_right hp hL0.le
      _ = _ := by rw [← pow_succ]; ring
  have hs : 3*(∑ p ∈ D.primeFactors, ((p : ℝ)-1)⁻¹) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hrec (show (0 : ℝ) ≤ 3 by norm_num)
    have he : (3 : ℝ)*((4/Real.log 2)*L/L^20) = (12/Real.log 2)*L/L^20 := by ring
    rw [he] at h
    exact h.trans hratio
  exact (parity_assignment_euler_correction_le_exp434 D).trans (Real.exp_le_exp.mpr hs)

/-- Actual literal-depth source assignments discharge roughness, positivity
and size; the original D1 correction has no logarithmic or L-power loss. -/
theorem parity_original_literal_assignment_euler_correction_eventually434 :
    ∀ᶠ L : ℝ in atTop,
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      ∀ (a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j})
      (marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g}),
      parityAssignmentEulerCorrection434 (parityAssignmentModulus434 20 Q P a marks) ≤ Real.exp 1 := by
  filter_upwards [source_shift_two_actual_band_roughness 20 (by norm_num),
    parity_original_assignment_modulus_size_eventually434,
    eventually_ge_atTop (2 : ℝ)] with L hrough hsize hL
  dsimp only
  intro a marks
  let d := sourceOriginalLiteralDepth 20 L
  let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
  let P := sourceOriginalPAllActualBands 20 L
  let D := parityAssignmentModulus434 20 Q P a marks
  apply parity_rough_assignment_euler_correction_le_e434 D L (Nat.ne_of_gt (hsize d a marks).1) hL
  · calc
      (D : ℝ) ≤ Real.exp (L/20) := (hsize d a marks).2
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2*Real.exp L := by linarith [Real.exp_pos L]
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    rcases parity_assignment_prime_divisor_alphabet434 20 Q P a marks
      (fun j p hp => source_original_Q_actual_prime 20 d L j.val p hp)
      (fun g p hp => source_original_P_all_actual_band_prime 20 L g p hp) p hpp hpd with hq | hg
    · obtain ⟨j,i,rfl⟩ := hq
      exact hrough.1 j.val _ (a j i).property
    · obtain ⟨g,rfl⟩ := hg
      exact hrough.2 g _ (marks g).property

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalLocalEulerComparison -/

section

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT

noncomputable def parityEulerTinyCorrection434 (p : ℕ) : ℝ :=
  1 / ((p : ℝ)*((p : ℝ)-1))

/-- Finite telescoping controls the convergent-product loss in original6.8. -/
theorem parity_finite_euler_tiny_sum_le_half434
    (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p) :
    (∑ p ∈ s, parityEulerTinyCorrection434 p) ≤ 1/2 := by
  classical
  let N := max 3 (s.sup id)
  have hN : 3 ≤ N := le_max_left _ _
  have hsub : s ⊆ Finset.Icc 3 N := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hs p hp,
      (Finset.le_sup (f := id) hp).trans (le_max_right _ _)⟩
  let f : ℕ → ℝ := fun k => -(1 : ℝ)/((k : ℝ)-1)
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 3 N) :
      parityEulerTinyCorrection434 k = f (k+1)-f k := by
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    have hk1 : (k : ℝ)-1 ≠ 0 := by linarith
    dsimp [parityEulerTinyCorrection434,f]
    push_cast
    simp only [add_sub_cancel_right]
    field_simp [hk0, hk1] <;> ring
  calc
    _ ≤ ∑ k ∈ Finset.Icc 3 N, parityEulerTinyCorrection434 k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k hk hks
        have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        unfold parityEulerTinyCorrection434
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
    _ = ∑ k ∈ Finset.Icc 3 N, (f (k+1)-f k) := Finset.sum_congr rfl hpoint
    _ = f (N+1)-f 3 := Finset.sum_Icc_sub hN f
    _ = (1/2 : ℝ)-(N : ℝ)⁻¹ := by
      dsimp [f]
      push_cast
      simp only [add_sub_cancel_right]
      ring
    _ ≤ 1/2 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem parity_finite_euler_tiny_product_le_exp_half434
    (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, (1+parityEulerTinyCorrection434 p)) ≤ Real.exp (1/2 : ℝ) := by
  calc
    _ ≤ ∏ p ∈ s, Real.exp (parityEulerTinyCorrection434 p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hs p hp
        exact add_nonneg (by norm_num)
          (div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (parityEulerTinyCorrection434 p)
    _ = Real.exp (∑ p ∈ s, parityEulerTinyCorrection434 p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (parity_finite_euler_tiny_sum_le_half434 s hs)

/-- The actual product-two local factors compared to the source Euler
factors. No universal distribution or sieve assertion is a premise. -/
theorem parity_original_local_euler_majorant434
    (p : ℕ) (hp : 3 ≤ p) (rough banned : Bool) :
    1-parityOriginalShiftTwoBoxDensity434 (fun _ => rough) (fun _ => banned) p ≤
      (if rough then (1-(p : ℝ)⁻¹)^2 else 1) *
      (if banned then 1-(p : ℝ)⁻¹ else 1) *
      (1+parityEulerTinyCorrection434 p) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  have h1 : 1 ≤ p := by omega
  have h2 : 1 ≤ 2*p := by omega
  let v : ℝ := 1-(p : ℝ)⁻¹
  have hv : 0 ≤ v := by
    have hh : (p : ℝ)⁻¹ ≤ (1 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith : (1 : ℝ) ≤ p)
    norm_num at hh
    dsimp [v]
    linarith
  have ht : 0 ≤ parityEulerTinyCorrection434 p :=
    div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hTF : 1-parityOriginalShiftTwoBoxDensity434 (fun _ => true) (fun _ => false) p = v^2 := by
    norm_num [parityOriginalShiftTwoBoxDensity434,localNu,Nat.cast_sub h1,Nat.cast_sub h2,v]
    <;> field_simp
    <;> ring
  have hFT : 1-parityOriginalShiftTwoBoxDensity434 (fun _ => false) (fun _ => true) p =
      v*(1+parityEulerTinyCorrection434 p) := by
    norm_num [parityOriginalShiftTwoBoxDensity434,localNu,Nat.cast_sub h1,Nat.cast_sub h2,
      v,parityEulerTinyCorrection434]
    <;> field_simp
    <;> ring
  have hTT : 1-parityOriginalShiftTwoBoxDensity434 (fun _ => true) (fun _ => true) p ≤ v^3 := by
    have he : 1-parityOriginalShiftTwoBoxDensity434 (fun _ => true) (fun _ => true) p =
        v*(1-2*(p : ℝ)⁻¹) := by
      norm_num [parityOriginalShiftTwoBoxDensity434,localNu,Nat.cast_sub h1,Nat.cast_sub h2,v]
      <;> field_simp
      <;> ring
    rw [he]
    have hsmall : 1-2*(p : ℝ)⁻¹ ≤ v^2 := by
      dsimp [v]
      nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
    calc
      _ ≤ v*v^2 := mul_le_mul_of_nonneg_left hsmall hv
      _ = v^3 := by ring
  cases rough <;> cases banned
  · norm_num [parityOriginalShiftTwoBoxDensity434,localNu]
    exact ht
  · simpa only [Bool.false_eq_true, ite_false, ite_true, one_mul] using hFT.le
  · have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1+parityEulerTinyCorrection434 p by linarith)
      (sq_nonneg v)
    simpa only [ite_true, Bool.false_eq_true, ite_false, mul_one, hTF] using hh
  · have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1+parityEulerTinyCorrection434 p by linarith)
      (pow_nonneg hv 3)
    have hh' := hTT.trans (by simpa only [mul_one] using hh)
    simpa only [ite_true, pow_succ, v] using hh'

end Green64Analytic.SourceCRT

end

/-! ## OriginalCompleteMaskAlphabet -/

section

set_option maxHeartbeats 1400000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Completed natural half-power blocks give exactly the odd primes up to
the original mask cutoff which do not divide the full assignment modulus. -/
theorem parity_original_complete_odd_blocks434
    (J D : ℕ) (z : ℝ) (hz : 1 < z) (hLast : z^((1/2 : ℝ)^J) < 3) :
    (Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)) =
      (sourceAllOddPrimeSet z).filter (fun p => ¬ p ∣ D) := by
  classical
  ext p
  constructor
  · intro hp
    have ha := source_natural_blocks_subset_all_odd J D z hp
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    have hprime := (source_natural_block_prime D z j.val p hpj).1
    have hcop := source_natural_block_coprime D z j.val p hpj
    exact Finset.mem_filter.mpr ⟨ha, hprime.coprime_iff_not_dvd.mp hcop.symm⟩
  · intro hp
    obtain ⟨ha,hnD⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp ha).2
    exact source_natural_blocks_cover_coprime J D z hz hLast p ha
      (hprime.coprime_iff_not_dvd.mpr hnD).symm

/-- Exact original deterministic-plus-random ban semantics on the actual
complete sieve alphabet. S is the allowed set, not the banned set. -/
theorem parity_original_mask_on_complete_odd_blocks434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (J D : ℕ) (z : ℝ) (hz : 1 < z) (hLast : z^((1/2 : ℝ)^J) < 3)
    (hP : ∀ g p, p ∈ P g → p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ z)
    (S : Finset ℕ) (hS : S ⊆ parityAssignmentMaskUniverse434 P D) :
    S ⊆ Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val) ∧
    ∀ p ∈ Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val),
      (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪
        (parityAssignmentMaskUniverse434 P D \ S) ↔ p ∉ S) := by
  classical
  rw [parity_original_complete_odd_blocks434 J D z hz hLast]
  constructor
  · intro p hp
    obtain ⟨hpP,hnD⟩ := Finset.mem_filter.mp (hS hp)
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hpP
    have hh := hP g p hpg
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hh.2.1,Nat.le_floor hh.2.2⟩,hh.1⟩,hnD⟩
  · intro p hp
    obtain ⟨hpOdd,hnD⟩ := Finset.mem_filter.mp hp
    by_cases hpP : p ∈ Finset.univ.biUnion P
    · have hpU : p ∈ parityAssignmentMaskUniverse434 P D :=
        Finset.mem_filter.mpr ⟨hpP,hnD⟩
      have hnDet : p ∉ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D := by
        intro hd
        exact (Finset.mem_filter.mp hd).2.1 hpP
      simp only [Finset.mem_union, Finset.mem_sdiff, hpU, hnDet, false_or, true_and]
    · have hpDet : p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D :=
        Finset.mem_filter.mpr ⟨hpOdd,hpP,hnD⟩
      have hnS : p ∉ S := by
        intro hs
        exact hpP (Finset.mem_filter.mp (hS hs)).1
      simp only [Finset.mem_union, hpDet, true_or, hnS, not_false_eq_true]

/-- One block count, chosen after the actual L-dependent cutoff, works
uniformly for every assignment modulus and every original half mask.
This block count is unrelated to the fixed nonsmooth-proxy parameter J. -/
theorem parity_original_actual_complete_mask_alphabet_eventually434 :
    ∀ᶠ L : ℝ in atTop,
      let P := sourceOriginalPAllActualBands 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434 * L)
      ∃ blockCount : ℕ, z^((1/2 : ℝ)^blockCount) < 3 ∧
        ∀ (D : ℕ) (S : Finset ℕ), S ⊆ parityAssignmentMaskUniverse434 P D →
          S ⊆ Finset.univ.biUnion
            (fun j : Fin blockCount => sourceNaturalOddPrimeBlock D z j.val) ∧
          ∀ p ∈ Finset.univ.biUnion
            (fun j : Fin blockCount => sourceNaturalOddPrimeBlock D z j.val),
            (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪
              (parityAssignmentMaskUniverse434 P D \ S) ↔ p ∉ S) := by
  filter_upwards [source_original_P_all_actual_local_eventually 20,
    parity_original_assignment_P_below_mask_cutoff_eventually434,
    eventually_gt_atTop (0 : ℝ)] with L hP hcut hL
  dsimp only
  have htheta : 0 < parityOriginalAssignmentTheta434 := by norm_num [parityOriginalAssignmentTheta434]
  have hz : 1 < Real.exp (parityOriginalAssignmentTheta434*L) :=
    Real.one_lt_exp_iff.mpr (mul_pos htheta hL)
  obtain ⟨J,hJ⟩ := source_exists_natural_halfpower_depth
    (Real.exp (parityOriginalAssignmentTheta434*L)) hz
  refine ⟨J,hJ,?_⟩
  intro D S hS
  exact parity_original_mask_on_complete_odd_blocks434 (sourceOriginalPAllActualBands 20 L)
    J D (Real.exp (parityOriginalAssignmentTheta434*L)) hz hJ
    (fun g p hp => ⟨source_original_P_all_actual_band_prime 20 L g p hp,
      le_trans (by norm_num) (hP.2.1 g p hp),hcut g p hp⟩) S hS

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalCompleteMaskEulerJoin -/

section

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT
open SourceBlockSieve

/-- Baseline on the exact odd alphabet remaining after the full D1 deletion.
Its conversion to the full V(W)^2 V(z) product is a separate statement. -/
noncomputable def parityOriginalOddEulerBaseline434 (P : Finset ℕ) (W : ℝ) : ℝ :=
  ∏ p ∈ P, (if (p : ℝ) ≤ W then (1-(p : ℝ)⁻¹)^2 else 1) * (1-(p : ℝ)⁻¹)

theorem parity_original_odd_euler_baseline_nonneg434
    (P : Finset ℕ) (W : ℝ) (hP : ∀ p ∈ P, 3 ≤ p) :
    0 ≤ parityOriginalOddEulerBaseline434 P W := by
  apply Finset.prod_nonneg
  intro p hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hP p hp
  have hi : (p : ℝ)⁻¹ ≤ (1 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith : (1 : ℝ) ≤ p)
  norm_num at hi
  apply mul_nonneg
  · split_ifs <;> positivity
  · linarith

/-- Finite product comparison for actual product-two local densities, with
the allowed set S and a convergent correction bounded independently of P. -/
theorem parity_original_allowed_odd_euler_product434
    (P S : Finset ℕ) (W : ℝ) (hP : ∀ p ∈ P, 3 ≤ p) (hS : S ⊆ P) :
    (∏ p ∈ P, (1-parityOriginalShiftTwoBoxDensity434
      (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∉ S)) p)) ≤
    Real.exp (1/2 : ℝ) * parityOriginalOddEulerBaseline434 P W *
      ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹ := by
  classical
  let F := fun p : ℕ => (if (p : ℝ) ≤ W then (1-(p : ℝ)⁻¹)^2 else 1) * (1-(p : ℝ)⁻¹)
  let G := fun p : ℕ => if p ∈ S then (1-(p : ℝ)⁻¹)⁻¹ else 1
  have hv (p : ℕ) (hp : p ∈ P) : 0 < 1-(p : ℝ)⁻¹ := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hi : (p : ℝ)⁻¹ < (1 : ℝ)⁻¹ :=
      inv_strictAnti₀ (by norm_num) (by linarith : (1 : ℝ) < p)
    norm_num at hi
    linarith
  have hFG : 0 ≤ (∏ p ∈ P, F p) * ∏ p ∈ P, G p := by
    apply mul_nonneg
    · exact parity_original_odd_euler_baseline_nonneg434 P W hP
    · apply Finset.prod_nonneg
      intro p hp
      dsimp [G]
      split_ifs
      · exact inv_nonneg.mpr (hv p hp).le
      · norm_num
  have hprodG : (∏ p ∈ P, G p) = ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹ := by
    dsimp [G]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hS]
  calc
    _ ≤ ∏ p ∈ P, (F p * G p) * (1+parityEulerTinyCorrection434 p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        change 0 ≤ 1-(localNu p (decide ((p : ℝ) ≤ W)) (decide (p ∉ S)) : ℝ)/(p : ℝ)^2
        have hh := local_density_le_seven_ninths p (hP p hp)
          (decide ((p : ℝ) ≤ W)) (decide (p ∉ S))
        linarith
      · intro p hp
        have hh := parity_original_local_euler_majorant434 p (hP p hp)
          (decide ((p : ℝ) ≤ W)) (decide (p ∉ S))
        change 1-parityOriginalShiftTwoBoxDensity434
          (fun _ => decide ((p : ℝ) ≤ W)) (fun _ => decide (p ∉ S)) p ≤ _
        by_cases hpS : p ∈ S
        · have he : F p * G p =
              (if (p : ℝ) ≤ W then (1-(p : ℝ)⁻¹)^2 else 1) := by
            dsimp [F,G]
            rw [if_pos hpS, mul_assoc, mul_inv_cancel₀ (hv p hp).ne', mul_one]
          rw [he]
          simpa only [hpS, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
            mul_one, decide_eq_true_eq] using hh
        · simpa only [F,G,hpS,not_false_eq_true,decide_true,ite_true,ite_false,mul_one,
            decide_eq_true_eq] using hh
    _ = ((∏ p ∈ P, F p) * ∏ p ∈ P, G p) *
        ∏ p ∈ P, (1+parityEulerTinyCorrection434 p) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ ((∏ p ∈ P, F p) * ∏ p ∈ P, G p) * Real.exp (1/2 : ℝ) :=
      mul_le_mul_of_nonneg_left (parity_finite_euler_tiny_product_le_exp_half434 P hP) hFG
    _ = _ := by rw [hprodG]; change _ = Real.exp (1/2 : ℝ) * (∏ p ∈ P, F p) * _; ring

/-- The real deterministic-plus-half-mask Euler average on complete original
blocks. It is bounded by the odd D1-deleted baseline times the original H_P.
This proves the source mask join, not the later complete Euler normalization. -/
theorem parity_original_complete_mask_euler_average434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (J D : ℕ) (z W : ℝ) (hz : 1 < z) (hLast : z^((1/2 : ℝ)^J) < 3)
    (hP : ∀ g p, p ∈ P g → p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ z)
    (hPn : ∀ g, (P g).Nonempty) :
    let PP := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
    let U := parityAssignmentMaskUniverse434 P D
    (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
      ∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
        (fun p => decide ((p : ℝ) ≤ W))
        (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪ (U \ S))) p)) ≤
    Real.exp (1/2 : ℝ) * parityOriginalOddEulerBaseline434 PP W * sourceLiteralHP P := by
  classical
  dsimp only
  let PP := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
  let U := parityAssignmentMaskUniverse434 P D
  have hPP (p : ℕ) (hp : p ∈ PP) : 3 ≤ p := by
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    have hprime := (source_natural_block_prime D z j.val p hpj).1
    have hodd := source_natural_block_odd D z j.val p hpj
    have htwo := hprime.two_le
    omega
  have hpoint (S : Finset ℕ) (hS : S ∈ U.powerset) :
      (∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
        (fun p => decide ((p : ℝ) ≤ W))
        (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪ (U \ S))) p)) ≤
      Real.exp (1/2 : ℝ) * parityOriginalOddEulerBaseline434 PP W *
        ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹ := by
    have hs := parity_original_mask_on_complete_odd_blocks434 P J D z hz hLast hP
      S (Finset.mem_powerset.mp hS)
    have he :
        (∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
          (fun p => decide ((p : ℝ) ≤ W))
          (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪ (U \ S))) p)) =
        ∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
          (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∉ S)) p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [parityOriginalShiftTwoBoxDensity434, U, hs.2 p hp]
    rw [he]
    exact parity_original_allowed_odd_euler_product434 PP S W hPP hs.1
  calc
    _ ≤ ∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
        (Real.exp (1/2 : ℝ) * parityOriginalOddEulerBaseline434 PP W *
          ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹) :=
      Finset.sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left (hpoint S hS) (by positivity))
    _ = (Real.exp (1/2 : ℝ) * parityOriginalOddEulerBaseline434 PP W) *
        ∑ S ∈ U.powerset, (1/2 : ℝ)^U.card * ∏ p ∈ S, (1-(p : ℝ)⁻¹)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (parity_original_assignment_mask_euler_le_HP434 P D (fun g p hp => (hP g p hp).2.1) hPn)
      (mul_nonneg (Real.exp_pos _).le (parity_original_odd_euler_baseline_nonneg434 PP W hPP))

end Green64Analytic.SourceCRT

end

/-! ## OriginalFullEulerNormalization -/

section

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT
open SourceBlockSieve

/-- Deleting full assignment divisors costs at most the cubic distinct-prime
correction. No squarefreeness or coprimality with two is imposed on D. -/
theorem parity_original_odd_baseline_delete_modulus434
    (P : Finset ℕ) (W : ℝ) (D : ℕ) (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) :
    parityOriginalOddEulerBaseline434 (P.filter (fun p => ¬ p ∣ D)) W ≤
      parityOriginalOddEulerBaseline434 P W * parityAssignmentEulerCorrection434 D := by
  classical
  let F := fun p : ℕ => (if (p : ℝ) ≤ W then (1-(p : ℝ)⁻¹)^2 else 1) * (1-(p : ℝ)⁻¹)
  let C := fun p : ℕ => ((1-(p : ℝ)⁻¹)⁻¹)^3
  let R := P.filter (fun p => p ∣ D)
  let K := P.filter (fun p => ¬ p ∣ D)
  have hv (p : ℕ) (hp : p.Prime) : 0 < 1-(p : ℝ)⁻¹ ∧ 1-(p : ℝ)⁻¹ ≤ 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hi : (p : ℝ)⁻¹ < (1 : ℝ)⁻¹ :=
      inv_strictAnti₀ (by norm_num) (by linarith : (1 : ℝ) < p)
    have hn : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    norm_num at hi
    constructor <;> linarith
  have hc (p : ℕ) (hp : p.Prime) : 1 ≤ C p := by
    have h := hv p hp
    have hi := inv_anti₀ h.1 h.2
    norm_num at hi
    simpa only [C, one_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hi 3
  have hfc (p : ℕ) (hp : p ∈ P) : 1 ≤ F p * C p := by
    let v := 1-(p : ℝ)⁻¹
    have hv0 : v ≠ 0 := (hv p (hP p hp).1).1.ne'
    have hi : 1 ≤ v⁻¹ := by
      have hh := inv_anti₀ (hv p (hP p hp).1).1 (hv p (hP p hp).1).2
      norm_num at hh
      exact hh
    by_cases hw : (p : ℝ) ≤ W
    · change 1 ≤ (if (p : ℝ) ≤ W then v^2 else 1)*v*(v⁻¹)^3
      rw [if_pos hw]
      have he : v^2*v*(v⁻¹)^3 = (v*v⁻¹)^3 := by ring
      rw [he,mul_inv_cancel₀ hv0]
      norm_num
    · change 1 ≤ (if (p : ℝ) ≤ W then v^2 else 1)*v*(v⁻¹)^3
      rw [if_neg hw,one_mul]
      have he : v*(v⁻¹)^3 = (v*v⁻¹)*(v⁻¹)^2 := by ring
      rw [he,mul_inv_cancel₀ hv0,one_mul]
      simpa only [one_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hi 2
  have hK0 : 0 ≤ ∏ p ∈ K, F p :=
    parity_original_odd_euler_baseline_nonneg434 K W
      (fun p hp => (hP p (Finset.mem_filter.mp hp).1).2)
  have hP0 : 0 ≤ ∏ p ∈ P, F p :=
    parity_original_odd_euler_baseline_nonneg434 P W (fun p hp => (hP p hp).2)
  have hR : R ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨hpP,hd⟩ := Finset.mem_filter.mp hp
    exact (hP p hpP).1.mem_primeFactors hd hD.ne'
  have hC : (∏ p ∈ R, C p) ≤ parityAssignmentEulerCorrection434 D := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hR
    · intro p hp
      exact (show (0 : ℝ) ≤ 1 by norm_num).trans (hc p (hP p (Finset.mem_filter.mp hp).1).1)
    · intro p hp hnot
      exact hc p (Nat.prime_of_mem_primeFactors hp)
  calc
    _ = (∏ p ∈ K, F p)*1 := by change _ = _; simp [parityOriginalOddEulerBaseline434,K,F]
    _ ≤ (∏ p ∈ K, F p) * ∏ p ∈ R, (F p*C p) :=
      mul_le_mul_of_nonneg_left (Finset.one_le_prod₀
        (fun p hp => hfc p (Finset.mem_filter.mp hp).1)) hK0
    _ = ((∏ p ∈ K, F p)*(∏ p ∈ R, F p)) * ∏ p ∈ R, C p := by
      have hr : (∏ p ∈ R, F p*C p) = (∏ p ∈ R, F p)*(∏ p ∈ R, C p) := by
        rw [Finset.prod_mul_distrib]
      rw [hr]
      ring
    _ = (∏ p ∈ P, F p) * ∏ p ∈ R, C p := by
      rw [Finset.prod_filter_not_mul_prod_filter P (fun p => p ∣ D) F]
    _ ≤ _ := mul_le_mul_of_nonneg_left hC hP0

/-- Exact source Euler normalization, including the closed rough cutoff
and the factor eight from deleting the prime two from three Euler powers. -/
theorem parity_original_full_odd_euler_baseline434
    (W z : ℝ) (hW : 2 ≤ W) (hWz : W ≤ z) :
    parityOriginalOddEulerBaseline434 (sourceAllOddPrimeSet z) W =
      8 * (sourceNaturalEuler ⌊W⌋₊)^2 * sourceNaturalEuler ⌊z⌋₊ := by
  classical
  let T := fun N : ℕ => (Finset.range (N+1)).filter Nat.Prime
  let F := fun p : ℕ => (if (p : ℝ) ≤ W then (1-(p : ℝ)⁻¹)^2 else 1) * (1-(p : ℝ)⁻¹)
  have hfloor : ⌊W⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono hWz
  have hfilt : (T ⌊z⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ W) = T ⌊W⌋₊ := by
    ext p
    simp only [T,Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨⟨hpz,hprime⟩,hpW⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpW),hprime⟩
    · rintro ⟨hpW,hprime⟩
      have hl : p ≤ ⌊W⌋₊ := Nat.le_of_lt_succ hpW
      exact ⟨⟨Nat.lt_succ_of_le (hl.trans hfloor),hprime⟩,
        (Nat.le_floor_iff' hprime.ne_zero).mp hl⟩
  have hfull : (∏ p ∈ T ⌊z⌋₊, F p) =
      (sourceNaturalEuler ⌊W⌋₊)^2 * sourceNaturalEuler ⌊z⌋₊ := by
    dsimp [F]
    rw [Finset.prod_mul_distrib,← Finset.prod_filter,hfilt,Finset.prod_pow]
    rfl
  have hodd : sourceAllOddPrimeSet z = (T ⌊z⌋₊).erase 2 := by
    ext p
    simp only [sourceAllOddPrimeSet,T,Finset.mem_filter,Finset.mem_Icc,
      Finset.mem_erase,Finset.mem_range]
    constructor
    · rintro ⟨⟨h3,hpz⟩,hprime⟩
      exact ⟨by omega,Nat.lt_succ_of_le hpz,hprime⟩
    · rintro ⟨hne,hpz,hprime⟩
      have htwo := hprime.two_le
      exact ⟨⟨by omega,Nat.le_of_lt_succ hpz⟩,hprime⟩
  have hmem : 2 ∈ T ⌊z⌋₊ := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_floor (hW.trans hWz))),Nat.prime_two⟩
  have hF2 : F 2 = (1/8 : ℝ) := by
    norm_num [F,if_pos hW]
  have he := Finset.mul_prod_erase (T ⌊z⌋₊) F hmem
  rw [hF2,←hodd,hfull] at he
  change (∏ p ∈ sourceAllOddPrimeSet z, F p) = _
  linarith

theorem parity_original_full_deleted_euler_baseline434
    (W z : ℝ) (D : ℕ) (hW : 2 ≤ W) (hWz : W ≤ z) (hD : 0 < D) :
    parityOriginalOddEulerBaseline434
      ((sourceAllOddPrimeSet z).filter (fun p => ¬ p ∣ D)) W ≤
      (8 * (sourceNaturalEuler ⌊W⌋₊)^2 * sourceNaturalEuler ⌊z⌋₊) *
        parityAssignmentEulerCorrection434 D := by
  have h := parity_original_odd_baseline_delete_modulus434 (sourceAllOddPrimeSet z) W D hD
    (fun p hp => ⟨(Finset.mem_filter.mp hp).2,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩)
  rw [parity_original_full_odd_euler_baseline434 W z hW hWz] at h
  exact h

/-- Full finite original (6.8) mask-average comparison for h=-2. All actual
ban semantics, complete blocks and prime-two/D1 Euler corrections are proved. -/
theorem parity_original_full_mask_euler_average434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (J D : ℕ) (z W : ℝ) (hW : 2 ≤ W) (hWz : W ≤ z) (hD : 0 < D)
    (hLast : z^((1/2 : ℝ)^J) < 3)
    (hP : ∀ g p, p ∈ P g → p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ z)
    (hPn : ∀ g, (P g).Nonempty) :
    let PP := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
    let U := parityAssignmentMaskUniverse434 P D
    (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
      ∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
        (fun p => decide ((p : ℝ) ≤ W))
        (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪ (U \ S))) p)) ≤
    Real.exp (1/2 : ℝ) *
      ((8 * (sourceNaturalEuler ⌊W⌋₊)^2 * sourceNaturalEuler ⌊z⌋₊) *
        parityAssignmentEulerCorrection434 D) * sourceLiteralHP P := by
  have hz : 1 < z := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hW.trans hWz)
  have h := parity_original_complete_mask_euler_average434 P J D z W hz hLast hP hPn
  dsimp only at h ⊢
  have he := parity_original_full_deleted_euler_baseline434 W z D hW hWz hD
  rw [←parity_original_complete_odd_blocks434 J D z hz hLast] at he
  have hHP : 0 ≤ sourceLiteralHP P :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (source_literal_HP_one_le P (fun g p hp => (hP g p hp).2.1) hPn)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le) hHP)

end Green64Analytic.SourceCRT

end

/-! ## OriginalNormalizedBoxMain -/

section

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem parity_original_box_mass_le_area_div434 (D A B C E : ℕ) (hD : 0 < D) :
    parityOriginalShiftTwoBoxMass434 D A B C E ≤
      (((B-A : ℕ) : ℝ)*((E-C : ℕ) : ℝ))/(D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have ht : (D.totient : ℝ) ≤ D := by exact_mod_cast Nat.totient_le D
  unfold parityOriginalShiftTwoBoxMass434
  calc
    _ ≤ (D : ℝ)*((B-A : ℕ) : ℝ)*((E-C : ℕ) : ℝ)/(D : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

/-- Explicit normalized upper main term; the fixed factors are
200^400 * 8 * exp(3/2+rho_2), independent of the source scale. -/
noncomputable def parityOriginalNormalizedBoxMainBound434
    (d : ℕ) (L W : ℝ) (A B C E : ℕ) : ℝ :=
  (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L *
    ((((B-A : ℕ) : ℝ)*((E-C : ℕ) : ℝ)) * Real.exp (parityOriginalShiftTwoSieveRho434 2) *
      (Real.exp (1/2 : ℝ) *
        ((8*(sourceNaturalEuler ⌊W⌋₊)^2 *
          sourceNaturalEuler ⌊Real.exp (parityOriginalAssignmentTheta434*L)⌋₊) * Real.exp 1) *
        sourceLiteralHP (sourceOriginalPAllActualBands 20 L)))

/-- All actual assignments are summed with their original factorial and
P-mark normalization. The source reciprocal moment and bounded full-D1
correction discharge the entire normalized Euler main average. -/
theorem parity_original_literal_box_main_normalized434 :
    ∀ᶠ L : ℝ in atTop,
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434*L)
      ∃ J : ℕ, z^((1/2 : ℝ)^J) < 3 ∧
        ∀ W : ℝ, 2 ≤ W → W ≤ z → ∀ A B C E : ℕ,
          parityOriginalAssignmentBoxMainAverage434 20 Q P z W J A B C E ≤
            parityOriginalNormalizedBoxMainBound434 d L W A B C E := by
  filter_upwards [parity_original_literal_assignment_three_moments434,
    parity_original_literal_assignment_euler_correction_eventually434,
    source_original_P_all_actual_local_eventually 20,
    parity_original_assignment_P_below_mask_cutoff_eventually434,
    eventually_gt_atTop (0 : ℝ)] with L hmom hcorr hPlocal hcut hL
  dsimp only at hmom hcorr ⊢
  let d := sourceOriginalLiteralDepth 20 L
  let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
  let P := sourceOriginalPAllActualBands 20 L
  let z := Real.exp (parityOriginalAssignmentTheta434*L)
  have hz : 1 < z := Real.one_lt_exp_iff.mpr
    (mul_pos (by norm_num [parityOriginalAssignmentTheta434]) hL)
  obtain ⟨J,hJ⟩ := source_exists_natural_halfpower_depth z hz
  refine ⟨J,hJ,?_⟩
  intro W hW hWz A B C E
  let area : ℝ := ((B-A : ℕ) : ℝ)*((E-C : ℕ) : ℝ)
  let ee := Real.exp (parityOriginalShiftTwoSieveRho434 2)
  let K : ℝ := 8*(sourceNaturalEuler ⌊W⌋₊)^2*sourceNaturalEuler ⌊z⌋₊
  let C0 : ℝ := Real.exp (1/2 : ℝ)*(K*Real.exp 1)*sourceLiteralHP P
  have hEuler (N : ℕ) : 0 ≤ sourceNaturalEuler N := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hi := inv_anti₀ (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ p by linarith)
    norm_num at hi
    linarith
  have hHP : 0 ≤ sourceLiteralHP P := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (source_literal_HP_one_le P (fun g p hp => le_trans (by norm_num) (hPlocal.2.1 g p hp)) hPlocal.1)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hEuler _)
  have hC : 0 ≤ C0 := mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg hK (Real.exp_pos _).le)) hHP
  have harea : 0 ≤ area := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hee : 0 ≤ ee := (Real.exp_pos _).le
  have heta := parity_assignment_normalization_nonneg434 (parityOriginalAssignmentTail434 d) 20 P
  unfold parityOriginalAssignmentBoxMainAverage434
  calc
    _ ≤ ∑ a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j},
        ∑ marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g},
          (parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P /
            (parityAssignmentModulus434 20 Q P a marks : ℝ)) * (area*ee*C0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro marks hm
      let D := parityAssignmentModulus434 20 Q P a marks
      let U := parityAssignmentMaskUniverse434 P D
      let PP := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
      let good := fun S : Finset ℕ =>
        ∏ p ∈ PP, (1-parityOriginalShiftTwoBoxDensity434
          (fun p => decide ((p : ℝ) ≤ W))
          (fun p => decide (p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪ (U \ S))) p)
      have hfull := parity_original_full_mask_euler_average434 P J D z W hW hWz
        (hmom.1 a marks).1 hJ
        (fun g p hp => ⟨source_original_P_all_actual_band_prime 20 L g p hp,
          le_trans (by norm_num) (hPlocal.2.1 g p hp),hcut g p hp⟩) hPlocal.1
      have havg : (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card*good S) ≤ C0 := by
        exact hfull.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcorr a marks) hK)
            (Real.exp_pos _).le) hHP)
      have hmass0 : 0 ≤ parityOriginalShiftTwoBoxMass434 D A B C E := by
        unfold parityOriginalShiftTwoBoxMass434
        positivity
      have hmass := parity_original_box_mass_le_area_div434 D A B C E (hmom.1 a marks).1
      have hi :
          (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
            (parityOriginalShiftTwoBoxMass434 D A B C E * good S * ee)) =
          (parityOriginalShiftTwoBoxMass434 D A B C E * ee) *
            ∑ S ∈ U.powerset, (1/2 : ℝ)^U.card*good S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      change parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P *
        (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
          (parityOriginalShiftTwoBoxMass434 D A B C E * good S * ee)) ≤ _
      rw [hi]
      calc
        _ ≤ parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P *
            ((parityOriginalShiftTwoBoxMass434 D A B C E * ee)*C0) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left havg (mul_nonneg hmass0 hee)) heta
        _ ≤ parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P *
            (((area/(D : ℝ))*ee)*C0) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass hee) hC) heta
        _ = _ := by ring
    _ = (∑ a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j},
        ∑ marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g},
          parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P /
            (parityAssignmentModulus434 20 Q P a marks : ℝ)) * (area*ee*C0) := by
      simp only [Finset.sum_mul]
    _ ≤ ((200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L)*(area*ee*C0) :=
      mul_le_mul_of_nonneg_right hmom.2.1 (mul_nonneg (mul_nonneg harea hee) hC)
    _ = _ := rfl

/-- The genuine original A_rho Psi source has a fully normalized Euler main
bound and the proved finite total assignment error. The analytic conversion
to Xrho and the vanishing remainder are deliberately not assumptions here. -/
theorem parity_original_literal_weighted_box_normalized434 :
    ∀ᶠ L : ℝ in atTop,
      ∃ J : ℕ,
      ∀ (rho : ℝ), |rho| ≤ 1 →
      ∀ (Psi : ℝ → ℝ), Psi 0 = 0 → (∀ x, 0 ≤ Psi x) → (∀ x, Psi x ≤ 1) →
      ∀ (W : ℝ), 2 ≤ W → W ≤ Real.exp (parityOriginalAssignmentTheta434*L) →
      ∀ (K N : Finset ℕ) (A B C E Y : ℕ),
      K ⊆ Finset.Ico A B → N ⊆ Finset.Ico C E → A ≤ B → C ≤ E →
      let d := sourceOriginalLiteralDepth 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434*L)
      let Z := ⌊z^(10 : ℝ)⌋₊
      (∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u : ℝ)/Real.exp L)) *
          ∑ xy ∈ parityOriginalShiftTwoPositivePairFibre434 K N u,
            if sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2 then (1 : ℝ) else 0) ≤
      parityOriginalNormalizedBoxMainBound434 d L W A B C E +
      (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L *
        (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) * Real.exp (L/20) +
          4 * (Z : ℝ)^2 * Real.exp (L/10)) * (1+Real.log (Z : ℝ))^3 := by
  filter_upwards [parity_original_literal_box_main_normalized434,
    parity_original_literal_weighted_box_sieve434] with L hmain hsource
  obtain ⟨J,hJ,hm⟩ := hmain
  refine ⟨J,?_⟩
  intro rho hrho Psi hPsi0 hPsiNonneg hPsiOne W hW hWz K N A B C E Y hK hN hAB hCE
  exact (hsource rho hrho Psi hPsi0 hPsiNonneg hPsiOne W K N J A B C E Y hK hN hAB hCE).trans
    (add_le_add (hm W hW hWz A B C E) le_rfl)

end Green64Analytic.Parity

end

