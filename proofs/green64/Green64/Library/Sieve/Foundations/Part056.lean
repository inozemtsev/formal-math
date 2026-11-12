module

public import Green64.Localization
public import Green64.Library.Analysis.Estimates.Part006
public import Green64.Library.Sieve.Foundations.Part054
public import Green64.Library.Sieve.Foundations.FrozenDensityMesh
public import Green64.Library.Sieve.Foundations.Part055
public import Green64.Library.Sieve.Foundations.Part002
public import Green64.Library.Weights.Part035
public import Green64.Library.Weights.Part105
public import Green64.Library.Weights.Part109
public import Green64.Library.Sieve.Foundations.Part005
public import Green64.Library.Correlation.Part032
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Weights.Part100
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Weights.Part111
public import Green64.Library.Weights.Part102
public import Green64.Library.Sieve.Foundations.PresieveBlocks

@[expose] public section

/-!
# Sieve / Foundations / Part056

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalBalancedDoubleRoughBridge -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The genuine weighted ordered double-W-rough balanced pair mass.
It uses exactly the original positive fibre m*n=u+2, both closed B_kappa
factor restrictions, the original parity coefficient and the original Psi.
The diagonal is retained. No box-count or sieve estimate is in this definition. -/
def balancedRoughPairMass
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (kappa : ℝ) (Y : ℕ) : ℝ :=
  ∑ u∈Finset.range (Y+1),
    (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L))*
    ∑ z∈parityOriginalShiftTwoPositivePairFibre434
      ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
      ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa)) u,
      if sourceD20Rough (Real.exp (Real.sqrt L)) z.1 ∧
        sourceD20Rough (Real.exp (Real.sqrt L)) z.2 then (1:ℝ) else 0

theorem parity_original_fullcell_prime_proxy_support434
    (L S gamma : ℝ) (a b n : ℕ)
    (hne : (parityOriginalFullCellCoefficient434 true true L S gamma a b n).re≠0) :
    sourceD20Rough (Real.exp (Real.sqrt L)) n := by
  by_contra hRough
  apply hne
  simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,
    b627PrimeFullProxy434,hRough]

/-- The existing Cpr=3 bound applies on the actual original closed B_kappa
carrier. The constant is independent of kappa, gamma, Y and S; the eventual
threshold only depends on the already fixed S. -/
theorem parity_original_balanced_fullcell_prime_cap434
    (S : ℝ) (hS : 0<S) :
    ∀ᶠ L : ℝ in atTop,∀ (kappa gamma : ℝ) (Y n : ℕ),
      kappa<1/50 →
      n∈((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa)) →
      0≤(parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) n).re ∧
      (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) n).re≤
        3/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  filter_upwards [b631_actual_prime_fine_density_uniform_constant434 S hS,
    eventually_gt_atTop (0:ℝ)] with L hDensity hL kappa gamma Y n hKappa hn
  have hIn := (Finset.mem_filter.mp hn).1
  have hBal := (Finset.mem_filter.mp hn).2
  have hLow : Real.exp ((2/5:ℝ)*L)≤(n:ℝ) :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by linarith : (2/5:ℝ)≤1/2-2*kappa) hL.le)).trans hBal.1
  have hExact :
      parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) n=
        ((b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n:ℝ):ℂ) := by
    simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,hIn]
  simpa only [hExact,Complex.ofReal_re] using hDensity n hLow

/-- Exact real source expression for the two original full-cell prime
proxies. This is proved by the source coefficient congruence, without an
assumed equality to a model pair sum. -/
theorem parity_original_balanced_proxy_source_re434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (S gamma kappa : ℝ) (Y : ℕ) :
    (balancedFactorSum true true d L rho Psi S gamma kappa Y).re =
      ∑ u∈Finset.range (Y+1),
        (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L))*
        ∑ z∈parityOriginalShiftTwoPositivePairFibre434
          ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
          ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa)) u,
          (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) z.1).re*
          (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) z.2).re := by
  unfold balancedFactorSum
  have h := parity_original_parity_source_coeff_congr434 d L rho Psi
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2))
    (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2))
    (fun m => ((parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) m).re:ℂ))
    (fun n => ((parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) n).re:ℂ))
    Y
    (by intro m hm
        exact (parity_original_fullcell_coefficient_real434 true true L S gamma 1 (Y+2) m).symm)
    (by intro n hn
        exact (parity_original_fullcell_coefficient_real434 true true L S gamma 1 (Y+2) n).symm)
  rw [h,parity_original_parity_source_real_coeff_re434]

/-- Closed source domination needed next in (8.4). Both parity branches
are valid under |rho|<=1. The remaining analytic obligation is an upper
bound on THIS actual double-rough mass with O(kappa*L+1), not a model CRT
box or the already known quadratic dyad count. -/
theorem parity_original_balanced_proxy_le_double_rough_mass434
    (Psi : ℝ → ℝ) (hNonneg : ∀ t,0≤Psi t) (S : ℝ) (hS : 0<S) :
    ∀ᶠ L : ℝ in atTop,∀ (d Y : ℕ) (rho gamma kappa : ℝ),
      |rho|≤1 → kappa<1/50 →
      (balancedFactorSum true true d L rho Psi S gamma kappa Y).re≤
        (9/(L^2*(sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)^2))*
          balancedRoughPairMass d L rho Psi kappa Y := by
  filter_upwards [parity_original_balanced_fullcell_prime_cap434 S hS,
    eventually_gt_atTop (0:ℝ)] with L hCap hL d Y rho gamma kappa hRho hKappa
  let C := 3/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)
  let K := 9/(L^2*(sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)^2)
  have hV := parity_original_subpower_natural_euler_pos434 L
  have hC : 0≤C := div_nonneg (by norm_num) (mul_pos hL hV).le
  have hK : 0≤K := by dsimp [K]; positivity
  have hSquare : C*C=K := by
    dsimp [C,K]
    field_simp [ne_of_gt hL,ne_of_gt hV] <;> ring
  rw [parity_original_balanced_proxy_source_re434]
  unfold balancedRoughPairMass
  change _≤K*_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hw := mul_nonneg (parity_original_parity_A_nonneg434 d L rho hRho u)
    (hNonneg ((u:ℝ)/Real.exp L))
  rw [mul_left_comm K]
  apply mul_le_mul_of_nonneg_left _ hw
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hPair := (Finset.mem_filter.mp hz).1
  have hm := (Finset.mem_product.mp hPair).1
  have hn := (Finset.mem_product.mp hPair).2
  have hmCap := hCap kappa gamma Y z.1 hKappa hm
  have hnCap := hCap kappa gamma Y z.2 hKappa hn
  by_cases hBoth :
      sourceD20Rough (Real.exp (Real.sqrt L)) z.1 ∧
        sourceD20Rough (Real.exp (Real.sqrt L)) z.2
  · rw [if_pos hBoth,mul_one]
    exact (mul_le_mul hmCap.2 hnCap.2 hnCap.1 hC).trans_eq hSquare
  · rw [if_neg hBoth,mul_zero]
    by_cases hmZero :
        (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) z.1).re=0
    · simp only [hmZero,zero_mul,le_refl]
    · have hnZero :
          (parityOriginalFullCellCoefficient434 true true L S gamma 1 (Y+2) z.2).re=0 := by
        by_contra hnZero
        exact hBoth
          ⟨parity_original_fullcell_prime_proxy_support434 L S gamma 1 (Y+2) z.1 hmZero,
            parity_original_fullcell_prime_proxy_support434 L S gamma 1 (Y+2) z.2 hnZero⟩
      simp only [hnZero,mul_zero,le_refl]
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedIntegratedAudit -/

section



end

/-! ## OriginalShiftTwoCRTIntegratedAudit -/

section

set_option pp.universes false
set_option pp.explicit false

end

/-! ## OriginalA0TailOrbit -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

theorem parity_factorial_inverse_bounds434 (n : ℕ) :
    0 ≤ ((n.factorial : ℝ)⁻¹) ∧ ((n.factorial : ℝ)⁻¹) ≤ 1 := by
  have hp : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos n)
  exact ⟨inv_nonneg.mpr hp.le, (inv_le_one₀ hp).mpr h1⟩

/-- Restrict a complete labelled Q witness to any chosen set of bands.
All repeated factors remain in the product. -/
theorem parity_source_restricted_slots_dvd434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (s : Finset B)
    (f : (b : B) → Fin r → {p // p ∈ Q b}) :
    (∏ j : s, ∏ i : Fin r, (f j.val i).val) ∣
      (∏ b : B, ∏ i : Fin r, (f b i).val) := by
  rw [Finset.prod_coe_sort s (fun b => ∏ i : Fin r, (f b i).val)]
  exact Finset.prod_dvd_prod_of_subset s Finset.univ
    (fun b => ∏ i : Fin r, (f b i).val) (Finset.subset_univ s)

/-- The full ordinary coefficient is dominated by the exact orbit mass
of its restricted witness. No arbitrary divisor assignment is used here. -/
theorem parity_source_ordinary_le_restricted_orbit434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (s : Finset B)
    (v : ℕ) (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) = v)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalOrdinaryCoefficient r Q v ≤
      ∑ a ∈ sourceShiftTwoMicroOrbit r (fun j : s => Q j.val)
        (fun j i => f j.val i),
        ∏ _j : s, (1 : ℝ) / (r.factorial : ℝ) := by
  classical
  rw [source_micro_orbit_mass_equals_factorials]
  have htail :
      (∏ j : s, ∏ p ∈ Q j.val, ((v.factorization p).factorial : ℝ)⁻¹) =
      ∏ j : s, ∏ p ∈ Finset.univ.image (fun i => f j.val i),
        ((Fintype.card {i : Fin r // f j.val i = p}).factorial : ℝ)⁻¹ := by
    apply Finset.prod_congr rfl
    intro j hj
    apply source_factorial_band_to_tuple r (Q j.val) (f j.val) v
    intro p hp
    have h := source_full_slots_band_factorization r Q hPrime hDisjoint f j.val p hp
    simpa [hf] using h
  rw [← htail, Finset.prod_coe_sort s (fun b => ∏ p ∈ Q b, ((v.factorization p).factorial : ℝ)⁻¹)]
  unfold sourceOriginalOrdinaryCoefficient
  rw [if_pos ⟨f, hf⟩]
  apply Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ s)
  · intro b hb
    exact Finset.prod_nonneg (fun p hp => (parity_factorial_inverse_bounds434 _).1)
  · intro b hb hbs
    exact Finset.prod_le_one₀ (fun p hp => (parity_factorial_inverse_bounds434 _).1)
      (fun p hp => (parity_factorial_inverse_bounds434 _).2)

/-- Exactly the ordinary source bands j ≥ j'=20, including an empty tail
when the finite source cutoff is below 20. -/
def parityOriginalAssignmentTail434 (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun j => 20 ≤ j.val)

@[simp] theorem parity_mem_original_assignment_tail434 (d : ℕ) (j : Fin (d+1)) :
    j ∈ parityOriginalAssignmentTail434 d ↔ 20 ≤ j.val := by
  simp [parityOriginalAssignmentTail434]

noncomputable def parityOriginalTailDivisorMass434 (d : ℕ) (L : ℝ) (u : ℕ) : ℝ :=
  ∑ a : (j : parityOriginalAssignmentTail434 d) →
      Fin 20 → {p // p ∈ sourceOriginalQActualBands 20 d L j.val},
    if (∏ j : parityOriginalAssignmentTail434 d, ∏ i : Fin 20, (a j i).val) ∣ u
    then ∏ _j : parityOriginalAssignmentTail434 d, (1 : ℝ) / ((Nat.factorial 20) : ℝ)
    else 0

/-- Genuine A0, full original P carrier, and the literal j≥20 Q tail.
This endpoint is the factorial-drop stage, before any mask is inserted. -/
theorem parity_original_A0_le_tail_divisor_mass434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u ≤
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      parityOriginalTailDivisorMass434 d L u := by
  classical
  let Q := sourceOriginalQActualBands 20 d L
  let P := sourceOriginalPAllActualBands 20 L
  let s := parityOriginalAssignmentTail434 d
  let v := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  have hN : 0 ≤ parityOriginalTailDivisorMass434 d L u := by
    apply Finset.sum_nonneg
    intro a ha
    split_ifs <;> positivity
  unfold sourceOriginalA0
  apply mul_le_mul_of_nonneg_left _ (source_original_W1_nonneg _ u)
  change sourceOriginalOrdinaryCoefficient 20 Q v ≤ _
  by_cases hs : ∃ f : (b : Fin (d+1)) → Fin 20 → {p // p ∈ Q b},
      (∏ b : Fin (d+1), ∏ i : Fin 20, (f b i).val) = v
  · obtain ⟨f, hf⟩ := hs
    let O := sourceShiftTwoMicroOrbit 20 (fun j : s => Q j.val) (fun j i => f j.val i)
    have hO := parity_source_ordinary_le_restricted_orbit434 20 Q s v f hf
      (source_original_Q_actual_prime 20 d L)
      (source_original_Q_actual_all_disjoint 20 d L (by norm_num) hL)
    have hd : (∏ j : s, ∏ i : Fin 20, (f j.val i).val) ∣ u := by
      have h1 := parity_source_restricted_slots_dvd434 20 Q s f
      rw [hf] at h1
      have h2 := source_original_ordinary_times_P_part (Finset.univ.biUnion P) u hu
      exact h1.trans ⟨_, h2.symm⟩
    have hOD (a : (j : s) → Fin 20 → {p // p ∈ Q j.val}) (ha : a ∈ O) :
        (∏ j : s, ∏ i : Fin 20, (a j i).val) ∣ u := by
      rw [source_micro_orbit_product_eq 20 (fun j : s => Q j.val)
        (fun j i => f j.val i) a ha]
      exact hd
    calc
      sourceOriginalOrdinaryCoefficient 20 Q v ≤
        ∑ a ∈ O, ∏ _j : s, (1 : ℝ)/((Nat.factorial 20) : ℝ) := hO
      _ = ∑ a ∈ O,
          if (∏ j : s, ∏ i : Fin 20, (a j i).val) ∣ u
          then ∏ _j : s, (1 : ℝ)/((Nat.factorial 20) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos (hOD a ha)]
      _ ≤ parityOriginalTailDivisorMass434 d L u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O)
        intro a ha hna
        split_ifs <;> positivity
  · rw [sourceOriginalOrdinaryCoefficient, if_neg hs]
    exact hN

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalA0Marks -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

noncomputable def parityMarkedGroupTerm434 (P : Finset ℕ) (u : ℕ) (p : P) : ℝ :=
  (if p.val ∣ u then ∏ q ∈ P.erase p.val, if q ∣ u then (1/2 : ℝ) else 1
   else 0) / (∑ q ∈ P, (q : ℝ)⁻¹)

noncomputable def parityGroupMarkNormalization434
    {G : Type} [Fintype G] (P : G → Finset ℕ) : ℝ :=
  ∏ g : G, (∑ p ∈ P g, (p : ℝ)⁻¹)⁻¹

noncomputable def parityAssignmentModulus434
    {J G : Type} [Fintype J] [Fintype G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (a : (j : J) → Fin r → {p // p ∈ Q j})
    (marks : (g : G) → {p // p ∈ P g}) : ℕ :=
  (∏ j : J, ∏ i : Fin r, (a j i).val) * (∏ g : G, (marks g).val)

theorem parity_W1_all_group_marks434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (u : ℕ) :
    sourceOriginalW1 P u =
      ∑ marks : (g : G) → {p // p ∈ P g},
        ∏ g : G, parityMarkedGroupTerm434 (P g) u (marks g) := by
  classical
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro g hg
  unfold parityMarkedGroupTerm434
  rw [← Finset.sum_div, Finset.sum_coe_sort (P g) (fun p : ℕ =>
    if p ∣ u then ∏ q ∈ (P g).erase p, if q ∣ u then (1/2 : ℝ) else 1 else 0)]
  exact (shift_two_group_mark_normalized (P g) u).symm

theorem parity_group_mark_product434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (u : ℕ)
    (marks : (g : G) → {p // p ∈ P g}) :
    (∏ g : G, parityMarkedGroupTerm434 (P g) u (marks g)) =
      if ∀ g : G, (marks g).val ∣ u
      then parityGroupMarkNormalization434 P *
        (∏ g : G, ∏ p ∈ (P g).erase (marks g).val,
          if p ∣ u then (1/2 : ℝ) else 1)
      else 0 := by
  classical
  by_cases h : ∀ g : G, (marks g).val ∣ u
  · simp only [if_pos h, parityMarkedGroupTerm434, if_pos (h _), div_eq_mul_inv,
      Finset.prod_mul_distrib, parityGroupMarkNormalization434]
    ring
  · rw [if_neg h]
    push_neg at h
    obtain ⟨g, hg⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ g) (by simp [parityMarkedGroupTerm434, hg])

/-- Distinct P marks divide the genuine P part, with all valuations retained. -/
theorem parity_group_marks_product_dvd_P_part434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (u : ℕ) (hu : u ≠ 0)
    (marks : (g : G) → {p // p ∈ P g})
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hDiv : ∀ g : G, (marks g).val ∣ u) :
    (∏ g : G, (marks g).val) ∣
      sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by
  classical
  have hInjective : Function.Injective (fun g : G => (marks g).val) := by
    intro g h heq
    apply hPP g h ((marks g).val) (marks g).property
    simpa [← heq] using (marks h).property
  let s : Finset ℕ := Finset.univ.image (fun g : G => (marks g).val)
  let t : Finset ℕ := u.primeFactors ∩ (Finset.univ.biUnion P)
  have hsub : s ⊆ t := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_inter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hPprime g _ (marks g).property, hDiv g, hu⟩,
       Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (marks g).property⟩⟩
  have himg : (∏ p ∈ s, p) = (∏ g : G, (marks g).val) :=
    Finset.prod_image (fun g hg h hh he => hInjective he)
  have hdPow : (∏ p ∈ s, p) ∣ (∏ p ∈ s, p ^ u.factorization p) := by
    apply Finset.prod_dvd_prod_of_dvd (fun p : ℕ => p) (fun p => p ^ u.factorization p)
    intro p hp
    have hm := Nat.mem_primeFactors.mp (Finset.mem_inter.mp (hsub hp)).1
    have hv : 0 < u.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hm.1 hu).mp hm.2.1
    exact dvd_pow_self p hv.ne'
  have hdSubset : (∏ p ∈ s, p ^ u.factorization p) ∣
      (∏ p ∈ t, p ^ u.factorization p) :=
    Finset.prod_dvd_prod_of_subset s t (fun p => p ^ u.factorization p) hsub
  rw [sourceOriginalPPrimePart]
  exact himg.symm ▸ hdPow.trans hdSubset

/-- The complete modulus, including every marked P prime, on a true source orbit. -/
theorem parity_assignment_dvd_iff_marks_on_source434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (s : Finset B)
    (u : ℕ) (hu : u ≠ 0)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) =
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)
    (a : (j : s) → Fin r → {p // p ∈ Q j.val})
    (ha : a ∈ sourceShiftTwoMicroOrbit r (fun j : s => Q j.val)
      (fun j i => f j.val i))
    (marks : (g : G) → {p // p ∈ P g})
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks ∣ u ↔
      ∀ g : G, (marks g).val ∣ u := by
  classical
  have hMicro : (∏ j : s, ∏ i : Fin r, (a j i).val) ∣
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
    rw [source_micro_orbit_product_eq r (fun j : s => Q j.val)
      (fun j i => f j.val i) a ha, ← hf]
    exact parity_source_restricted_slots_dvd434 r Q s f
  unfold parityAssignmentModulus434
  constructor
  · intro hD g
    exact (Finset.dvd_prod_of_mem (fun h : G => (marks h).val)
      (Finset.mem_univ g)).trans (dvd_mul_left _ _) |>.trans hD
  · intro hmarks
    have hpDiv := parity_group_marks_product_dvd_P_part434 P u hu marks hPprime hPP hmarks
    have hBoth := mul_dvd_mul hMicro hpDiv
    rw [source_original_ordinary_times_P_part _ u hu] at hBoth
    exact hBoth

/-- A P prime divides D1 exactly when it is its group's selected mark.
No squarefreeness of Q products or of u is assumed. -/
theorem parity_P_prime_dvd_assignment_iff_mark434
    {J G : Type} [Fintype J] [Fintype G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (a : (j : J) → Fin r → {p // p ∈ Q j})
    (marks : (g : G) → {p // p ∈ P g})
    (hQprime : ∀ j p, p ∈ Q j → p.Prime)
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ j g p, p ∈ Q j → p ∈ P g → False)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (g : G) (p : ℕ) (hp : p ∈ P g) :
    p ∣ parityAssignmentModulus434 r Q P a marks ↔ p = (marks g).val := by
  classical
  have hpp : p.Prime := hPprime g p hp
  have hNoQ : ¬ p ∣ (∏ j : J, ∏ i : Fin r, (a j i).val) := by
    intro hd
    obtain ⟨j, hj, hjd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp)
      (fun j : J => ∏ i : Fin r, (a j i).val)).mp hd
    obtain ⟨i, hi, hid⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp)
      (fun i : Fin r => (a j i).val)).mp hjd
    have he : p = (a j i).val := (Nat.prime_dvd_prime_iff_eq hpp
      (hQprime j _ (a j i).property)).mp hid
    exact hQP j g p (by simpa [he] using (a j i).property) hp
  unfold parityAssignmentModulus434
  constructor
  · intro hd
    have hm := ((Nat.Prime.dvd_mul hpp).mp hd).resolve_left hNoQ
    obtain ⟨h, hh, hhD⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp)
      (fun h : G => (marks h).val)).mp hm
    have he : p = (marks h).val := (Nat.prime_dvd_prime_iff_eq hpp
      (hPprime h _ (marks h).property)).mp hhD
    have hhg : h = g :=
      (hPP g h p hp (by simpa [he] using (marks h).property)).symm
    rw [hhg] at he
    exact he
  · intro he
    exact (Nat.Prime.dvd_mul hpp).mpr (Or.inr (he ▸
      Finset.dvd_prod_of_mem (fun h : G => (marks h).val) (Finset.mem_univ g)))

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalA0BooleanMasks -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

noncomputable def parityAssignmentMaskUniverse434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (D : ℕ) : Finset ℕ :=
  (Finset.univ.biUnion P).filter (fun p => ¬ p ∣ D)

noncomputable def parityAssignmentDetBans434 (z : ℝ) (Pall : Finset ℕ) (D : ℕ) : Finset ℕ :=
  ((Finset.Icc 3 ⌊z⌋₊).filter Nat.Prime).filter (fun p => p ∉ Pall ∧ ¬ p ∣ D)

/-- Uniform independent half permissions on every actual unmarked group prime.
S lists allowed primes; its complement is banned. -/
noncomputable def parityAssignmentMaskAverage434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (z : ℝ) (D u : ℕ) : ℝ :=
  let U := parityAssignmentMaskUniverse434 P D
  let B := parityAssignmentDetBans434 z (Finset.univ.biUnion P) D
  ∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
    ∏ p ∈ B ∪ (U \ S), if p ∣ u then (0 : ℝ) else 1

theorem parity_uniform_half_mask_normalized434 (U : Finset ℕ) :
    (∑ _S ∈ U.powerset, (1/2 : ℝ)^U.card) = 1 := by
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

theorem parity_uniform_half_mask_factor_weight434 (U S : Finset ℕ) (hS : S ⊆ U) :
    (1/2 : ℝ)^U.card =
      (∏ _p ∈ S, (1/2 : ℝ)) * (∏ _p ∈ U \ S, (1/2 : ℝ)) := by
  have h := Finset.prod_sdiff (f := fun _p : ℕ => (1/2 : ℝ)) hS
  simpa only [Finset.prod_const, mul_comm] using h.symm

/-- Exact finite Bernoulli expectation, no independence assumption is a premise. -/
theorem parity_uniform_half_mask_survival434 (U : Finset ℕ) (u : ℕ) :
    (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
      ∏ p ∈ U \ S, if p ∣ u then (0 : ℝ) else 1) =
    ∏ p ∈ U, if p ∣ u then (1/2 : ℝ) else 1 := by
  classical
  calc
    _ = ∑ S ∈ U.powerset, (∏ _p ∈ S, (1/2 : ℝ)) *
        (∏ p ∈ U \ S, (1/2 : ℝ) * (if p ∣ u then (0 : ℝ) else 1)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [parity_uniform_half_mask_factor_weight434 U S (Finset.mem_powerset.mp hS),
        Finset.prod_mul_distrib]
      ring
    _ = ∏ p ∈ U, ((1/2 : ℝ) + (1/2 : ℝ) * (if p ∣ u then (0 : ℝ) else 1)) :=
      (Finset.prod_add (fun _ => (1/2 : ℝ))
        (fun p => (1/2 : ℝ) * (if p ∣ u then (0 : ℝ) else 1)) U).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      split_ifs <;> norm_num

theorem parity_assignment_mask_average_nonneg434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (z : ℝ) (D u : ℕ) :
    0 ≤ parityAssignmentMaskAverage434 P z D u := by
  unfold parityAssignmentMaskAverage434
  apply Finset.sum_nonneg
  intro S hS
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro p hp
  split_ifs <;> norm_num

/-- Literal nongroup bans and random group bans are disjoint by construction. -/
theorem parity_assignment_mask_average_split434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (z : ℝ) (D u : ℕ) :
    parityAssignmentMaskAverage434 P z D u =
      (∏ p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D,
        if p ∣ u then (0 : ℝ) else 1) *
      (∏ p ∈ parityAssignmentMaskUniverse434 P D,
        if p ∣ u then (1/2 : ℝ) else 1) := by
  classical
  let U := parityAssignmentMaskUniverse434 P D
  let B := parityAssignmentDetBans434 z (Finset.univ.biUnion P) D
  have hdisj (S : Finset ℕ) : Disjoint B (U \ S) := by
    apply Finset.disjoint_left.mpr
    intro p hpB hpU
    have hn := (Finset.mem_filter.mp hpB).2.1
    have hm := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpU).1).1
    exact hn hm
  calc
    parityAssignmentMaskAverage434 P z D u =
      (∏ p ∈ B, if p ∣ u then (0 : ℝ) else 1) *
        (∑ S ∈ U.powerset, (1/2 : ℝ)^U.card *
          ∏ p ∈ U \ S, if p ∣ u then (0 : ℝ) else 1) := by
      unfold parityAssignmentMaskAverage434
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_union (hdisj S)]
      ring
    _ = _ := by rw [parity_uniform_half_mask_survival434]

/-- The random domain is exactly all P primes other than one own-group mark. -/
theorem parity_assignment_mask_universe_eq_erased_groups434
    {J G : Type} [Fintype J] [Fintype G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (a : (j : J) → Fin r → {p // p ∈ Q j})
    (marks : (g : G) → {p // p ∈ P g})
    (hQprime : ∀ j p, p ∈ Q j → p.Prime)
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ j g p, p ∈ Q j → p ∈ P g → False)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) =
      Finset.univ.biUnion (fun g : G => (P g).erase (marks g).val) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpD⟩ := Finset.mem_filter.mp hp
    obtain ⟨g, hg, hpg⟩ := Finset.mem_biUnion.mp hpP
    refine Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_erase.mpr ⟨?_, hpg⟩⟩
    exact fun he => hpD ((parity_P_prime_dvd_assignment_iff_mark434
      r Q P a marks hQprime hPprime hQP hPP g p hpg).mpr he)
  · intro hp
    obtain ⟨g, hg, hpg⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hpg
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hg, hmem⟩, ?_⟩
    exact fun hd => hne ((parity_P_prime_dvd_assignment_iff_mark434
      r Q P a marks hQprime hPprime hQP hPP g p hmem).mp hd)

theorem parity_assignment_unmarked_product434
    {J G : Type} [Fintype J] [Fintype G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (a : (j : J) → Fin r → {p // p ∈ Q j})
    (marks : (g : G) → {p // p ∈ P g})
    (hQprime : ∀ j p, p ∈ Q j → p.Prime)
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ j g p, p ∈ Q j → p ∈ P g → False)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h) (u : ℕ) :
    (∏ p ∈ parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks),
      if p ∣ u then (1/2 : ℝ) else 1) =
      ∏ g : G, ∏ p ∈ (P g).erase (marks g).val,
        if p ∣ u then (1/2 : ℝ) else 1 := by
  classical
  rw [parity_assignment_mask_universe_eq_erased_groups434 r Q P a marks
    hQprime hPprime hQP hPP]
  apply Finset.prod_biUnion
  intro g hg h hh hne
  apply Finset.disjoint_left.mpr
  intro p hpG hpH
  exact hne (hPP g h p (Finset.mem_of_mem_erase hpG) (Finset.mem_of_mem_erase hpH))

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalA0Deterministic -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

noncomputable def parityOriginalAssignmentTheta434 : ℝ := (3/2 : ℝ) * (1/44 : ℝ) * (1/2 : ℝ)^20

theorem parity_original_assignment_macro_gap434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin (d+1))
    (hj : j ∉ parityOriginalAssignmentTail434 d) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands 20 d L j) :
    Real.exp (parityOriginalAssignmentTheta434 * L) < (p : ℝ) := by
  have hj19 : j.val ≤ 19 := by
    have hn : ¬ 20 ≤ j.val := by simpa using hj
    omega
  have hpow : (2 : ℝ)^j.val ≤ (2 : ℝ)^19 :=
    pow_le_pow_right₀ (by norm_num) hj19
  have hden : (44 : ℝ) * (2 : ℝ)^j.val ≤ 44 * (2 : ℝ)^19 :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hq : 1 / (44 * (2 : ℝ)^19) ≤ 1 / (44 * (2 : ℝ)^j.val) :=
    one_div_le_one_div_of_le (by positivity) hden
  have ht : parityOriginalAssignmentTheta434 < 1 / (44 * (2 : ℝ)^19) := by
    norm_num [parityOriginalAssignmentTheta434]
  have hgap : parityOriginalAssignmentTheta434 < sourceOriginalQActualExponent 20 j.val := by
    rw [(parity_r20_Q_exponent434 j.val).1]
    exact ht.trans_le hq
  have hlo : Real.exp (sourceOriginalQActualExponent 20 j.val * L) ≤ (p : ℝ) := by
    rw [source_original_Q_actual_scale_eq_P_scale 20 j.val L (by norm_num)]
    exact (source_original_Q_actual_prime_range 20 d L (by norm_num) j p hp).1
  exact (Real.exp_strictMono (mul_lt_mul_of_pos_right hgap hL)).trans_le hlo

/-- The full ordinary witness forces every sufficiently small non-P prime
divisor into the selected tail. This is proved before enlarging its orbit. -/
theorem parity_source_small_nonP_prime_in_tail434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (s : Finset B)
    (Pall : Finset ℕ) (u : ℕ) (hu : u ≠ 0)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) = sourceOriginalOrdinaryPart Pall u)
    (z : ℝ)
    (hQprime : ∀ b p, p ∈ Q b → p.Prime)
    (hMacro : ∀ b, b ∉ s → ∀ p, p ∈ Q b → z < (p : ℝ))
    (p : ℕ) (hp : p.Prime) (hpz : (p : ℝ) ≤ z)
    (hpP : p ∉ Pall) (hpu : p ∣ u) :
    p ∣ (∏ j : s, ∏ i : Fin r, (f j.val i).val) := by
  classical
  have hpStar : p ∣ sourceOriginalOrdinaryPart Pall u :=
    source_ordinary_part_dvd_of_not_mem Pall u p hu hp hpu hpP
  rw [← hf] at hpStar
  obtain ⟨b, hb, hbd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
    (fun b : B => ∏ i : Fin r, (f b i).val)).mp hpStar
  obtain ⟨i, hi, hid⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
    (fun i : Fin r => (f b i).val)).mp hbd
  have he : p = (f b i).val := (Nat.prime_dvd_prime_iff_eq hp
    (hQprime b _ (f b i).property)).mp hid
  have hbs : b ∈ s := by
    by_contra hn
    have hg := hMacro b hn _ (f b i).property
    rw [← he] at hg
    exact (not_lt_of_ge hpz) hg
  exact hbd.trans (Finset.dvd_prod_of_mem
    (fun j : s => ∏ i : Fin r, (f j.val i).val) (Finset.mem_univ ⟨b,hbs⟩))

/-- Every original deterministic ban is survived on the complete-witness orbit.
It is essential that D contains its entire tail product. -/
theorem parity_source_orbit_deterministic_survival434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (s : Finset B)
    (Pall : Finset ℕ) (u : ℕ) (hu : u ≠ 0)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) = sourceOriginalOrdinaryPart Pall u)
    (a : (j : s) → Fin r → {p // p ∈ Q j.val})
    (ha : a ∈ sourceShiftTwoMicroOrbit r (fun j : s => Q j.val) (fun j i => f j.val i))
    (D : ℕ) (hD : (∏ j : s, ∏ i : Fin r, (a j i).val) ∣ D)
    (z : ℝ) (hz : 0 ≤ z)
    (hQprime : ∀ b p, p ∈ Q b → p.Prime)
    (hMacro : ∀ b, b ∉ s → ∀ p, p ∈ Q b → z < (p : ℝ)) :
    (∏ p ∈ parityAssignmentDetBans434 z Pall D,
      if p ∣ u then (0 : ℝ) else 1) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro p hp
  obtain ⟨hp0, hpP, hpD⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp0
  have hpz : (p : ℝ) ≤ z := by
    have hfloor : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hpI).2
    exact hfloor.trans (Nat.floor_le hz)
  have hnot : ¬ p ∣ u := by
    intro hpu
    have ht := parity_source_small_nonP_prime_in_tail434 r Q s Pall u hu f hf z
      hQprime hMacro p hpPrime hpz hpP hpu
    rw [← source_micro_orbit_product_eq r (fun j : s => Q j.val)
      (fun j i => f j.val i) a ha] at ht
    exact hpD (ht.trans hD)
  simp [hnot]

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalA0AssignmentMajorant -/

section

set_option maxHeartbeats 500000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

noncomputable def parityAssignmentNormalization434
    (J : Type) [Fintype J] {G : Type} [Fintype G]
    (r : ℕ) (P : G → Finset ℕ) : ℝ :=
  (∏ _j : J, (1 : ℝ) / (r.factorial : ℝ)) * parityGroupMarkNormalization434 P

/-- Literal Parity (6.3) RHS. All ordered tail slots, one mark in every group,
the complete multiplicity-preserving D1, and its exact Boolean average. -/
noncomputable def parityAssignmentMajorant434
    {J G : Type} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ) (z : ℝ) (u : ℕ) : ℝ :=
  ∑ a : (j : J) → Fin r → {p // p ∈ Q j},
    ∑ marks : (g : G) → {p // p ∈ P g},
      if parityAssignmentModulus434 r Q P a marks ∣ u
      then parityAssignmentNormalization434 J r P *
        parityAssignmentMaskAverage434 P z (parityAssignmentModulus434 r Q P a marks) u
      else 0

theorem parity_assignment_normalization_nonneg434
    (J : Type) [Fintype J] {G : Type} [Fintype G]
    (r : ℕ) (P : G → Finset ℕ) :
    0 ≤ parityAssignmentNormalization434 J r P := by
  unfold parityAssignmentNormalization434 parityGroupMarkNormalization434
  positivity

/-- Exact original W1-to-mask identity on a restricted complete source witness.
The witness has not been discarded or replaced by arbitrary divisor tuples. -/
theorem parity_source_orbit_W1_mark_mask_identity434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (s : Finset B)
    (u : ℕ) (hu : u ≠ 0)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) =
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)
    (a : (j : s) → Fin r → {p // p ∈ Q j.val})
    (ha : a ∈ sourceShiftTwoMicroOrbit r (fun j : s => Q j.val) (fun j i => f j.val i))
    (z : ℝ) (hz : 0 ≤ z)
    (hQprime : ∀ b p, p ∈ Q b → p.Prime)
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hMacro : ∀ b, b ∉ s → ∀ p, p ∈ Q b → z < (p : ℝ)) :
    sourceOriginalW1 P u =
      ∑ marks : (g : G) → {p // p ∈ P g},
        if parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks ∣ u
        then parityGroupMarkNormalization434 P *
          parityAssignmentMaskAverage434 P z
            (parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks) u
        else 0 := by
  classical
  rw [parity_W1_all_group_marks434]
  apply Finset.sum_congr rfl
  intro marks hm
  have hdiv := parity_assignment_dvd_iff_marks_on_source434
    r Q P s u hu f hf a ha marks hPprime hPP
  have hdet := parity_source_orbit_deterministic_survival434 r Q s
    (Finset.univ.biUnion P) u hu f hf a ha
    (parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks)
    (dvd_mul_right _ _) z hz hQprime hMacro
  have hmean :
      parityAssignmentMaskAverage434 P z
        (parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks) u =
      ∏ g : G, ∏ p ∈ (P g).erase (marks g).val,
        if p ∣ u then (1/2 : ℝ) else 1 := by
    rw [parity_assignment_mask_average_split434, hdet, one_mul]
    exact parity_assignment_unmarked_product434 r (fun j : s => Q j.val) P a marks
      (fun j => hQprime j.val) hPprime (fun j => hQP j.val) hPP u
  simp only [parity_group_mark_product434, hmean, hdiv]

/-- Source-faithful assignment majorant: remove macro factorials, retain their
witness through deterministic survival, then and only then enlarge the orbit. -/
theorem parity_original_A0_assignment_majorant_of_source_geometry434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (s : Finset B)
    (z : ℝ) (hz : 0 ≤ z) (u : ℕ) (hu : u ≠ 0)
    (hQprime : ∀ b p, p ∈ Q b → p.Prime)
    (hQdisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPprime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False)
    (hPP : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hMacro : ∀ b, b ∉ s → ∀ p, p ∈ Q b → z < (p : ℝ)) :
    sourceOriginalA0 r Q P u ≤
      parityAssignmentMajorant434 r (fun j : s => Q j.val) P z u := by
  classical
  let v := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  let C : ℝ := ∏ _j : s, (1 : ℝ)/(r.factorial : ℝ)
  let F := fun (a : (j : s) → Fin r → {p // p ∈ Q j.val}) =>
    ∑ marks : (g : G) → {p // p ∈ P g},
      if parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks ∣ u
      then parityAssignmentNormalization434 s r P *
        parityAssignmentMaskAverage434 P z
          (parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks) u
      else 0
  have hF (a : (j : s) → Fin r → {p // p ∈ Q j.val}) : 0 ≤ F a := by
    apply Finset.sum_nonneg
    intro marks hm
    split_ifs
    · exact mul_nonneg (parity_assignment_normalization_nonneg434 s r P)
        (parity_assignment_mask_average_nonneg434 P z _ u)
    · exact le_rfl
  by_cases hs : ∃ f : (b : B) → Fin r → {p // p ∈ Q b},
      (∏ b : B, ∏ i : Fin r, (f b i).val) = v
  · obtain ⟨f, hf⟩ := hs
    let O := sourceShiftTwoMicroOrbit r (fun j : s => Q j.val) (fun j i => f j.val i)
    have hle := parity_source_ordinary_le_restricted_orbit434 r Q s v f hf hQprime hQdisjoint
    have hterm (a : (j : s) → Fin r → {p // p ∈ Q j.val}) (ha : a ∈ O) :
        sourceOriginalW1 P u * C = F a := by
      rw [parity_source_orbit_W1_mark_mask_identity434 r Q P s u hu f hf a ha
        z hz hQprime hPprime hQP hPP hMacro, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro marks hm
      by_cases hd : parityAssignmentModulus434 r (fun j : s => Q j.val) P a marks ∣ u
      · simp only [if_pos hd, parityAssignmentNormalization434]
        dsimp [C]
        ring
      · simp only [if_neg hd, zero_mul]
    calc
      sourceOriginalA0 r Q P u ≤
          sourceOriginalW1 P u * (∑ a ∈ O, C) :=
        mul_le_mul_of_nonneg_left hle (source_original_W1_nonneg P u)
      _ = ∑ a ∈ O, F a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a ha => hterm a ha)
      _ ≤ ∑ a, F a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O) (fun a ha hna => hF a)
      _ = parityAssignmentMajorant434 r (fun j : s => Q j.val) P z u := rfl
  · have hzero : sourceOriginalOrdinaryCoefficient r Q v = 0 := by
      rw [sourceOriginalOrdinaryCoefficient, if_neg hs]
    change sourceOriginalW1 P u * sourceOriginalOrdinaryCoefficient r Q v ≤ ∑ a, F a
    rw [hzero, mul_zero]
    exact Finset.sum_nonneg (fun a ha => hF a)

/-- Literal original Parity (6.3) A0 majorant: r0=20, sigma=1/44,
j'=20, theta0=(3/2)sigma 2^-20, and every actual P group.
No desired source identity, mask law, or assignment bound is assumed. -/
theorem parity_original_A0_assignment_mask_majorant434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u ≤
    parityAssignmentMajorant434 20
      (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
      (sourceOriginalPAllActualBands 20 L)
      (Real.exp (parityOriginalAssignmentTheta434 * L)) u := by
  apply parity_original_A0_assignment_majorant_of_source_geometry434
    20 (sourceOriginalQActualBands 20 d L) (sourceOriginalPAllActualBands 20 L)
    (parityOriginalAssignmentTail434 d) _ (Real.exp_pos _).le u hu
    (source_original_Q_actual_prime 20 d L)
    (source_original_Q_actual_all_disjoint 20 d L (by norm_num) hL)
    (source_original_P_all_actual_band_prime 20 L)
    (source_original_Q_actual_all_P_disjoint 20 d L (by norm_num) hL)
    (source_original_P_actual_all_disjoint 20 L (by norm_num) hL)
  intro j hj p hp
  exact parity_original_assignment_macro_gap434 d L hL j hj p hp

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalA0LiteralParity -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

theorem parity_original_assignment_tail_card434 (d : ℕ) :
    (parityOriginalAssignmentTail434 d).card = d + 1 - 20 := by
  by_cases h : 20 < d + 1
  · have he : parityOriginalAssignmentTail434 d = Finset.Ici (⟨20,h⟩ : Fin (d+1)) := by
      ext j
      simp only [parity_mem_original_assignment_tail434, Finset.mem_Ici]
      rfl
    rw [he, Fin.card_Ici]
  · have he : parityOriginalAssignmentTail434 d = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj20 := (parity_mem_original_assignment_tail434 d j).mp hj
      have hlt := j.isLt
      omega
    rw [he, Finset.card_empty]
    omega

/-- Exact original eta: one inverse 20! per j≥20 and one inverse V_g
per genuine P group. No quarter-cell normalization is introduced. -/
theorem parity_original_assignment_normalization_exact434 (d : ℕ) (L : ℝ) :
    parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20
      (sourceOriginalPAllActualBands 20 L) =
      (1 / (Nat.factorial 20 : ℝ))^(d + 1 - 20) *
        ∏ g : sourceOriginalPAllGroupType 20 L,
          (∑ p ∈ sourceOriginalPAllActualBands 20 L g, (p : ℝ)⁻¹)⁻¹ := by
  unfold parityAssignmentNormalization434 parityGroupMarkNormalization434
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    parity_original_assignment_tail_card434]

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open SourceBlockSieve

theorem parity_original_parity_A_le_A0_434
    (d : ℕ) (L rho : ℝ) (hRho : |rho| ≤ 1) (u : ℕ) :
    parityWeight d L rho u ≤
      sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u := by
  let E := sourceOriginalPParityExponent
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  have hm : |rho * (-1 : ℝ)^E| ≤ 1 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one] using hRho
  have hproj : (1 + rho * (-1 : ℝ)^E) / 2 ≤ 1 := by
    linarith [(abs_le.mp hm).2]
  have h0 := source_original_A0_nonneg 20 (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u
  unfold parityWeight
  exact (mul_le_mul_of_nonneg_left hproj h0).trans_eq (mul_one _)

/-- Original (6.3), including both Liouville parity projections. -/
theorem parity_original_parity_assignment_mask_majorant434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (rho : ℝ) (hRho : |rho| ≤ 1)
    (u : ℕ) (hu : u ≠ 0) :
    parityWeight d L rho u ≤
      parityAssignmentMajorant434 20
        (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
        (sourceOriginalPAllActualBands 20 L)
        (Real.exp (parityOriginalAssignmentTheta434 * L)) u :=
  (parity_original_parity_A_le_A0_434 d L rho hRho u).trans
    (parity_original_A0_assignment_mask_majorant434 d L hL u hu)

/-- The original cutoff is the literal source depth, not a freely chosen model. -/
theorem parity_original_literal_assignment_mask_majorant434
    (L : ℝ) (hL : 0 < L) (rho : ℝ) (hRho : |rho| ≤ 1)
    (u : ℕ) (hu : u ≠ 0) :
    parityWeight (sourceOriginalLiteralDepth 20 L) L rho u ≤
      parityAssignmentMajorant434 20
        (fun j : parityOriginalAssignmentTail434 (sourceOriginalLiteralDepth 20 L) =>
          sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L j.val)
        (sourceOriginalPAllActualBands 20 L)
        (Real.exp (parityOriginalAssignmentTheta434 * L)) u :=
  parity_original_parity_assignment_mask_majorant434 _ L hL rho hRho u hu

end Green64Analytic.Parity

end

/-! ## OriginalAssignmentReciprocal -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

noncomputable def parityAssignmentHarmonicMass434
    {J : Type} [Fintype J] (r : ℕ) (Q : J → Finset ℕ) : ℝ :=
  ∏ j : J, ((∑ p ∈ Q j, (p : ℝ)⁻¹)^r / (r.factorial : ℝ))

/-- The same labelled, curried Q slots used by the source assignment. -/
theorem parity_curried_assignment_reciprocal434
    {J : Type} [Fintype J] [DecidableEq J]
    (r : ℕ) (Q : J → Finset ℕ) (c : ℝ) :
    (∑ a : (j : J) → Fin r → {p // p ∈ Q j},
      c / ((∏ j : J, ∏ i : Fin r, (a j i).val : ℕ) : ℝ)) =
      c * ∏ j : J, (∑ p ∈ Q j, (p : ℝ)⁻¹)^r := by
  classical
  have hband (j : J) :
      (∑ f : Fin r → {p // p ∈ Q j}, ∏ i : Fin r, ((f i).val : ℝ)⁻¹) =
      (∑ p ∈ Q j, (p : ℝ)⁻¹)^r := by
    have h := Green64FiniteExtraction.assignment_reciprocal (fun _i : Fin r => Q j) 1
    simpa only [one_div, Nat.cast_prod, Finset.prod_inv_distrib, one_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hall :
      (∑ a : (j : J) → Fin r → {p // p ∈ Q j},
        ∏ j : J, ∏ i : Fin r, ((a j i).val : ℝ)⁻¹) =
      ∏ j : J, (∑ p ∈ Q j, (p : ℝ)⁻¹)^r := by
    rw [← Fintype.prod_sum (fun (j : J) (f : Fin r → {p // p ∈ Q j}) =>
      ∏ i : Fin r, ((f i).val : ℝ)⁻¹)]
    exact Finset.prod_congr rfl (fun j hj => hband j)
  calc
    _ = c * ∑ a : (j : J) → Fin r → {p // p ∈ Q j},
          ∏ j : J, ∏ i : Fin r, ((a j i).val : ℝ)⁻¹ := by
      simp only [Finset.mul_sum, div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = _ := by rw [hall]

/-- Exact eta/D1 sum for the very same assignments as the mask majorant.
The P harmonic factors cancel; no factor H_P or model measure is inserted. -/
theorem parity_assignment_reciprocal_mass_exact434
    {J G : Type} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (hP : ∀ g, (∑ p ∈ P g, (p : ℝ)⁻¹) ≠ 0) :
    (∑ a : (j : J) → Fin r → {p // p ∈ Q j},
      ∑ marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 J r P /
          (parityAssignmentModulus434 r Q P a marks : ℝ)) =
      parityAssignmentHarmonicMass434 r Q := by
  classical
  let C : ℝ := ∏ _j : J, (1 : ℝ)/(r.factorial : ℝ)
  let V : ℝ := ∏ g : G, ∑ p ∈ P g, (p : ℝ)⁻¹
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g hg => hP g)
  have hN : parityAssignmentNormalization434 J r P = C * V⁻¹ := by
    unfold parityAssignmentNormalization434 parityGroupMarkNormalization434
    rw [Finset.prod_inv_distrib]
  have hinner (a : (j : J) → Fin r → {p // p ∈ Q j}) :
      (∑ marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 J r P /
          (parityAssignmentModulus434 r Q P a marks : ℝ)) =
      C / ((∏ j : J, ∏ i : Fin r, (a j i).val : ℕ) : ℝ) := by
    unfold parityAssignmentModulus434
    simp only [Nat.cast_mul, div_mul_eq_div_div]
    rw [Green64FiniteExtraction.assignment_reciprocal, hN]
    change (C * V⁻¹ / _) * V = _
    calc
      _ = (C / ((∏ j : J, ∏ i : Fin r, (a j i).val : ℕ) : ℝ)) * (V⁻¹ * V) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hV, mul_one]
  calc
    _ = ∑ a : (j : J) → Fin r → {p // p ∈ Q j},
        C / ((∏ j : J, ∏ i : Fin r, (a j i).val : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun a ha => hinner a)
    _ = C * ∏ j : J, (∑ p ∈ Q j, (p : ℝ)⁻¹)^r :=
      parity_curried_assignment_reciprocal434 r Q C
    _ = parityAssignmentHarmonicMass434 r Q := by
      unfold parityAssignmentHarmonicMass434
      simp only [C, one_div, Finset.prod_div_distrib, div_eq_mul_inv,
        Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_const_one, one_mul]
      ring

/-- Finite moment transport for these exact nested assignment sums. -/
theorem parity_assignment_two_moments_of_size434
    {J G : Type} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : J → Finset ℕ) (P : G → Finset ℕ)
    (hP : ∀ g, (∑ p ∈ P g, (p : ℝ)⁻¹) ≠ 0)
    (X : ℝ) (hX : 0 ≤ X)
    (hD : ∀ (a : (j : J) → Fin r → {p // p ∈ Q j})
      (marks : (g : G) → {p // p ∈ P g}),
      0 < (parityAssignmentModulus434 r Q P a marks : ℝ) ∧
        (parityAssignmentModulus434 r Q P a marks : ℝ) ≤ X) :
    (∑ _a : (j : J) → Fin r → {p // p ∈ Q j},
      ∑ _marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 J r P) ≤ X * parityAssignmentHarmonicMass434 r Q ∧
    (∑ a : (j : J) → Fin r → {p // p ∈ Q j},
      ∑ marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 J r P *
          (parityAssignmentModulus434 r Q P a marks : ℝ)) ≤
      X^2 * parityAssignmentHarmonicMass434 r Q := by
  classical
  have hN := parity_assignment_normalization_nonneg434 J r P
  have hmass := parity_assignment_reciprocal_mass_exact434 r Q P hP
  have h1 :
      (∑ _a : (j : J) → Fin r → {p // p ∈ Q j},
        ∑ _marks : (g : G) → {p // p ∈ P g},
          parityAssignmentNormalization434 J r P) ≤ X * parityAssignmentHarmonicMass434 r Q := by
    rw [← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro marks hm
    have h := mul_le_mul_of_nonneg_right (hD a marks).2
      (div_nonneg hN (hD a marks).1.le)
    simpa [mul_div_cancel₀ _ (ne_of_gt (hD a marks).1), mul_comm] using h
  refine ⟨h1, ?_⟩
  calc
    _ ≤ ∑ _a : (j : J) → Fin r → {p // p ∈ Q j},
        ∑ _marks : (g : G) → {p // p ∈ P g},
          X * parityAssignmentNormalization434 J r P := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro marks hm
      exact (mul_le_mul_of_nonneg_left (hD a marks).2 hN).trans_eq (mul_comm _ _)
    _ = X * (∑ _a : (j : J) → Fin r → {p // p ∈ Q j},
        ∑ _marks : (g : G) → {p // p ∈ P g},
          parityAssignmentNormalization434 J r P) := by simp only [Finset.mul_sum]
    _ ≤ X * (X * parityAssignmentHarmonicMass434 r Q) :=
      mul_le_mul_of_nonneg_left h1 hX
    _ = _ := by ring

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalAssignmentSize -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Actual Q tail size for arbitrary tail assignments, not only source divisors. -/
theorem parity_original_assignment_Q_log_budget434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (a : (j : parityOriginalAssignmentTail434 d) →
      Fin 20 → {p // p ∈ sourceOriginalQActualBands 20 d L j.val}) :
    (∑ j : parityOriginalAssignmentTail434 d, ∑ i : Fin 20,
      Real.log ((a j i).val : ℝ)) ≤ L/25 := by
  classical
  let slotLog : ℕ → Fin 20 → ℝ := fun k i =>
    if hk : k ∈ Finset.Ico 20 (d+1) then
      Real.log ((a ⟨⟨k,(Finset.mem_Ico.mp hk).2⟩,
        (parity_mem_original_assignment_tail434 d _).mpr (Finset.mem_Ico.mp hk).1⟩ i).val : ℝ)
    else 0
  have hslot (k : ℕ) (hk : k ∈ Finset.Ico 20 (d+1)) (i : Fin 20) :
      slotLog k i ≤ (6/5 : ℝ) * (5/(11*(20 : ℝ))) * L * (1/2 : ℝ)^k := by
    let j : parityOriginalAssignmentTail434 d :=
      ⟨⟨k,(Finset.mem_Ico.mp hk).2⟩,
        (parity_mem_original_assignment_tail434 d _).mpr (Finset.mem_Ico.mp hk).1⟩
    have hp := source_original_Q_actual_prime_range 20 d L (by norm_num)
      j.val (a j i).val (a j i).property
    have hpos : (0 : ℝ) < (a j i).val := by
      exact_mod_cast (source_original_Q_actual_prime 20 d L j.val _ (a j i).property).pos
    have hl := Real.log_le_log hpos hp.2
    rw [Real.log_exp, ← source_original_Q_actual_scale_eq_P_scale 20 k L (by norm_num)] at hl
    have he :
        (6/5 : ℝ) * (sourceOriginalQActualExponent 20 k * L) =
        (6/5 : ℝ) * (5/(11*(20 : ℝ))) * L * (1/2 : ℝ)^k := by
      rw [(parity_r20_Q_exponent434 k).1]
      simp only [one_div, mul_inv_rev, inv_pow]
      ring
    rw [he] at hl
    simpa only [slotLog, dif_pos hk] using hl
  have htail := Parity.parity_original_Q_actual_dyadic_slot_tail_48_434
    20 (d+1) L hL.le slotLog hslot
  have heq :
      (∑ j : parityOriginalAssignmentTail434 d, ∑ i : Fin 20,
        Real.log ((a j i).val : ℝ)) =
      ∑ k ∈ Finset.Ico 20 (d+1), ∑ i : Fin 20, slotLog k i := by
    apply Finset.sum_bij (fun j _hj => j.val.val)
    · intro j hj
      exact Finset.mem_Ico.mpr
        ⟨(parity_mem_original_assignment_tail434 d j.val).mp j.property, j.val.isLt⟩
    · intro j hj k hk he
      exact Subtype.ext (Fin.ext he)
    · intro k hk
      exact ⟨⟨⟨k,(Finset.mem_Ico.mp hk).2⟩,
        (parity_mem_original_assignment_tail434 d _).mpr (Finset.mem_Ico.mp hk).1⟩,
        Finset.mem_univ _, rfl⟩
    · intro j hj
      have hk : j.val.val ∈ Finset.Ico 20 (d+1) := Finset.mem_Ico.mpr
        ⟨(parity_mem_original_assignment_tail434 d j.val).mp j.property, j.val.isLt⟩
      apply Finset.sum_congr rfl
      intro i hi
      simp only [slotLog, dif_pos hk]
  rw [heq]
  refine htail.trans ?_
  norm_num at *
  linarith

theorem parity_original_assignment_P_log_budget_eventually434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ marks : (g : sourceOriginalPAllGroupType 20 L) →
        {p // p ∈ sourceOriginalPAllActualBands 20 L g},
      (∑ g : sourceOriginalPAllGroupType 20 L,
        Real.log ((marks g).val : ℝ)) ≤ L/100 := by
  have hsmall := (isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 3/5 by norm_num)).bound (show (0 : ℝ) < 1/400 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 2)] with L hb hL
  have he : (1 : ℝ) ≤ Real.exp 2 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 by norm_num))
  have h1 : 1 ≤ L := he.trans hL
  have h0 : 0 < L := lt_of_lt_of_le zero_lt_one h1
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg h1
  have hr4 : 0 ≤ L^(2/5 : ℝ) := Real.rpow_nonneg h0.le _
  have hr6 : 0 ≤ L^(3/5 : ℝ) := Real.rpow_nonneg h0.le _
  have hb' : Real.log L ≤ (1/400 : ℝ) * L^(3/5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hr6] using hb
  have hprod : L^(3/5 : ℝ) * L^(2/5 : ℝ) = L := by
    rw [← Real.rpow_add h0]
    norm_num
  have hbudget : 4 * Real.log L * L^(2/5 : ℝ) ≤ L/100 := by
    have hm := mul_le_mul_of_nonneg_right hb' hr4
    nlinarith [hm]
  intro marks
  have hc : (Fintype.card (sourceOriginalPAllGroupType 20 L) : ℝ) ≤ 4 * Real.log L := by
    simpa only [sourceOriginalPAllGroupType, Fintype.card_coe] using
      parity_original_all_group_indices_card_four434 20 L hL
  calc
    _ ≤ (Fintype.card (sourceOriginalPAllGroupType 20 L) : ℝ) * L^(2/5 : ℝ) := by
      have hs := Finset.sum_le_sum (fun g (_hg : g ∈ (Finset.univ :
          Finset (sourceOriginalPAllGroupType 20 L))) =>
        source_original_P_all_actual_band_log 20 L h1 g _ (marks g).property)
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs
    _ ≤ 4 * Real.log L * L^(2/5 : ℝ) := mul_le_mul_of_nonneg_right hc hr4
    _ ≤ L/100 := hbudget

/-- Actual (6.2) modulus size, retaining repeated Q primes and all P marks. -/
theorem parity_original_assignment_modulus_size_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℕ,
      ∀ (a : (j : parityOriginalAssignmentTail434 d) →
        Fin 20 → {p // p ∈ sourceOriginalQActualBands 20 d L j.val})
      (marks : (g : sourceOriginalPAllGroupType 20 L) →
        {p // p ∈ sourceOriginalPAllActualBands 20 L g}),
      0 < parityAssignmentModulus434 20
        (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
        (sourceOriginalPAllActualBands 20 L) a marks ∧
      (parityAssignmentModulus434 20
        (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
        (sourceOriginalPAllActualBands 20 L) a marks : ℝ) ≤ Real.exp (L/20) := by
  filter_upwards [parity_original_assignment_P_log_budget_eventually434,
    eventually_gt_atTop (0 : ℝ)] with L hP hL
  intro d a marks
  have hq (j : parityOriginalAssignmentTail434 d) (i : Fin 20) : 0 < (a j i).val :=
    (source_original_Q_actual_prime 20 d L j.val _ (a j i).property).pos
  have hp (g : sourceOriginalPAllGroupType 20 L) : 0 < (marks g).val :=
    (source_original_P_all_actual_band_prime 20 L g _ (marks g).property).pos
  have hQnat : 0 < ∏ j : parityOriginalAssignmentTail434 d, ∏ i : Fin 20, (a j i).val :=
    Finset.prod_pos (fun j hj => Finset.prod_pos (fun i hi => hq j i))
  have hPnat : 0 < ∏ g : sourceOriginalPAllGroupType 20 L, (marks g).val :=
    Finset.prod_pos (fun g hg => hp g)
  have hQpos : (0 : ℝ) <
      ((∏ j : parityOriginalAssignmentTail434 d, ∏ i : Fin 20, (a j i).val : ℕ) : ℝ) := by
    exact_mod_cast hQnat
  have hPpos : (0 : ℝ) <
      ((∏ g : sourceOriginalPAllGroupType 20 L, (marks g).val : ℕ) : ℝ) := by
    exact_mod_cast hPnat
  have hQL :
      Real.log ((∏ j : parityOriginalAssignmentTail434 d, ∏ i : Fin 20, (a j i).val : ℕ) : ℝ) =
      ∑ j : parityOriginalAssignmentTail434 d, ∑ i : Fin 20, Real.log ((a j i).val : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_prod, Real.log_prod]
      intro i hi
      exact ne_of_gt (by exact_mod_cast hq j i)
    · intro j hj
      exact ne_of_gt (by exact_mod_cast Finset.prod_pos (fun i hi => hq j i))
  have hPL :
      Real.log ((∏ g : sourceOriginalPAllGroupType 20 L, (marks g).val : ℕ) : ℝ) =
      ∑ g : sourceOriginalPAllGroupType 20 L, Real.log ((marks g).val : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro g hg
    exact ne_of_gt (by exact_mod_cast hp g)
  refine ⟨mul_pos hQnat hPnat, ?_⟩
  apply (Real.log_le_iff_le_exp (by
    change (0 : ℝ) < (((∏ j : parityOriginalAssignmentTail434 d,
      ∏ i : Fin 20, (a j i).val) * (∏ g, (marks g).val) : ℕ) : ℝ)
    exact_mod_cast mul_pos hQnat hPnat)).mp
  unfold parityAssignmentModulus434
  rw [Nat.cast_mul, Real.log_mul (ne_of_gt hQpos) (ne_of_gt hPpos), hQL, hPL]
  have hqb := parity_original_assignment_Q_log_budget434 d L hL a
  have hpb := hP marks
  linarith

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalAssignmentMoments -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Exactly twenty omitted macro bands; every full-source normalized Q factor
has a fixed positive floor. Thus the loss is constant in L. -/
theorem parity_tail_HQ_le_full_HQ_of_band_floor434
    (d : ℕ) (L : ℝ) (hd : 20 ≤ d)
    (hF : ∀ j : Fin (d+1), 1/(200 : ℝ)^20 ≤
      (∑ p ∈ sourceOriginalQActualBands 20 d L j, (p : ℝ)⁻¹)^20 /
        (Nat.factorial 20 : ℝ)) :
    parityAssignmentHarmonicMass434 20
      (fun j : parityOriginalAssignmentTail434 d =>
        sourceOriginalQActualBands 20 d L j.val) ≤
      (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L := by
  classical
  let s := parityOriginalAssignmentTail434 d
  let m : Finset (Fin (d+1)) := Finset.univ \ s
  let F : Fin (d+1) → ℝ := fun j =>
    (∑ p ∈ sourceOriginalQActualBands 20 d L j, (p : ℝ)⁻¹)^20 /
      (Nat.factorial 20 : ℝ)
  have hm : m = Finset.Iio (⟨20,by omega⟩ : Fin (d+1)) := by
    ext j
    simp only [m, Finset.mem_sdiff, Finset.mem_univ, true_and,
      s, parity_mem_original_assignment_tail434, Finset.mem_Iio]
    exact not_le
  have hc : m.card = 20 := by rw [hm, Fin.card_Iio]
  have htail :
      parityAssignmentHarmonicMass434 20
        (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val) =
      ∏ j ∈ s, F j := by
    unfold parityAssignmentHarmonicMass434
    exact Finset.prod_coe_sort s F
  have htn : 0 ≤ ∏ j ∈ s, F j :=
    Finset.prod_nonneg (fun j hj => le_trans (by positivity) (hF j))
  have hmacro : (1/(200 : ℝ)^20)^20 ≤ ∏ j ∈ m, F j := by
    calc
      _ = ∏ _j ∈ m, (1/(200 : ℝ)^20) := by rw [Finset.prod_const, hc]
      _ ≤ _ := Finset.prod_le_prod₀ (fun j hj => by positivity) (fun j hj => hF j)
  have hpow : (1/(200 : ℝ)^20)^20 = 1/(200 : ℝ)^400 := by
    rw [div_pow, one_pow, ← pow_mul]
  rw [hpow] at hmacro
  have hfull : (∏ j ∈ m, F j) * (∏ j ∈ s, F j) =
      sourceOriginalQActualHQ 20 d L :=
    Finset.prod_sdiff (f := F) (Finset.subset_univ s)
  rw [htail]
  have hmain : (∏ j ∈ s, F j) / (200 : ℝ)^400 ≤ sourceOriginalQActualHQ 20 d L := by
    have h := mul_le_mul_of_nonneg_right hmacro htn
    rw [hfull] at h
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h
  exact ((div_le_iff₀ (by positivity : (0 : ℝ) < (200 : ℝ)^400)).mp hmain).trans_eq
    (mul_comm _ _)

theorem parity_original_tail_HQ_le_full_HQ_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℕ,
      sourceOriginalDepthAdmissible 20 d L → 20 ≤ d →
      parityAssignmentHarmonicMass434 20
        (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val) ≤
      (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L := by
  filter_upwards [b635_actual_moving_Q_twelfth_floor434 20 (by norm_num)] with L hL
  intro d hd h20
  apply parity_tail_HQ_le_full_HQ_of_band_floor434 d L h20
  intro j
  have hV := hL d hd j.val (Nat.le_of_lt_succ j.isLt)
  change (1/12 : ℝ) ≤ ∑ p ∈ sourceOriginalQActualBands 20 d L j, (p : ℝ)⁻¹ at hV
  exact b635_parity_band_factor_numeric434.1.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hV 20) (by positivity))

/-- Actual original (6.2), including its eta*D1 consequence, at literal depth.
The constant 200^400 is fixed before L and no H_P or log loss appears. -/
theorem parity_original_literal_assignment_three_moments434 :
    ∀ᶠ L : ℝ in atTop,
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      let eta := parityAssignmentNormalization434 (parityOriginalAssignmentTail434 d) 20 P
      (∀ (a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j})
        (marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g}),
        0 < parityAssignmentModulus434 20 Q P a marks ∧
          (parityAssignmentModulus434 20 Q P a marks : ℝ) ≤ Real.exp (L/20)) ∧
      (∑ a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j},
        ∑ marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g},
          eta / (parityAssignmentModulus434 20 Q P a marks : ℝ)) ≤
        (200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L ∧
      (∑ _a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j},
        ∑ _marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g}, eta) ≤
        (200 : ℝ)^400 * Real.exp (L/20) * sourceOriginalQActualHQ 20 d L ∧
      (∑ a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j},
        ∑ marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g},
          eta * (parityAssignmentModulus434 20 Q P a marks : ℝ)) ≤
        (200 : ℝ)^400 * Real.exp (L/10) * sourceOriginalQActualHQ 20 d L := by
  filter_upwards [parity_original_assignment_modulus_size_eventually434,
    parity_original_tail_HQ_le_full_HQ_eventually434,
    source_original_P_all_actual_local_eventually 20,
    source_original_literal_depth_properties_eventually 20 (by norm_num),
    source_original_literal_depth_grows 20 20 (by norm_num)] with L hsize hHQ hP hdepth h20
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
  let P := sourceOriginalPAllActualBands 20 L
  have hV : ∀ g : sourceOriginalPAllGroupType 20 L,
      (∑ p ∈ P g, (p : ℝ)⁻¹) ≠ 0 := by
    intro g
    apply ne_of_gt
    exact Finset.sum_pos (fun p hp => inv_pos.mpr (by
      exact_mod_cast (source_original_P_all_actual_band_prime 20 L g p hp).pos)) (hP.1 g)
  have hs (a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j})
      (marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g}) :
      0 < (parityAssignmentModulus434 20 Q P a marks : ℝ) ∧
        (parityAssignmentModulus434 20 Q P a marks : ℝ) ≤ Real.exp (L/20) :=
    ⟨by exact_mod_cast (hsize d a marks).1, (hsize d a marks).2⟩
  have hm := parity_assignment_reciprocal_mass_exact434 20 Q P hV
  have hb := parity_assignment_two_moments_of_size434 20 Q P hV
    (Real.exp (L/20)) (Real.exp_pos _).le hs
  have hq := hHQ d hdepth.1 h20
  refine ⟨hsize d, ?_, ?_, ?_⟩
  · exact hm.le.trans hq
  · calc
      _ ≤ Real.exp (L/20) * parityAssignmentHarmonicMass434 20 Q := hb.1
      _ ≤ Real.exp (L/20) * ((200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L) :=
        mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = _ := by ring
  · have he : (Real.exp (L/20))^2 = Real.exp (L/10) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (Real.exp (L/20))^2 * parityAssignmentHarmonicMass434 20 Q := hb.2
      _ = Real.exp (L/10) * parityAssignmentHarmonicMass434 20 Q := by rw [he]
      _ ≤ Real.exp (L/10) * ((200 : ℝ)^400 * sourceOriginalQActualHQ 20 d L) :=
        mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = _ := by ring

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalAssignmentCRTInputs -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
open Filter
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

theorem parity_original_assignment_P_below_mask_cutoff_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ g : sourceOriginalPAllGroupType 20 L, ∀ p,
      p ∈ sourceOriginalPAllActualBands 20 L g →
      (p : ℝ) ≤ Real.exp (parityOriginalAssignmentTheta434 * L) := by
  have ht : 0 < parityOriginalAssignmentTheta434 := by
    norm_num [parityOriginalAssignmentTheta434]
  have hs := (tendsto_rpow_atTop (show (0 : ℝ) < 3/5 by norm_num)).eventually_ge_atTop
    parityOriginalAssignmentTheta434⁻¹
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hsmall hL
  have h0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpw : L^(3/5 : ℝ) * L^(2/5 : ℝ) = L := by
    rw [← Real.rpow_add h0]
    norm_num
  have hh : 1 ≤ parityOriginalAssignmentTheta434 * L^(3/5 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall ht.le
    simpa only [mul_inv_cancel₀ ht.ne'] using h
  have hb : L^(2/5 : ℝ) ≤ parityOriginalAssignmentTheta434 * L := by
    have h := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg h0.le (2/5 : ℝ))
    simpa only [one_mul, mul_assoc, hpw] using h
  intro g p hp
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (source_original_P_all_actual_band_prime 20 L g p hp).pos
  exact (Real.log_le_iff_le_exp hp0).mp
    ((source_original_P_all_actual_band_log 20 L hL g p hp).trans hb)

/-- The original Q intervals are closed prime bands, not definitionally odd.
Oddness follows from the genuine literal-depth scale lower bound. -/
theorem parity_original_literal_Q_primes_ge_three_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ j : Fin (sourceOriginalLiteralDepth 20 L + 1), ∀ p,
      p ∈ sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L j →
      3 ≤ p := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with L hdepth hL
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hL
  have hlog : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  intro j p hp
  have hs := b635_admissible_all_scales434 20 (sourceOriginalLiteralDepth 20 L)
    j.val L (by norm_num) hL0.le hdepth.1 (Nat.le_of_lt_succ j.isLt)
  have hlo := (source_original_Q_actual_prime_range
    20 (sourceOriginalLiteralDepth 20 L) L (by norm_num) j p hp).1
  rw [← source_original_Q_actual_scale_eq_P_scale 20 j.val L (by norm_num)] at hlo
  have h3 : (3 : ℝ) ≤ p := by
    have he : (3 : ℝ) ≤ Real.exp 20 := by
      have h := Real.add_one_le_exp (20 : ℝ)
      linarith
    exact (he.trans (Real.exp_le_exp.mpr (by linarith : (20 : ℝ) ≤
      sourceOriginalQActualExponent 20 j.val * L))).trans hlo
  exact_mod_cast h3

theorem parity_prime_ge_three_coprime_two434 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    Nat.Coprime 2 p := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hd
  have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
  omega

/-- All actual CRT root and banned-prime premises are discharged from the
literal source; repeated factors of D1 are allowed throughout. -/
theorem parity_original_literal_assignment_CRT_inputs_eventually434 :
    ∀ᶠ L : ℝ in atTop,
      let d := sourceOriginalLiteralDepth 20 L
      let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
      let P := sourceOriginalPAllActualBands 20 L
      let z := Real.exp (parityOriginalAssignmentTheta434 * L)
      ∀ (a : (j : parityOriginalAssignmentTail434 d) → Fin 20 → {p // p ∈ Q j})
      (marks : (g : sourceOriginalPAllGroupType 20 L) → {p // p ∈ P g}),
      let D := parityAssignmentModulus434 20 Q P a marks
      0 < D ∧ Nat.Coprime 2 D ∧
      ∀ S ∈ (parityAssignmentMaskUniverse434 P D).powerset,
        ∀ p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P) D ∪
          (parityAssignmentMaskUniverse434 P D \ S),
          p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ z ∧ ¬ p ∣ D := by
  filter_upwards [parity_original_assignment_modulus_size_eventually434,
    parity_original_literal_Q_primes_ge_three_eventually434,
    source_original_P_all_actual_local_eventually 20,
    parity_original_assignment_P_below_mask_cutoff_eventually434] with L hsize hQ3 hP hPsmall
  dsimp only
  intro a marks
  let d := sourceOriginalLiteralDepth 20 L
  let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
  let P := sourceOriginalPAllActualBands 20 L
  let D := parityAssignmentModulus434 20 Q P a marks
  have h2Q : Nat.Coprime 2 (∏ j : parityOriginalAssignmentTail434 d, ∏ i : Fin 20, (a j i).val) := by
    apply Nat.Coprime.prod_right
    intro j hj
    apply Nat.Coprime.prod_right
    intro i hi
    exact parity_prime_ge_three_coprime_two434 _ (source_original_Q_actual_prime 20 d L
      j.val _ (a j i).property) (hQ3 j.val _ (a j i).property)
  have h2P : Nat.Coprime 2 (∏ g : sourceOriginalPAllGroupType 20 L, (marks g).val) := by
    apply Nat.Coprime.prod_right
    intro g hg
    exact parity_prime_ge_three_coprime_two434 _ (source_original_P_all_actual_band_prime
      20 L g _ (marks g).property) (le_trans (by norm_num) (hP.2.1 g _ (marks g).property))
  refine ⟨(hsize d a marks).1, h2Q.mul_right h2P, ?_⟩
  intro S hS p hp
  rcases Finset.mem_union.mp hp with hb | hg
  · obtain ⟨hodd, hnP, hnD⟩ := Finset.mem_filter.mp hb
    obtain ⟨hI, hpPrime⟩ := Finset.mem_filter.mp hodd
    have hI' := Finset.mem_Icc.mp hI
    refine ⟨hpPrime, hI'.1, ?_, hnD⟩
    have hfloor : (p : ℝ) ≤ ⌊Real.exp (parityOriginalAssignmentTheta434 * L)⌋₊ := by
      exact_mod_cast hI'.2
    exact hfloor.trans (Nat.floor_le (Real.exp_pos _).le)
  · obtain ⟨hpU, hpS⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hpP, hpD⟩ := Finset.mem_filter.mp hpU
    obtain ⟨g, hg, hpG⟩ := Finset.mem_biUnion.mp hpP
    exact ⟨source_original_P_all_actual_band_prime 20 L g p hpG,
      le_trans (by norm_num) (hP.2.1 g p hpG), hPsmall g p hpG, hpD⟩

end Green64Analytic.SourceBlockSieve

end

/-! ## OriginalAssignmentPairCount -/

section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

theorem parity_no_banned_indicator434 (B : Finset ℕ) (u : ℕ) :
    (∏ p ∈ B, if p ∣ u then (0 : ℝ) else 1) =
      if ∀ p ∈ B, ¬ p ∣ u then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∀ p ∈ B, ¬ p ∣ u
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun p hp => by simp [h p hp])
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hp, hpu⟩ := h
    exact Finset.prod_eq_zero hp (by simp [hpu])

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open SourceBlockSieve

/-- Original integer coordinates are retained. This is the actual shifted
sifted pair set after removing only the u cutoff, with u=mn-2. -/
noncomputable def parityOriginalAssignmentSiftedPairs434
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (D : ℕ) (B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (K.product J).filter (fun z =>
    0 < z.1 ∧ 0 < z.2 ∧ 2 ≤ z.1*z.2 ∧
    D ∣ (z.1*z.2-2) ∧ R z ∧ ∀ p ∈ B, ¬ p ∣ (z.1*z.2-2))

theorem parity_original_fibre_assignment_indicator434
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (D u : ℕ) (B : Finset ℕ) :
    (if D ∣ u then ∏ p ∈ B, if p ∣ u then (0 : ℝ) else 1 else 0) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if R z then (1 : ℝ) else 0) =
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      if D ∣ u ∧ R z ∧ (∀ p ∈ B, ¬ p ∣ u) then (1 : ℝ) else 0 := by
  classical
  rw [parity_no_banned_indicator434, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hD : D ∣ u <;>
    by_cases hR : R z <;>
    by_cases hB : ∀ p ∈ B, ¬ p ∣ u <;> simp [hD, hR, hB]

/-- Source triples inject into integer pairs because mn=u+2 determines u.
No inverse-two transformation of the box or assumed source equality is used. -/
theorem parity_original_fibre_assignment_count_le_pairs434
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (D Y : ℕ) (B : Finset ℕ) :
    (∑ u ∈ Finset.range (Y+1),
      ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if D ∣ u ∧ R z ∧ (∀ p ∈ B, ¬ p ∣ u) then (1 : ℝ) else 0) ≤
    (parityOriginalAssignmentSiftedPairs434 K J R D B).card := by
  classical
  let C := fun u => (parityOriginalShiftTwoPositivePairFibre434 K J u).filter
    (fun z => D ∣ u ∧ R z ∧ (∀ p ∈ B, ¬ p ∣ u))
  have hc (u : ℕ) :
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if D ∣ u ∧ R z ∧ (∀ p ∈ B, ¬ p ∣ u) then (1 : ℝ) else 0) =
        ((C u).card : ℝ) := by
    simp [C, Finset.sum_ite]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (Y+1))) C := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro z hzu hzv
    have hfu := (Finset.mem_filter.mp (Finset.mem_filter.mp hzu).1).2.2.2
    have hfv := (Finset.mem_filter.mp (Finset.mem_filter.mp hzv).1).2.2.2
    exact huv (by omega)
  have hcard : ((Finset.range (Y+1)).biUnion C).card =
      ∑ u ∈ Finset.range (Y+1), (C u).card :=
    Finset.card_biUnion hdisj
  have hsub : (Finset.range (Y+1)).biUnion C ⊆ parityOriginalAssignmentSiftedPairs434 K J R D B := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hf, hD, hR, hB⟩ := Finset.mem_filter.mp hzu
    obtain ⟨hKJ, hm, hn, hshift⟩ := Finset.mem_filter.mp hf
    have hsub : z.1*z.2-2 = u := by omega
    exact Finset.mem_filter.mpr ⟨hKJ, hm, hn, by omega, by simpa [hsub] using hD,
      hR, by simpa [hsub] using hB⟩
  calc
    _ = ∑ u ∈ Finset.range (Y+1), ((C u).card : ℝ) :=
      Finset.sum_congr rfl (fun u hu => hc u)
    _ = (((Finset.range (Y+1)).biUnion C).card : ℝ) := by exact_mod_cast hcard.symm
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end Green64Analytic.Parity

end

/-! ## OriginalBalancedAssignmentJoin -/

section

set_option maxHeartbeats 500000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.Parity
open SourceBlockSieve

noncomputable def parityOriginalAssignmentPairBound434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ)
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) : ℝ :=
  ∑ a : (j : T) → Fin r → {p // p ∈ Q j},
    ∑ marks : (g : G) → {p // p ∈ P g},
      parityAssignmentNormalization434 T r P *
        ∑ S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
          (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
            (parityAssignmentModulus434 r Q P a marks)).card *
          (parityOriginalAssignmentSiftedPairs434 K J R
            (parityAssignmentModulus434 r Q P a marks)
            (parityAssignmentDetBans434 z (Finset.univ.biUnion P)
              (parityAssignmentModulus434 r Q P a marks) ∪
              (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S))).card

theorem parity_assignment_majorant_nonneg434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ) (u : ℕ) :
    0 ≤ parityAssignmentMajorant434 r Q P z u := by
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro marks hm
  split_ifs
  · exact mul_nonneg (parity_assignment_normalization_nonneg434 T r P)
      (parity_assignment_mask_average_nonneg434 P z _ u)
  · exact le_rfl

/-- Exact finite distribution of the proved source majorant through its
original positive shifted fibre. -/
theorem parity_assignment_majorant_fibre_expansion434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ)
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (u : ℕ) :
    parityAssignmentMajorant434 r Q P z u *
      (∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if R v then (1 : ℝ) else 0) =
    ∑ a : (j : T) → Fin r → {p // p ∈ Q j},
      ∑ marks : (g : G) → {p // p ∈ P g},
        parityAssignmentNormalization434 T r P *
          ∑ S ∈ (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks)).powerset,
            (1/2 : ℝ)^(parityAssignmentMaskUniverse434 P
              (parityAssignmentModulus434 r Q P a marks)).card *
            ∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
              if parityAssignmentModulus434 r Q P a marks ∣ u ∧ R v ∧
                (∀ p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
                  (parityAssignmentModulus434 r Q P a marks) ∪
                    (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S),
                  ¬ p ∣ u) then (1 : ℝ) else 0 := by
  classical
  unfold parityAssignmentMajorant434
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro marks hm
  by_cases hd : parityAssignmentModulus434 r Q P a marks ∣ u
  · rw [if_pos hd]
    unfold parityAssignmentMaskAverage434
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [mul_assoc]
    congr 1
    have hi := parity_original_fibre_assignment_indicator434 K J R
      (parityAssignmentModulus434 r Q P a marks) u
      (parityAssignmentDetBans434 z (Finset.univ.biUnion P)
        (parityAssignmentModulus434 r Q P a marks) ∪
        (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S))
    by_cases hB : ∀ p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
        (parityAssignmentModulus434 r Q P a marks) ∪
        (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S), ¬ p ∣ u
    · simpa [hd, hB] using hi
    · simpa [hd, hB] using hi
  · simp only [if_neg hd, zero_mul, hd, false_and, if_false,
      Finset.sum_const_zero, mul_zero]

/-- Sum the genuine source fibres, then drop their cutoff by the proved
mn=u+2 injection. This is an upper bound, not a stipulated carrier identity. -/
theorem parity_assignment_majorant_fibre_sum_le_pairs434
    {T G : Type} [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]
    (r : ℕ) (Q : T → Finset ℕ) (P : G → Finset ℕ) (z : ℝ)
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (Y : ℕ) :
    (∑ u ∈ Finset.range (Y+1),
      parityAssignmentMajorant434 r Q P z u *
        ∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          if R v then (1 : ℝ) else 0) ≤
    parityOriginalAssignmentPairBound434 r Q P z K J R := by
  classical
  simp_rw [parity_assignment_majorant_fibre_expansion434]
  rw [Finset.sum_comm]
  unfold parityOriginalAssignmentPairBound434
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro marks hm
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (parity_assignment_normalization_nonneg434 T r P)
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro S hS
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc := parity_original_fibre_assignment_count_le_pairs434 K J R
    (parityAssignmentModulus434 r Q P a marks) Y
    (parityAssignmentDetBans434 z (Finset.univ.biUnion P)
      (parityAssignmentModulus434 r Q P a marks) ∪
      (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S))
  refine le_trans ?_ hc
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  by_cases hb : parityAssignmentModulus434 r Q P a marks ∣ u ∧ R v ∧
      ∀ p ∈ parityAssignmentDetBans434 z (Finset.univ.biUnion P)
        (parityAssignmentModulus434 r Q P a marks) ∪
        (parityAssignmentMaskUniverse434 P (parityAssignmentModulus434 r Q P a marks) \ S), ¬ p ∣ u
  · simp only [hb, ite_true, le_refl]
  · simp only [hb, ite_false, le_refl]

/-- The original AρΨ source, including its u=0 term, is bounded by actual
assignment/mask sifted integer pairs. Both parity signs and multiplicities remain. -/
theorem parity_original_weighted_fibre_le_assignment_pairs434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (rho : ℝ) (hRho : |rho| ≤ 1)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (hPsiNonneg : ∀ x, 0 ≤ Psi x) (hPsiOne : ∀ x, Psi x ≤ 1)
    (K J : Finset ℕ) (R : ℕ × ℕ → Prop) (Y : ℕ) :
    (∑ u ∈ Finset.range (Y+1),
      (parityWeight d L rho u * Psi ((u : ℝ)/Real.exp L)) *
        ∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          if R v then (1 : ℝ) else 0) ≤
    parityOriginalAssignmentPairBound434 20
      (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
      (sourceOriginalPAllActualBands 20 L)
      (Real.exp (parityOriginalAssignmentTheta434 * L)) K J R := by
  classical
  let Q := fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val
  let P := sourceOriginalPAllActualBands 20 L
  let z := Real.exp (parityOriginalAssignmentTheta434 * L)
  have hcount (u : ℕ) : 0 ≤ ∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      if R v then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun v hv => by split_ifs <;> norm_num)
  calc
    _ ≤ ∑ u ∈ Finset.range (Y+1),
        parityAssignmentMajorant434 20 Q P z u *
          ∑ v ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            if R v then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hu0 : u = 0
      · subst u
        simp only [Nat.cast_zero, zero_div, hPsi0, mul_zero, zero_mul]
        exact mul_nonneg (parity_assignment_majorant_nonneg434 20 Q P z 0) (hcount 0)
      · apply mul_le_mul_of_nonneg_right _ (hcount u)
        calc
          parityWeight d L rho u * Psi ((u : ℝ)/Real.exp L) ≤
            parityWeight d L rho u := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left
                (hPsiOne ((u : ℝ)/Real.exp L)) (parity_original_parity_A_nonneg434 d L rho hRho u)
          _ ≤ parityAssignmentMajorant434 20 Q P z u :=
            parity_original_parity_assignment_mask_majorant434 d L hL rho hRho u hu0
    _ ≤ _ := parity_assignment_majorant_fibre_sum_le_pairs434 20 Q P z K J R Y

/-- Source-facing downstream endpoint: the exact balanced double-W-rough
mass beneath the accepted 9/(L²V(W)²) proxy bound. Both Bκ restrictions,
ordered orientations and the diagonal are preserved. -/
theorem parity_original_balanced_double_rough_le_assignment_pairs434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (rho : ℝ) (hRho : |rho| ≤ 1)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (hPsiNonneg : ∀ x, 0 ≤ Psi x) (hPsiOne : ∀ x, Psi x ≤ 1)
    (kappa : ℝ) (Y : ℕ) :
    balancedRoughPairMass d L rho Psi kappa Y ≤
    parityOriginalAssignmentPairBound434 20
      (fun j : parityOriginalAssignmentTail434 d => sourceOriginalQActualBands 20 d L j.val)
      (sourceOriginalPAllActualBands 20 L)
      (Real.exp (parityOriginalAssignmentTheta434 * L))
      ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
      ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
      (fun v => sourceD20Rough (Real.exp (Real.sqrt L)) v.1 ∧
        sourceD20Rough (Real.exp (Real.sqrt L)) v.2) := by
  classical
  have h := parity_original_weighted_fibre_le_assignment_pairs434 d L hL rho hRho
    Psi hPsi0 hPsiNonneg hPsiOne
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    (fun v => sourceD20Rough (Real.exp (Real.sqrt L)) v.1 ∧
      sourceD20Rough (Real.exp (Real.sqrt L)) v.2) Y
  refine le_trans ?_ h
  unfold balancedRoughPairMass
  apply Finset.sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg
    (parity_original_parity_A_nonneg434 d L rho hRho u) (hPsiNonneg _))
  apply Finset.sum_le_sum
  intro v hv
  by_cases hr : sourceD20Rough (Real.exp (Real.sqrt L)) v.1 ∧
      sourceD20Rough (Real.exp (Real.sqrt L)) v.2
  · simp only [hr, ite_true, le_refl]
  · simp only [hr, ite_false, le_refl]

end Green64Analytic.Parity

end

/-! ## OriginalShiftTwoBoxMoments -/

section

set_option maxHeartbeats 1500000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT

noncomputable def parityOriginalShiftTwoBoxObjects434
    (D A B C E : ℕ) : Finset (ℕ × ℕ) :=
  parityOriginalShiftTwoIntegerBox434 D 1 (fun _ => True) A B C E

noncomputable def parityOriginalShiftTwoBoxBad434
    (P : Finset ℕ) (rough banned : ℕ → Bool) (xy : ℕ × ℕ) : Finset ℕ :=
  P.filter (fun p => parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
    ((xy.1 : ZMod p), (xy.2 : ZMod p)))

noncomputable def parityOriginalShiftTwoBoxDensity434
    (rough banned : ℕ → Bool) (p : ℕ) : ℝ :=
  (localNu p (rough p) (banned p) : ℝ) / (p : ℝ)^2

noncomputable def parityOriginalShiftTwoBoxMass434 (D A B C E : ℕ) : ℝ :=
  (D.totient : ℝ) * ((B-A : ℕ) : ℝ) * ((E-C : ℕ) : ℝ) / (D : ℝ)^2

/-- Projection for every integer pair, including pairs below the shifted
positive source. It makes no transformation of the rectangle. -/
theorem parity_original_squarefree_bad_nat_flags434
    (d m n : ℕ) (hd : Squarefree d) (rough banned : ℕ → Bool) :
    parityOriginalShiftTwoSquarefreeBad434 d hd rough banned
      ((m : ZMod d), (n : ZMod d)) ↔
      ∀ p ∈ d.primeFactors, parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
        ((m : ZMod p), (n : ZMod p)) := by
  constructor
  · intro h p hp
    have ht := h ⟨p,hp⟩
    simpa only [parity_original_squarefree_pair_projection_nat434] using ht
  · intro h p
    rw [parity_original_squarefree_pair_projection_nat434]
    exact h p.val p.property

theorem parity_prime_finset_product_squarefree434 (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp
    exact (hs p hp).squarefree

theorem parity_boolean_product_indicator434 (s t : Finset ℕ) :
    (∏ p ∈ s, if p ∈ t then (1 : ℝ) else 0) =
      if ∀ p ∈ s, p ∈ t then 1 else 0 := by
  classical
  by_cases h : ∀ p ∈ s, p ∈ t
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun p hp => if_pos (h p hp))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p,hp,hpt⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hpt)

/-- Every finite moment is the genuine product-two masked-box count. The
moment identity is proved from original coordinates, not supplied as a premise. -/
theorem parity_original_shift_two_box_moment434
    (D A B C E : ℕ) (hD : 0 < D)
    (P s : Finset ℕ) (hs : s ⊆ P) (hp : ∀ p ∈ s, p.Prime)
    (rough banned : ℕ → Bool) :
    (∑ xy ∈ parityOriginalShiftTwoBoxObjects434 D A B C E,
      (1 : ℝ) * ∏ p ∈ s,
        if p ∈ parityOriginalShiftTwoBoxBad434 P rough banned xy then 1 else 0) =
    parityOriginalShiftTwoBoxMass434 D A B C E *
      (∏ p ∈ s, parityOriginalShiftTwoBoxDensity434 rough banned p) +
      parityOriginalShiftTwoMaskedRemainder434 D (∏ p ∈ s, p) A B C E rough banned := by
  classical
  let d := ∏ p ∈ s, p
  have hd : Squarefree d := parity_prime_finset_product_squarefree434 s hp
  have hpf : d.primeFactors = s := Nat.primeFactors_prod hp
  let pred : ℕ × ℕ → Prop := fun xy =>
    parityOriginalShiftTwoSquarefreeBad434 d hd rough banned
      ((xy.1 : ZMod d), (xy.2 : ZMod d))
  have hind (xy : ℕ × ℕ) :
      (∏ p ∈ s, if p ∈ parityOriginalShiftTwoBoxBad434 P rough banned xy then (1 : ℝ) else 0) =
      if pred xy then 1 else 0 := by
    rw [parity_boolean_product_indicator434]
    have hi : (∀ p ∈ s, p ∈ parityOriginalShiftTwoBoxBad434 P rough banned xy) ↔ pred xy := by
      dsimp only [pred]
      rw [parity_original_squarefree_bad_nat_flags434, hpf]
      constructor
      · intro h p hps
        exact (Finset.mem_filter.mp (h p hps)).2
      · intro h p hps
        exact Finset.mem_filter.mpr ⟨hs hps, h p hps⟩
    exact if_congr hi rfl rfl
  have hf :
      (parityOriginalShiftTwoBoxObjects434 D A B C E).filter pred =
      parityOriginalShiftTwoIntegerBox434 D d
        (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) A B C E := by
    ext xy
    simp only [parityOriginalShiftTwoBoxObjects434, parityOriginalShiftTwoIntegerBox434,
      Finset.mem_filter, and_true, pred, and_assoc]
  have hcount :
      (∑ xy ∈ parityOriginalShiftTwoBoxObjects434 D A B C E,
        (1 : ℝ) * ∏ p ∈ s,
          if p ∈ parityOriginalShiftTwoBoxBad434 P rough banned xy then 1 else 0) =
      ((parityOriginalShiftTwoIntegerBox434 D d
        (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) A B C E).card : ℝ) := by
    simp_rw [one_mul, hind]
    rw [← hf]
    simp [Finset.sum_filter]
  have hmain :
      parityOriginalShiftTwoBoxMass434 D A B C E *
        (∏ p ∈ s, parityOriginalShiftTwoBoxDensity434 rough banned p) =
      ((D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (((B-A : ℕ) : ℝ) * ((E-C : ℕ) : ℝ) / ((D*d : ℕ) : ℝ)^2) := by
    rw [hpf]
    simp only [parityOriginalShiftTwoBoxMass434, parityOriginalShiftTwoBoxDensity434,
      Finset.prod_div_distrib, ← Finset.prod_pow, d, Nat.cast_mul, Nat.cast_prod, mul_pow]
    ring
  rw [hcount]
  change _ = _ + parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned
  rw [parityOriginalShiftTwoMaskedRemainder434, dif_pos hd, hmain]
  ring

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoBoxSieve -/

section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT
open SourceBlockSieve

noncomputable def parityOriginalShiftTwoBoxSifted434
    (D A B C E : ℕ) (P : Finset ℕ) (rough banned : ℕ → Bool) : Finset (ℕ × ℕ) :=
  (parityOriginalShiftTwoBoxObjects434 D A B C E).filter (fun xy =>
    ∀ p ∈ P, ¬ parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
      ((xy.1 : ZMod p), (xy.2 : ZMod p)))

noncomputable def parityOriginalShiftTwoSieveRho434 (h : ℕ) : ℝ :=
  ((Real.exp (Real.exp 1 * 12)/(1-Real.exp (-1)))/Real.exp (-12/(2/9 : ℝ))) *
    Real.exp (-(h : ℝ))

noncomputable def parityOriginalShiftTwoSieveError434
    (h D A B C E : ℕ) (z : ℝ) (P : Finset ℕ) (rough banned : ℕ → Bool) : ℝ :=
  ∑ d ∈ (∏ p ∈ P, p).divisors.filter
    (fun d : ℕ => Squarefree d ∧ (d : ℝ) ≤ z^(4*(h : ℝ)+2)),
    |parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned|

theorem parity_original_shift_two_box_survival434
    (J D A B C E : ℕ) (blocks : Fin J → Finset ℕ) (rough banned : ℕ → Bool) :
    let P := Finset.univ.biUnion blocks
    (∑ xy ∈ parityOriginalShiftTwoBoxObjects434 D A B C E,
      (1 : ℝ) * (if ∀ j, blocks j ∩ parityOriginalShiftTwoBoxBad434 P rough banned xy = ∅
        then 1 else 0)) =
    ((parityOriginalShiftTwoBoxSifted434 D A B C E P rough banned).card : ℝ) := by
  classical
  dsimp only
  let P := Finset.univ.biUnion blocks
  have hi (xy : ℕ × ℕ) :
      (∀ j, blocks j ∩ parityOriginalShiftTwoBoxBad434 P rough banned xy = ∅) ↔
      (∀ p ∈ P, ¬ parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
        ((xy.1 : ZMod p), (xy.2 : ZMod p))) := by
    constructor
    · intro h p hp hb
      obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
      have hm : p ∈ blocks j ∩ parityOriginalShiftTwoBoxBad434 P rough banned xy :=
        Finset.mem_inter.mpr ⟨hpj, Finset.mem_filter.mpr ⟨hp,hb⟩⟩
      rw [h j] at hm
      exact Finset.notMem_empty p hm
    · intro h j
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpj,hpb⟩ := Finset.mem_inter.mp hp
      exact h p (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hpj⟩)
        (Finset.mem_filter.mp hpb).2
  have hind (xy : ℕ × ℕ) :
      (1 : ℝ) * (if ∀ j, blocks j ∩ parityOriginalShiftTwoBoxBad434 P rough banned xy = ∅
        then 1 else 0) =
      if ∀ p ∈ P, ¬ parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
        ((xy.1 : ZMod p), (xy.2 : ZMod p)) then 1 else 0 := by
    rw [one_mul]
    exact if_congr (hi xy) rfl rfl
  calc
    _ = ∑ xy ∈ parityOriginalShiftTwoBoxObjects434 D A B C E,
        if ∀ p ∈ P, ¬ parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
          ((xy.1 : ZMod p), (xy.2 : ZMod p)) then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun xy hxy => hind xy)
    _ = _ := by simp [parityOriginalShiftTwoBoxSifted434, Finset.sum_filter, P]

/-- Actual product-two Brun--Hooley upper bound on unchanged rectangles.
All finite moments are discharged by the preceding CRT identity. No
abstract distribution premise, inverse-two coordinates, or squarefree D. -/
theorem parity_original_shift_two_box_sieve434
    (h J D A B C E : ℕ) (z : ℝ) (hz : 1 < z) (hh : 2 ≤ h) (heven : Even h)
    (hD : 0 < D) (rough banned : ℕ → Bool) :
    let blocks := fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val
    let P := Finset.univ.biUnion blocks
    ((parityOriginalShiftTwoBoxSifted434 D A B C E P rough banned).card : ℝ) ≤
      parityOriginalShiftTwoBoxMass434 D A B C E *
        (∏ p ∈ P, (1-parityOriginalShiftTwoBoxDensity434 rough banned p)) *
        Real.exp (parityOriginalShiftTwoSieveRho434 h) +
      parityOriginalShiftTwoSieveError434 h D A B C E z P rough banned := by
  classical
  dsimp only
  let blocks := fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val
  let P := Finset.univ.biUnion blocks
  let g := parityOriginalShiftTwoBoxDensity434 rough banned
  have hg (j : Fin J) (p : ℕ) (hp : p ∈ blocks j) :
      0 ≤ g p ∧ g p ≤ 1-(2/9 : ℝ) ∧ g p ≤ 3/(p : ℝ) := by
    have hpPrime := (source_natural_block_prime D z j.val p hp).1
    have hodd := source_natural_block_odd D z j.val p hp
    have htwo : p = 2 → banned p = false := by intro he; omega
    have hb := parity_original_shift_two_local_density_bounds434 p hpPrime (rough p) (banned p) htwo
    rw [parity_original_shift_two_local_flag_card434 p hpPrime (rough p) (banned p) htwo] at hb
    refine ⟨by dsimp [g,parityOriginalShiftTwoBoxDensity434]; positivity, ?_, hb.2⟩
    change (localNu p (rough p) (banned p) : ℝ)/(p : ℝ)^2 ≤ _
    linarith [hb.1]
  have hsum (j : Fin J) : (∑ p ∈ blocks j, g p) ≤ 12 := by
    calc
      _ ≤ ∑ p ∈ blocks j, 3/(p : ℝ) := Finset.sum_le_sum (fun p hp => (hg j p hp).2.2)
      _ = 3 * ∑ p ∈ blocks j, (p : ℝ)⁻¹ := by simp only [div_eq_mul_inv, Finset.mul_sum]
      _ ≤ 3 * 4 := mul_le_mul_of_nonneg_left
        (source_dyadic_prime_mass_le_four z j.val (blocks j) hz
          (fun p hp => source_natural_block_prime D z j.val p hp)) (by norm_num)
      _ = 12 := by norm_num
  have hpP (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    exact (source_natural_block_prime D z j.val p hpj).1
  have hmain := SieveContinuation.weighted_block_sieve h J blocks z 12 (2/9)
    (parityOriginalShiftTwoBoxObjects434 D A B C E) (fun _ => 1)
    (parityOriginalShiftTwoBoxBad434 P rough banned) g
    (fun d => parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned)
    (parityOriginalShiftTwoBoxMass434 D A B C E)
    hz hh heven (by norm_num) (by norm_num)
    (by unfold parityOriginalShiftTwoBoxMass434; positivity)
    (by intro xy hxy; norm_num)
    (fun j p hp => source_natural_block_prime D z j.val p hp)
    (fun j p hp => ⟨(hg j p hp).1,(hg j p hp).2.1⟩) hsum
    (fun s hs => parity_original_shift_two_box_moment434 D A B C E hD P s hs
      (fun p hp => hpP p (hs hp)) rough banned)
  dsimp only at hmain
  rw [parity_original_shift_two_box_survival434] at hmain
  exact hmain.2

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoBoxSieveError -/

section

set_option maxHeartbeats 1500000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.SourceCRT
open SourceBlockSieve

/-- Native original6.7 applied to the exact divisor support emitted by the
product-two Brun--Hooley sieve. Repeated primes in assignment D remain. -/
theorem parity_original_shift_two_box_sieve_error_bound434
    (h J D A B C E : ℕ) (z : ℝ) (hz : 1 < z)
    (hD : 0 < D) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hTwo : banned 2 = false)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    let P := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
    let Z := ⌊z^(4*(h : ℝ)+2)⌋₊
    parityOriginalShiftTwoSieveError434 h D A B C E z P rough banned ≤
      (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) +
        4 * (D : ℝ) * (Z : ℝ)^2) * (1+Real.log (Z : ℝ))^3 := by
  classical
  dsimp only
  let P := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
  let Z := ⌊z^(4*(h : ℝ)+2)⌋₊
  let T := (∏ p ∈ P, p).divisors.filter
    (fun d : ℕ => Squarefree d ∧ (d : ℝ) ≤ z^(4*(h : ℝ)+2))
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    exact (source_natural_block_prime D z j.val p hpj).1
  have hcop : D.Coprime (∏ p ∈ P, p) := by
    apply Nat.Coprime.prod_right
    intro p hp
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    exact source_natural_block_coprime D z j.val p hpj
  have hpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hT : T ⊆ Finset.Ioc 0 Z := by
    intro d hd
    obtain ⟨hdv,hds,hlevel⟩ := Finset.mem_filter.mp hd
    have hdvd := (Nat.mem_divisors.mp hdv).1
    have hdpos : 0 < d := by
      apply Nat.pos_of_ne_zero
      intro hd0
      obtain ⟨k,hk⟩ := hdvd
      rw [hd0, zero_mul] at hk
      exact (Nat.ne_of_gt hpos) hk
    exact Finset.mem_Ioc.mpr ⟨hdpos, Nat.le_floor hlevel⟩
  have hsq : ∀ d ∈ T, Squarefree d := fun d hd => (Finset.mem_filter.mp hd).2.1
  have hcp : ∀ d ∈ T, D.Coprime d := by
    intro d hd
    exact Nat.Coprime.of_dvd_right (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hcop
  exact parity_original_shift_two_masked_remainder_sum434 D Z A B C E hD h2D
    rough banned hTwo hAB hCE T hT hsq hcp

/-- Fully estimated box upper bound, with actual product-two density,
literal natural level and a proved explicit error. -/
theorem parity_original_shift_two_box_sieve_explicit434
    (h J D A B C E : ℕ) (z : ℝ) (hz : 1 < z) (hh : 2 ≤ h) (heven : Even h)
    (hD : 0 < D) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hTwo : banned 2 = false)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    let P := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
    let Z := ⌊z^(4*(h : ℝ)+2)⌋₊
    ((parityOriginalShiftTwoBoxSifted434 D A B C E P rough banned).card : ℝ) ≤
      parityOriginalShiftTwoBoxMass434 D A B C E *
        (∏ p ∈ P, (1-parityOriginalShiftTwoBoxDensity434 rough banned p)) *
        Real.exp (parityOriginalShiftTwoSieveRho434 h) +
      (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) +
        4 * (D : ℝ) * (Z : ℝ)^2) * (1+Real.log (Z : ℝ))^3 := by
  dsimp only
  exact (parity_original_shift_two_box_sieve434 h J D A B C E z hz hh heven hD rough banned).trans
    (add_le_add le_rfl (parity_original_shift_two_box_sieve_error_bound434 h J D A B C E z hz
      hD h2D rough banned hTwo hAB hCE))

end Green64Analytic.SourceCRT

end

/-! ## OriginalAssignmentPairsBox -/

section

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem parity_original_D20_no_closed_small_prime434
    (W : ℝ) (n p : ℕ) (hn : sourceD20Rough W n) (hp : p.Prime)
    (hW : (p : ℝ) ≤ W) : ¬ p ∣ n := by
  intro hd
  have hmin := Nat.minFac_le_of_dvd hp.two_le hd
  have hr : (n.minFac : ℝ) ≤ p := by exact_mod_cast hmin
  exact (not_lt_of_ge hW) (hn.2.trans_le hr)

/-- Actual source rough pairs are a subset of the genuine product-two
sifted rectangle. All shifts, closed rough thresholds and original integer
coordinates are checked; removing positivity and source region cuts only enlarges. -/
theorem parity_original_assignment_pairs_subset_box434
    (K N : Finset ℕ) (A B C E D : ℕ) (W : ℝ) (Bans P : Finset ℕ)
    (hK : K ⊆ Finset.Ico A B) (hN : N ⊆ Finset.Ico C E)
    (hP : ∀ p ∈ P, p.Prime) :
    parityOriginalAssignmentSiftedPairs434 K N
      (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) D Bans ⊆
    parityOriginalShiftTwoBoxSifted434 D A B C E P
      (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans)) := by
  classical
  intro xy hxy
  simp only [parityOriginalAssignmentSiftedPairs434, Finset.mem_filter] at hxy
  obtain ⟨hKN, hm, hn, htwo, hD, hrough, hbans⟩ := hxy
  have hshift : xy.1*xy.2 = (xy.1*xy.2-2)+2 := (Nat.sub_add_cancel htwo).symm
  have hres : (xy.1 : ZMod D)*(xy.2 : ZMod D) = 2 :=
    (parity_original_shift_two_product_residue_iff_dvd434 D
      (xy.1*xy.2-2) xy.1 xy.2 hshift).mpr hD
  simp only [parityOriginalShiftTwoBoxSifted434, parityOriginalShiftTwoBoxObjects434,
    parityOriginalShiftTwoIntegerBox434, Finset.mem_filter, and_true]
  constructor
  · exact ⟨Finset.mem_product.mpr
      ⟨hK (Finset.mem_product.mp hKN).1, hN (Finset.mem_product.mp hKN).2⟩, hres⟩
  · intro p hp hbad
    rcases hbad with ⟨hflag,hzero⟩ | ⟨hflag,htwores⟩
    · have hpW : (p : ℝ) ≤ W := of_decide_eq_true hflag
      have hd : p ∣ xy.1*xy.2 := (ZMod.natCast_eq_zero_iff (xy.1*xy.2) p).mp
        (by simpa only [Nat.cast_mul] using hzero)
      rcases (hP p hp).dvd_mul.mp hd with hdm | hdn
      · exact parity_original_D20_no_closed_small_prime434 W xy.1 p hrough.1 (hP p hp) hpW hdm
      · exact parity_original_D20_no_closed_small_prime434 W xy.2 p hrough.2 (hP p hp) hpW hdn
    · have hpB : p ∈ Bans := of_decide_eq_true hflag
      exact hbans p hpB ((parity_original_shift_two_product_residue_iff_dvd434 p
        (xy.1*xy.2-2) xy.1 xy.2 hshift).mp htwores)

/-- Genuine source-assignment count with explicit original6.7 error.
This theorem has no assumed source identity or abstract moment hypothesis. -/
theorem parity_original_assignment_pairs_box_sieve434
    (K N : Finset ℕ) (A B C E D J : ℕ) (W z : ℝ) (Bans : Finset ℕ)
    (hK : K ⊆ Finset.Ico A B) (hN : N ⊆ Finset.Ico C E)
    (hz : 1 < z) (hD : 0 < D) (h2D : Nat.Coprime 2 D)
    (hTwo : 2 ∉ Bans) (hAB : A ≤ B) (hCE : C ≤ E) :
    let P := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
    let Z := ⌊z^(10 : ℝ)⌋₊
    ((parityOriginalAssignmentSiftedPairs434 K N
      (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) D Bans).card : ℝ) ≤
      parityOriginalShiftTwoBoxMass434 D A B C E *
        (∏ p ∈ P, (1-parityOriginalShiftTwoBoxDensity434
          (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans)) p)) *
        Real.exp (parityOriginalShiftTwoSieveRho434 2) +
      (2 * (((B-A : ℕ) : ℝ) + ((E-C : ℕ) : ℝ)) * (Z : ℝ) +
        4 * (D : ℝ) * (Z : ℝ)^2) * (1+Real.log (Z : ℝ))^3 := by
  classical
  dsimp only
  let P := Finset.univ.biUnion (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val)
  have hpp (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
    exact (source_natural_block_prime D z j.val p hpj).1
  have hs : ((parityOriginalAssignmentSiftedPairs434 K N
      (fun xy => sourceD20Rough W xy.1 ∧ sourceD20Rough W xy.2) D Bans).card : ℝ) ≤
      (parityOriginalShiftTwoBoxSifted434 D A B C E P
        (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans))).card := by
    exact_mod_cast Finset.card_le_card
      (parity_original_assignment_pairs_subset_box434 K N A B C E D W Bans P hK hN hpp)
  have hb := parity_original_shift_two_box_sieve_explicit434 2 J D A B C E z hz
    (by norm_num) (by norm_num) hD h2D
    (fun p => decide ((p : ℝ) ≤ W)) (fun p => decide (p ∈ Bans))
    (by simp [hTwo]) hAB hCE
  convert hs.trans hb using 1 <;> norm_num

end Green64Analytic.Parity

end

