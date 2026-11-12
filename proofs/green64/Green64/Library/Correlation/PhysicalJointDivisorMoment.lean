module

public import Green64.Library.Correlation.SelectedPhysicalRows
public import Green64.Library.Weights.Part034

@[expose] public section

/-!
# Correlation / PhysicalJointDivisorMoment

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalJointDivisorMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual joint selected-product density, before harmonic
selected-mark normalization restores X_A X_B. -/
def b595JointDivisorBudget (Y XA XB : ℕ) : ℝ :=
  32*((Y:ℝ)/((XA:ℝ)*(XB:ℝ)))*(1+Real.log (Y:ℝ))^15

private theorem b595_quotient_budget_le
    (Y XA XB : ℕ) (hXA : 0<XA) (hXB : 0<XB) (hN : 0<Y/XB) :
    32*(((Y/XB:ℕ):ℝ)/(XA:ℝ))*(1+Real.log ((Y/XB:ℕ):ℝ))^15 ≤
      b595JointDivisorBudget Y XA XB := by
  have hXAr : 0<(XA:ℝ) := by exact_mod_cast hXA
  have hXBr : 0<(XB:ℝ) := by exact_mod_cast hXB
  have hNr : 0<((Y/XB:ℕ):ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤((Y/XB:ℕ):ℝ) := by exact_mod_cast hN
  have hNY : ((Y/XB:ℕ):ℝ)≤(Y:ℝ) := by exact_mod_cast Nat.div_le_self Y XB
  have hdiv : ((Y/XB:ℕ):ℝ)≤(Y:ℝ)/(XB:ℝ) := by
    apply (le_div_iff₀ hXBr).mpr
    exact_mod_cast Nat.div_mul_le_self Y XB
  have hlog : 1+Real.log ((Y/XB:ℕ):ℝ)≤1+Real.log (Y:ℝ) :=
    by linarith [Real.log_le_log hNr hNY]
  have hnlog : 0≤1+Real.log ((Y/XB:ℕ):ℝ) :=
    by linarith [Real.log_nonneg hN1]
  calc
    _ ≤ 32*(((Y:ℝ)/(XB:ℝ))/(XA:ℝ))*(1+Real.log (Y:ℝ))^15 := by
      gcongr
    _ = b595JointDivisorBudget Y XA XB := by
      unfold b595JointDivisorBudget
      congr 2
      field_simp

/-- A genuine AP moment for the complete physical source quotient.
Both selected divisibilities are present before any estimate. The unit
residue, its uniqueness and the injection are derived from the actual
signed graph. No divisor-moment premise is assumed. -/
theorem b595_physical_source_fourth_moment434
    (Y XA XB D : ℕ) (k : ℤ) (S : Finset (ℕ×ℕ))
    (hS : S ⊆ b595SelectedPhysicalPairs Y XA XB D k)
    (hXA : 0<XA) (hXB : 0<XB) (hcop : XA.Coprime XB)
    (hShift : XA.Coprime (2*k*(D:ℤ)).natAbs)
    (hsize : XA^16≤Y/XB) :
    (∑ p ∈ S, ((p.1/XB).divisors.card:ℝ)^4) ≤
      b595JointDivisorBudget Y XA XB := by
  have hN : 0<Y/XB := lt_of_lt_of_le (pow_pos hXA 16) hsize
  have hY : 0<Y := lt_of_lt_of_le hN (Nat.div_le_self Y XB)
  have hY1 : (1:ℝ)≤(Y:ℝ) := by exact_mod_cast hY
  have hlogY : 0≤1+Real.log (Y:ℝ) :=
    by linarith [Real.log_nonneg hY1]
  by_cases hne : S.Nonempty
  · obtain ⟨p0,hp0⟩ := hne
    have hunit : XA.Coprime (p0.1/XB) :=
      b595_source_quotient_unit434 Y XA XB D k hShift (hS hp0)
    let T := (Finset.Ioc 0 (Y/XB)).filter
      (fun u => Nat.ModEq XA u (p0.1/XB))
    have hinj : Set.InjOn (fun p : ℕ×ℕ => p.1/XB) (↑S) := by
      intro p hp q hq heq
      exact b595_source_quotient_injective434 Y XA XB D k (hS hp) (hS hq) heq
    have hmap : S.image (fun p => p.1/XB) ⊆ T := by
      intro u hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      have hrow := b595_mem_physical_pairs434.mp (hS hp)
      have hupos : 0<p.1/XB :=
        Nat.div_pos (Nat.le_of_dvd hrow.1.1 hrow.2.2.1) hXB
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨hupos,Nat.div_le_div_right hrow.1.2⟩,?_⟩
      exact b595_source_quotients_same_residue434
        Y XA XB D k hcop (hS hp) (hS hp0)
    have hsum :
        (∑ p ∈ S, ((p.1/XB).divisors.card:ℝ)^4) ≤
          ∑ u ∈ T, (u.divisors.card:ℝ)^4 :=
      Finset.sum_le_sum_of_injOn (fun p => p.1/XB) hinj hmap
        (fun _ _ => le_rfl) (fun _ _ _ => by positivity)
    exact hsum.trans
      ((b593_unit_progression_tau_four434 (Y/XB) XA (p0.1/XB)
        hXA hunit hsize).trans (b595_quotient_budget_le Y XA XB hXA hXB hN))
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.sum_empty]
    unfold b595JointDivisorBudget
    positivity

/-- The target moment is the SAME physical estimate with signed k
reversed and selected products swapped; no target progression is dropped. -/
theorem b595_physical_target_fourth_moment434
    (Y XA XB D : ℕ) (k : ℤ) (S : Finset (ℕ×ℕ))
    (hS : S ⊆ b595SelectedPhysicalPairs Y XA XB D k)
    (hXA : 0<XA) (hXB : 0<XB) (hcop : XA.Coprime XB)
    (hShift : XB.Coprime (2*k*(D:ℤ)).natAbs)
    (hsize : XB^16≤Y/XA) :
    (∑ p ∈ S, ((p.2/XA).divisors.card:ℝ)^4) ≤
      b595JointDivisorBudget Y XA XB := by
  let T := S.image Prod.swap
  have hT : T ⊆ b595SelectedPhysicalPairs Y XB XA D (-k) := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact b595_swap_physical_pair434 Y XA XB D k (hS hx)
  have hShift' : XB.Coprime (2*(-k)*(D:ℤ)).natAbs := by
    have he : 2*(-k)*(D:ℤ)=-(2*k*(D:ℤ)) := by ring
    simpa only [he,Int.natAbs_neg] using hShift
  have hh := b595_physical_source_fourth_moment434
    Y XB XA D (-k) T hT hXB hXA hcop.symm hShift' hsize
  have hsum :
      (∑ p ∈ T, ((p.1/XA).divisors.card:ℝ)^4) =
        ∑ p ∈ S, ((p.2/XA).divisors.card:ℝ)^4 := by
    dsimp only [T]
    rw [Finset.sum_image]
    · rfl
    · exact Prod.swap_injective.injOn
  rw [hsum] at hh
  simpa only [b595JointDivisorBudget,mul_comm (XB:ℝ) (XA:ℝ)] using hh

/-- The two stripped divisor squares have the full joint CRT density.
The elementary 2ab≤a²+b² is applied only AFTER both fourth moments
have retained their opposite selected modulus. Thus no sqrt(D) or
selected-prime divisor factor is introduced. -/
theorem b595_physical_joint_two_core_majorant434
    (Y XA XB D : ℕ) (k : ℤ) (S : Finset (ℕ×ℕ))
    (hS : S ⊆ b595SelectedPhysicalPairs Y XA XB D k)
    (hXA : 0<XA) (hXB : 0<XB) (hcop : XA.Coprime XB)
    (hShiftA : XA.Coprime (2*k*(D:ℤ)).natAbs)
    (hShiftB : XB.Coprime (2*k*(D:ℤ)).natAbs)
    (hsizeA : XA^16≤Y/XB) (hsizeB : XB^16≤Y/XA) :
    (∑ p ∈ S,
      ((p.1/XB).divisors.card:ℝ)^2 * ((p.2/XA).divisors.card:ℝ)^2) ≤
      b595JointDivisorBudget Y XA XB := by
  have hs := b595_physical_source_fourth_moment434
    Y XA XB D k S hS hXA hXB hcop hShiftA hsizeA
  have ht := b595_physical_target_fourth_moment434
    Y XA XB D k S hS hXA hXB hcop hShiftB hsizeB
  have hterm :
      2*(∑ p ∈ S,
        ((p.1/XB).divisors.card:ℝ)^2*((p.2/XA).divisors.card:ℝ)^2) ≤
      (∑ p ∈ S,((p.1/XB).divisors.card:ℝ)^4) +
      (∑ p ∈ S,((p.2/XA).divisors.card:ℝ)^4) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    nlinarith [sq_nonneg
      (((p.1/XB).divisors.card:ℝ)^2-((p.2/XA).divisors.card:ℝ)^2)]
  linarith

end Green64Analytic.ShiftTwoTerminal

end

end

