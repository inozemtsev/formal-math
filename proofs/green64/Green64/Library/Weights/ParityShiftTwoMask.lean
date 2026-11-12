module

public import Mathlib

@[expose] public section

/-!
# Weights / ParityShiftTwoMask

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityShiftTwoMask -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Canonical integer representatives of Parity's literal T_{d,2} for the
specialization h=-2, a=1, b=2, R=2. The quotient is an INTEGER quotient.
Coprimality is taken modulo 2*d, including its full unit condition. -/
def b625ParityShiftTwoResidues434 (d : ℕ) : Finset ℕ :=
  (Finset.range (2*d)).filter fun r =>
    r.Coprime (2*d) ∧ (d : ℤ) ∣ (r : ℤ)-1 ∧
      Odd (((r : ℤ)-1)/(d : ℤ))

/-- Exact enumeration of the actual residue set. Its odd-d case is empty;
the even-d case contains the one unit representative d+1. -/
theorem b625_parity_shift_two_residue_classification434
    (d r : ℕ) (hd : 0 < d) :
    r ∈ b625ParityShiftTwoResidues434 d ↔ Even d ∧ r=d+1 := by
  simp only [b625ParityShiftTwoResidues434, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrange, hcop, hdiv, hodd⟩
    have hrpos : 0 < r := by
      by_contra h
      have hr0 : r=0 := by omega
      subst r
      simp only [Nat.coprime_zero_left] at hcop
      omega
    have hdR : (0 : ℤ) < d := by exact_mod_cast hd
    have hrR : (r : ℤ) < 2*(d : ℤ) := by exact_mod_cast hrange
    have hnum : (0 : ℤ) ≤ (r : ℤ)-1 := by omega
    let t : ℤ := ((r : ℤ)-1)/(d : ℤ)
    have ht0 : 0 ≤ t := Int.ediv_nonneg hnum hdR.le
    have hrel : t*(d : ℤ) = (r : ℤ)-1 := Int.ediv_mul_cancel hdiv
    have ht2 : t < 2 := by nlinarith
    have htOdd : Odd t := hodd
    have ht1 : t=1 := by
      rcases htOdd with ⟨j,hj⟩
      omega
    have hre : r=d+1 := by rw [ht1] at hrel; omega
    have hrTwo : r.Coprime 2 :=
      Nat.Coprime.coprime_dvd_right (show 2 ∣ 2*d from ⟨d,rfl⟩) hcop
    have hrOdd : Odd r := Nat.coprime_two_right.mp hrTwo
    refine ⟨?_,hre⟩
    rcases hrOdd with ⟨j,hj⟩
    exact ⟨j,by omega⟩
  · rintro ⟨he, rfl⟩
    have hd2 : 2 ≤ d := by rcases he with ⟨j,hj⟩; omega
    have hOdd : Odd (d+1) := by
      rcases he with ⟨j,hj⟩
      exact ⟨j,by omega⟩
    have hC2 : (d+1).Coprime 2 := Nat.coprime_two_right.mpr hOdd
    have hCd : (d+1).Coprime d := by
      simpa only [Nat.add_comm] using
        (Nat.coprime_add_self_left (m:=1) (n:=d)).mpr (by simp)
    have hdR : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    refine ⟨by omega, Nat.coprime_mul_iff_right.mpr ⟨hC2,hCd⟩, ?_, ?_⟩
    · norm_num
    · simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        Int.ediv_self hdR] using (show Odd (1 : ℤ) by decide)

/-- The signed original k is converted to d=|k| with parity preserved.
This is an exact mask statement, not a cancellation or RMS estimate. -/
theorem b625_parity_signed_shift_residue_set434
    (k : ℤ) (hk : k ≠ 0) :
    b625ParityShiftTwoResidues434 k.natAbs =
      if Even k then {k.natAbs+1} else ∅ := by
  have hd : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  ext r
  rw [b625_parity_shift_two_residue_classification434 k.natAbs r hd,
    Int.natAbs_even]
  by_cases he : Even k <;> simp [he]

/-- The genuine standard quadratic Dirichlet character of modulus four,
mapped from integer values to complex values. -/
def b625ParityChiFour434 : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

private theorem b625_chi_four_int434 (n : ℤ) :
    b625ParityChiFour434 (n : ZMod 4) =
      if n%2=0 then 0 else if n%4=1 then 1 else -1 := by
  change ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ) = _
  rw [ZMod.χ₄_int_eq_if_mod_four]
  split_ifs <;> norm_num

/-- On the actual unit group modulo four, the k=2 ratio mask is exactly
the two-character projector. The principal term equals one on these units. -/
theorem b625_parity_k_two_ratio_projector434
    (m mp : ZMod 4) (hm : IsUnit m) (hp : IsUnit mp) :
    (if (mp*m⁻¹).val ∈ b625ParityShiftTwoResidues434 2 then (1 : ℂ) else 0) =
      (1-b625ParityChiFour434 mp * star (b625ParityChiFour434 m))/2 := by
  have hMask : b625ParityShiftTwoResidues434 2 = {3} := by
    ext r
    rw [b625_parity_shift_two_residue_classification434 2 r (by norm_num)]
    norm_num
  have hUnits : ∀ z : ZMod 4, IsUnit z → z=1 ∨ z=3 := by decide
  have h33 : (3 : ZMod 4)*3=1 := by decide
  have hInv : (3 : ZMod 4)⁻¹=3 :=
    ZMod.inv_eq_of_mul_eq_one 4 (3 : ZMod 4) 3 h33
  have hVal1 : (1 : ZMod 4).val = 1 := by decide
  have hVal3 : (3 : ZMod 4).val = 3 := by decide
  have hOne : b625ParityChiFour434 (1 : ZMod 4)=1 := map_one _
  have hThree : b625ParityChiFour434 (3 : ZMod 4) = -1 := by
    change ((ZMod.χ₄ (3 : ZMod 4) : ℤ) : ℂ) = -1
    norm_num [ZMod.χ₄]
  rcases hUnits m hm with rfl | rfl <;> rcases hUnits mp hp with rfl | rfl <;>
    norm_num [hMask,hInv,h33,hOne,hThree,hVal1,hVal3]

/-- The same projector is the original signed divisibility/odd-quotient
gate for k=+2 and k=-2, on arbitrary odd integer cofactors. No representative
choice, natural subtraction or unsigned-quotient substitution is used. -/
theorem b625_parity_signed_two_quotient_projector434
    (m mp k : ℤ) (hm : Odd m) (hp : Odd mp)
    (hk : k=2 ∨ k = -2) :
    (if k ∣ mp-m ∧ Odd ((mp-m)/k) then (1 : ℂ) else 0) =
      (1-b625ParityChiFour434 (mp : ZMod 4) *
        star (b625ParityChiFour434 (m : ZMod 4)))/2 := by
  have hm2 : m%2=1 := Int.odd_iff.mp hm
  have hp2 : mp%2=1 := Int.odd_iff.mp hp
  have hcond : (k ∣ mp-m ∧ Odd ((mp-m)/k)) ↔ m%4 ≠ mp%4 := by
    rcases hk with rfl | rfl <;>
      simp only [Int.odd_iff, Int.dvd_iff_emod_eq_zero, Int.emod_neg, Int.ediv_neg] <;> omega
  simp only [hcond, b625_chi_four_int434]
  have hm4 : m%4=1 ∨ m%4=3 := by omega
  have hp4 : mp%4=1 ∨ mp%4=3 := by omega
  rcases hm4 with hm4 | hm4 <;> rcases hp4 with hp4 | hp4 <;>
    norm_num [hm2,hp2,hm4,hp4]

end Green64Analytic.Parity

end

end

