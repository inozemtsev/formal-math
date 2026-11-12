module

public import Mathlib

@[expose] public section

/-!
# Sieve / Foundations / StrippedCRTCount

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualStrippedCRTCount -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

private theorem b587_coprime_joint_difference
    (a b x y : ℕ) (s : ℤ) (hab : a.Coprime b) (hxy : x ≤ y)
    (hbx : b ∣ x) (hby : b ∣ y)
    (hax : (a:ℤ) ∣ (x:ℤ)+s) (hay : (a:ℤ) ∣ (y:ℤ)+s) :
    a*b ∣ y-x := by
  have hi : (a:ℤ) ∣ ((y-x:ℕ):ℤ) := by
    rw [Int.natCast_sub hxy]
    convert dvd_sub hay hax using 1; ring
  exact hab.mul_dvd_of_dvd_of_dvd
    (Int.natCast_dvd_natCast.mp hi) (Nat.dvd_sub hby hbx)

/-- Both ORIGINAL selected divisibilities on the signed stripped graph
force a SINGLE residue modulo X_A X_B. No character average is used. -/
theorem b587_actual_stripped_joint_residue434
    (XA XB D w v : ℕ) (k : ℤ) (hcop : XA.Coprime XB)
    (hBw : XB ∣ w) (hBv : XB ∣ v)
    (hAw : (XA:ℤ) ∣ (w:ℤ)+2*k*(D:ℤ))
    (hAv : (XA:ℤ) ∣ (v:ℤ)+2*k*(D:ℤ)) :
    Nat.ModEq (XA*XB) w v := by
  apply Nat.modEq_iff_dvd.mpr
  by_cases hle : w ≤ v
  · have hd := b587_coprime_joint_difference XA XB w v (2*k*(D:ℤ)) hcop hle hBw hBv hAw hAv
    have hi := Int.natCast_dvd_natCast.mpr hd
    simpa only [Int.natCast_mul,Int.natCast_sub hle] using hi
  · have hle' : v ≤ w := by omega
    have hd := b587_coprime_joint_difference XA XB v w (2*k*(D:ℤ)) hcop hle' hBv hBw hAv hAw
    have hi : ((XA*XB:ℕ):ℤ) ∣ (w:ℤ)-(v:ℤ) := by
      simpa only [Int.natCast_mul,Int.natCast_sub hle'] using Int.natCast_dvd_natCast.mpr hd
    simpa only [neg_sub] using (dvd_neg.mpr hi)

def b587ActualStrippedCRTPositions (Y XA XB D : ℕ) (k : ℤ) : Finset ℕ :=
  (Finset.range (Y+1)).filter (fun w =>
    0 < w ∧ 0 < (w:ℤ)+2*k*(D:ℤ) ∧
    XB ∣ w ∧ (XA:ℤ) ∣ (w:ℤ)+2*k*(D:ℤ))

/-- Quantitative density of the actual positive signed physical graph:
both selected-product restrictions are retained BEFORE Cauchy. -/
theorem b587_actual_stripped_CRT_count434
    (Y XA XB D : ℕ) (k : ℤ) (hcop : XA.Coprime XB) :
    (b587ActualStrippedCRTPositions Y XA XB D k).card ≤ Y/(XA*XB)+1 := by
  let S := b587ActualStrippedCRTPositions Y XA XB D k
  have hm : Set.MapsTo (fun w : ℕ => w/(XA*XB)) (↑S)
      (↑(Finset.range (Y/(XA*XB)+1))) := by
    intro w hw
    have hwY : w ≤ Y := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      omega
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hwY))
  have hinj : Set.InjOn (fun w : ℕ => w/(XA*XB)) (↑S) := by
    intro w hw v hv heq
    change w/(XA*XB)=v/(XA*XB) at heq
    have hgw := (Finset.mem_filter.mp hw).2
    have hgv := (Finset.mem_filter.mp hv).2
    have hmod := b587_actual_stripped_joint_residue434 XA XB D w v k hcop
      hgw.2.2.1 hgv.2.2.1 hgw.2.2.2 hgv.2.2.2
    change w % (XA*XB)=v % (XA*XB) at hmod
    calc
      w = w%(XA*XB)+(XA*XB)*(w/(XA*XB)) := (Nat.mod_add_div _ _).symm
      _ = v%(XA*XB)+(XA*XB)*(v/(XA*XB)) := by rw [hmod,heq]
      _ = v := Nat.mod_add_div _ _
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn
    (fun w : ℕ => w/(XA*XB)) hm hinj

private theorem b587_quotient_unit
    (a b w : ℕ) (s : ℤ) (hbw : b ∣ w)
    (has : a.Coprime s.natAbs) (haw : (a:ℤ) ∣ (w:ℤ)+s) :
    a.Coprime (w/b) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpu
  have hpw : p ∣ w := by
    obtain ⟨r,hr⟩ := hpu
    refine ⟨r*b,?_⟩
    rw [←Nat.div_mul_cancel hbw,hr]
    ring
  have hpi : (p:ℤ) ∣ (w:ℤ)+s :=
    (Int.natCast_dvd_natCast.mpr hpa).trans haw
  have hps : (p:ℤ) ∣ s := by
    convert dvd_sub hpi (Int.natCast_dvd_natCast.mpr hpw) using 1; ring
  have hd := Nat.dvd_gcd hpa (Int.natCast_dvd.mp hps)
  change Nat.gcd a s.natAbs=1 at has
  simpa only [has] using hd

/-- On the genuine free/auxiliary-coprime sector the ordinary quotient
variable lies in a UNIT progression, as required by the AP moment bound. -/
theorem b587_actual_stripped_quotient_unit434
    (XA XB D w : ℕ) (k : ℤ) (hBw : XB ∣ w)
    (hShift : XA.Coprime (2*k*(D:ℤ)).natAbs)
    (hAw : (XA:ℤ) ∣ (w:ℤ)+2*k*(D:ℤ)) :
    XA.Coprime (w/XB) :=
  b587_quotient_unit XA XB w (2*k*(D:ℤ)) hBw hShift hAw

/-- BOTH quotient variables are units in their opposite selected modulus.
The actual integer shift is retained, including negative k. -/
theorem b587_actual_stripped_both_quotients_unit434
    (XA XB D w wp : ℕ) (k : ℤ)
    (hBw : XB ∣ w) (hAwp : XA ∣ wp)
    (hShiftA : XA.Coprime (2*k*(D:ℤ)).natAbs)
    (hShiftB : XB.Coprime (2*k*(D:ℤ)).natAbs)
    (hGraph : (wp:ℤ)=(w:ℤ)+2*k*(D:ℤ)) :
    XA.Coprime (w/XB) ∧ XB.Coprime (wp/XA) := by
  constructor
  · apply b587_quotient_unit XA XB w (2*k*(D:ℤ)) hBw hShiftA
    rw [←hGraph]
    exact Int.natCast_dvd_natCast.mpr hAwp
  · apply b587_quotient_unit XB XA wp (-(2*k*(D:ℤ))) hAwp
    · simpa only [Int.natAbs_neg] using hShiftB
    · have heq : (wp:ℤ)+(-(2*k*(D:ℤ)))=(w:ℤ) := by rw [hGraph]; ring
      rw [heq]
      exact Int.natCast_dvd_natCast.mpr hBw
end Green64Analytic.ShiftTwoTerminal

end

end

