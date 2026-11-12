module

public import Green64.Library.Sieve.Foundations.StrippedCRTCount

@[expose] public section

/-!
# Correlation / SelectedPhysicalRows

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SelectedPhysicalRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The full positive physical graph with both original selected-product
divisibilities retained together. Negative physical shifts are allowed. -/
def b595SelectedPhysicalPairs (Y XA XB D : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc 0 Y) ×ˢ (Finset.Ioc 0 Y)).filter
    (fun p => XB ∣ p.1 ∧ XA ∣ p.2 ∧
      (p.2 : ℤ) = (p.1 : ℤ) + 2*k*(D:ℤ))

@[simp] theorem b595_mem_physical_pairs434
    {Y XA XB D : ℕ} {k : ℤ} {p : ℕ × ℕ} :
    p ∈ b595SelectedPhysicalPairs Y XA XB D k ↔
      (0 < p.1 ∧ p.1 ≤ Y) ∧ (0 < p.2 ∧ p.2 ≤ Y) ∧
      XB ∣ p.1 ∧ XA ∣ p.2 ∧
      (p.2 : ℤ) = (p.1 : ℤ) + 2*k*(D:ℤ) := by
  simp [b595SelectedPhysicalPairs, and_assoc]

/-- Removing the actual source selected product does not identify
different physical rows: the target is fixed by the same signed graph. -/
theorem b595_source_quotient_injective434
    (Y XA XB D : ℕ) (k : ℤ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1/XB)
      (↑(b595SelectedPhysicalPairs Y XA XB D k)) := by
  intro x hx y hy heq
  change x.1/XB = y.1/XB at heq
  rcases b595_mem_physical_pairs434.mp hx with ⟨hx,hxp,hxB,hxA,hxg⟩
  rcases b595_mem_physical_pairs434.mp hy with ⟨hy,hyp,hyB,hyA,hyg⟩
  have hfirst : x.1 = y.1 := by
    rw [← Nat.div_mul_cancel hxB, ← Nat.div_mul_cancel hyB, heq]
  have hsecond : x.2 = y.2 := by
    apply Int.natCast_inj.mp
    rw [hxg,hyg,hfirst]
  exact Prod.ext hfirst hsecond

/-- Every source quotient on the genuine coupled graph lies in the SAME
residue modulo the opposite selected product. No averaging is used. -/
theorem b595_source_quotients_same_residue434
    (Y XA XB D : ℕ) (k : ℤ) (hcop : XA.Coprime XB)
    {x y : ℕ × ℕ}
    (hx : x ∈ b595SelectedPhysicalPairs Y XA XB D k)
    (hy : y ∈ b595SelectedPhysicalPairs Y XA XB D k) :
    Nat.ModEq XA (x.1/XB) (y.1/XB) := by
  rcases b595_mem_physical_pairs434.mp hx with ⟨hx,hxp,hxB,hxA,hxg⟩
  rcases b595_mem_physical_pairs434.mp hy with ⟨hy,hyp,hyB,hyA,hyg⟩
  have hxAi : (XA:ℤ) ∣ (x.1:ℤ)+2*k*(D:ℤ) := by
    rw [←hxg]
    exact Int.natCast_dvd_natCast.mpr hxA
  have hyAi : (XA:ℤ) ∣ (y.1:ℤ)+2*k*(D:ℤ) := by
    rw [←hyg]
    exact Int.natCast_dvd_natCast.mpr hyA
  have hjoint := b587_actual_stripped_joint_residue434
    XA XB D x.1 y.1 k hcop hxB hyB hxAi hyAi
  have hmod : Nat.ModEq XA x.1 y.1 :=
    Nat.ModEq.of_dvd (dvd_mul_right XA XB) hjoint
  rw [←Nat.div_mul_cancel hxB, ←Nat.div_mul_cancel hyB] at hmod
  exact Nat.ModEq.cancel_right_of_coprime hcop hmod

/-- The unit condition is derived from the real signed physical shift. -/
theorem b595_source_quotient_unit434
    (Y XA XB D : ℕ) (k : ℤ)
    (hShift : XA.Coprime (2*k*(D:ℤ)).natAbs)
    {x : ℕ × ℕ} (hx : x ∈ b595SelectedPhysicalPairs Y XA XB D k) :
    XA.Coprime (x.1/XB) := by
  rcases b595_mem_physical_pairs434.mp hx with ⟨hx,hxp,hxB,hxA,hxg⟩
  apply b587_actual_stripped_quotient_unit434 XA XB D x.1 k hxB hShift
  rw [←hxg]
  exact Int.natCast_dvd_natCast.mpr hxA

/-- Reversing a physical row swaps the actual selected products and
negates k, while preserving the full positive cutoff. -/
theorem b595_swap_physical_pair434
    (Y XA XB D : ℕ) (k : ℤ) {x : ℕ × ℕ}
    (hx : x ∈ b595SelectedPhysicalPairs Y XA XB D k) :
    x.swap ∈ b595SelectedPhysicalPairs Y XB XA D (-k) := by
  rcases b595_mem_physical_pairs434.mp hx with ⟨hx,hxp,hxB,hxA,hxg⟩
  apply b595_mem_physical_pairs434.mpr
  refine ⟨hxp,hx,hxA,hxB,?_⟩
  change (x.1:ℤ) = (x.2:ℤ)+2*(-k)*(D:ℤ)
  rw [hxg]
  ring

end Green64Analytic.ShiftTwoTerminal

end

end

