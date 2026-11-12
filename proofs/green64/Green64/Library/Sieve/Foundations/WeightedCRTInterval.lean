module

public import Green64.Library.Sieve.Foundations.Part001
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

/-!
# Sieve / Foundations / WeightedCRTInterval

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## WeightedCRTInterval -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.SourceCRT
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem b637_mod_eq_cast (D n : ℕ) [NeZero D] (v : ZMod D) :
    Nat.ModEq D n v.val ↔ (n : ZMod D) = v := by
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.natCast_eq_natCast_iff n v.val D).symm

/-- A weighted arithmetic progression count on the actual interval [A,B).
No statistical-independence or discrepancy hypothesis is used. -/
theorem b637_weighted_residue_interval434
    (D A B : ℕ) [NeZero D] (hAB : A ≤ B)
    (w : ZMod D → ℝ) (hw : ∀ r, 0 ≤ w r) :
    |(∑ n ∈ Finset.Ico A B, w (n : ZMod D)) -
      ((B-A : ℕ) : ℝ)/(D : ℝ)*(∑ r : ZMod D, w r)| ≤
      2*(∑ r : ZMod D, w r) := by
  have hf : (∑ r : ZMod D, (residueIntervalCount D r.val A B : ℝ)*w r) =
      ∑ n ∈ Finset.Ico A B, w (n : ZMod D) := by
    simp only [residueIntervalCount, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [b637_mod_eq_cast, ite_mul, one_mul, zero_mul]
    simp
  have he (r : ZMod D) := residueIntervalCount_real_error D r.val A B
    (NeZero.pos D) hAB
  calc
    _ = |∑ r : ZMod D,
        ((residueIntervalCount D r.val A B : ℝ)-((B-A:ℕ):ℝ)/(D:ℝ))*w r| := by
      rw [←hf,Finset.mul_sum,←Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r : ZMod D,
        |((residueIntervalCount D r.val A B : ℝ)-((B-A:ℕ):ℝ)/(D:ℝ))*w r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : ZMod D, 2*w r := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul,abs_of_nonneg (hw r)]
      exact mul_le_mul_of_nonneg_right (he r) (hw r)
    _ = _ := by rw [Finset.mul_sum]

/-- True weighted CRT on any pairwise coprime finite family. The error
retains the total residue weight, rather than a full-modulus cap. -/
theorem b637_weighted_crt_interval434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (A B : ℕ) (hAB : A ≤ B)
    (w : (i : ι) → ZMod (q i) → ℝ) (hw : ∀ i r, 0 ≤ w i r) :
    |(∑ n ∈ Finset.Ico A B, ∏ i, w i (n : ZMod (q i))) -
      ((B-A:ℕ):ℝ)/(∏ i, (q i:ℝ))*(∏ i, ∑ r : ZMod (q i), w i r)| ≤
      2*(∏ i, ∑ r : ZMod (q i), w i r) := by
  let D := ∏ i, q i
  let : NeZero D := ⟨Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (q i))⟩
  let e := ZMod.prodEquivPi q hc
  let W : ZMod D → ℝ := fun a => ∏ i, w i (e a i)
  have hW : ∀ a, 0 ≤ W a := fun a => Finset.prod_nonneg (fun i hi => hw i (e a i))
  have hsum : (∑ a : ZMod D, W a) = ∏ i, ∑ r : ZMod (q i), w i r := by
    calc
      _ = ∑ a : (i : ι) → ZMod (q i), ∏ i, w i (a i) :=
        Equiv.sum_comp e.toEquiv (fun a => ∏ i, w i (a i))
      _ = _ := (Fintype.prod_sum w).symm
  have hnat (n : ℕ) : W (n : ZMod D) = ∏ i, w i (n : ZMod (q i)) := by
    dsimp [W,e]
    simp only [map_natCast,Pi.natCast_apply]
  have h := b637_weighted_residue_interval434 D A B hAB W hW
  simpa only [hsum,hnat,D,Nat.cast_prod] using h
end Green64Analytic.SourceBlockSieve

end

end

