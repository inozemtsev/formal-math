module

public import Green64.Library.Correlation.Part035
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

/-!
# Weights / ActiveResidueTransfer

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActiveResidueTransfer -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem b641_weighted_root_error
    (D lo hi : ℕ) [NeZero D] (g : ZMod D → ℝ) (hg : ∀ r,0≤g r)
    (f : ℕ → ℝ) (M eps : ℝ)
    (h : ∀ r : ZMod D,
      |(∑ n ∈ Finset.Ico lo hi, if Nat.ModEq D n r.val then f n else 0)-M| ≤ M*eps) :
    |(∑ n ∈ Finset.Ico lo hi, g (n:ZMod D)*f n)-M*(∑ r : ZMod D,g r)| ≤
      (M*(∑ r : ZMod D,g r))*eps := by
  have he (n : ℕ) (r : ZMod D) : Nat.ModEq D n r.val ↔ (n:ZMod D)=r := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff n r.val D).symm
  have hs : (∑ r : ZMod D, g r*(∑ n ∈ Finset.Ico lo hi,
        if Nat.ModEq D n r.val then f n else 0)) =
      ∑ n ∈ Finset.Ico lo hi, g (n:ZMod D)*f n := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [he,mul_ite,mul_zero]
    simp
  calc
    _ = |∑ r : ZMod D,g r*((∑ n ∈ Finset.Ico lo hi,
        if Nat.ModEq D n r.val then f n else 0)-M)| := by
      simp only [mul_sub,Finset.sum_sub_distrib]
      rw [←Finset.sum_mul,hs]
      congr 1
      ring
    _ ≤ ∑ r : ZMod D,|g r*((∑ n ∈ Finset.Ico lo hi,
        if Nat.ModEq D n r.val then f n else 0)-M)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : ZMod D,g r*(M*eps) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul,abs_of_nonneg (hg r)]
      exact mul_le_mul_of_nonneg_left (h r) (hg r)
    _ = _ := by rw [←Finset.sum_mul]; ring

private theorem b641_sum_residue_val (p : ℕ) [NeZero p] (f : ℕ → ℝ) :
    (∑ r : ZMod p, f r.val) = ∑ r ∈ Finset.range p,f r := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => exact Fin.sum_univ_eq_sum_range f (p+1)

/-- Quantitative relative physical-to-independent-residue transfer with
ALL active local weights included. Active weights may contain the actual
forced divisibility indicators and endpoint/internal damping. They need
only be nonnegative; zero-density and incompatible active paths remain
included. No active root congruence, CRT independence or relative-error
hypothesis is supplied by the caller. -/
theorem b641_eventually_actual_parity_active_weight_CRT434
    (E gamma : ℝ) (hE : 0≤E) (hgamma : 0<gamma) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    ∀ active : Finset ℕ,
      active ⊆ sourceNativeOriginalG434 20 L →
      active.card ≤ J*(N+1)*(sourceOriginalPAllGroupIndices 20 L).card →
    ∀ w : ℕ → ℕ → ℝ, (∀ p ∈ active, ∀ r,0≤w p r) →
    ∀ lo hi : ℕ, Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
    ∀ eta : ℕ → ℝ, ∀ offset : ℕ → ℤ,
      (∀ i ∈ Finset.range (N+1), 0≤eta i ∧ eta i≤1) →
    let P := sourceNativeOriginalG434 20 L \ active
    let f := b637PathResidueLoss434 (Finset.range (N+1)) eta offset
    let V := ∏ p ∈ P, (1-b637ResidueMean434 f p)
    let W := ∏ p ∈ active, (∑ r ∈ Finset.range p,w p r)/(p:ℝ)
    |(∑ n ∈ Finset.Ico lo hi,
        (∏ p ∈ active,w p (n%p)) *
        (∏ p ∈ P, ∏ i ∈ Finset.range (N+1),
          (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1))) -
      ((hi-lo:ℕ):ℝ)*W*V| ≤
        (((hi-lo:ℕ):ℝ)*W*V)*L^(-E*(N:ℝ)) := by
  filter_upwards [b638_eventually_actual_parity_relative_CRT434 E gamma hE hgamma J,
    eventually_ge_atTop (1:ℝ)] with L h hL
  dsimp only at h ⊢
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  intro active hactive hcard w hw lo hi hH eta offset heta
  let P := sourceNativeOriginalG434 20 L \ active
  let loss := b637PathResidueLoss434 (Finset.range (N+1)) eta offset
  let V := ∏ p ∈ P,(1-b637ResidueMean434 loss p)
  let D : ℕ := ∏ p : active,p.val
  let (p : active) : NeZero p.val :=
    ⟨(b638_actual_full_P_range434 L hL p.val (hactive p.property)).1.ne_zero⟩
  let : NeZero D := ⟨Finset.prod_ne_zero_iff.mpr (fun p hp => NeZero.ne p.val)⟩
  have hD : D = ∏ p ∈ active,p := Finset.prod_coe_sort active (fun p : ℕ => p)
  have hc : Pairwise (fun p q : active => p.val.Coprime q.val) := by
    intro p q hpq
    apply (Nat.coprime_primes
      (b638_actual_full_P_range434 L hL p.val (hactive p.property)).1
      (b638_actual_full_P_range434 L hL q.val (hactive q.property)).1).mpr
    intro he
    exact hpq (Subtype.ext he)
  let e := ZMod.prodEquivPi (fun p : active => p.val) hc
  let g : ZMod D → ℝ := fun r => ∏ p : active,w p.val (e r p).val
  have hg : ∀ r,0≤g r := fun r =>
    Finset.prod_nonneg (fun p hp => hw p.val p.property _)
  have hnat (n : ℕ) : g (n:ZMod D)=∏ p ∈ active,w p (n%p) := by
    change (∏ p : active,w p.val (e (n:ZMod D) p).val) = _
    simp only [map_natCast,Pi.natCast_apply,ZMod.val_natCast]
    exact Finset.prod_coe_sort active (fun p : ℕ => w p (n%p))
  have hsum : (∑ r : ZMod D,g r) = ∏ p ∈ active,∑ r ∈ Finset.range p,w p r := by
    calc
      _ = ∑ r : (p : active) → ZMod p.val, ∏ p : active,w p.val (r p).val :=
        Equiv.sum_comp e.toEquiv (fun r => ∏ p : active,w p.val (r p).val)
      _ = ∏ p : active, ∑ r : ZMod p.val,w p.val r.val := (Fintype.prod_sum (fun (p : active) (r : ZMod p.val) => w p.val r.val)).symm
      _ = _ := by
        simp_rw [b641_sum_residue_val]
        exact Finset.prod_coe_sort active (fun p : ℕ => ∑ r ∈ Finset.range p,w p r)
  let f : ℕ → ℝ := fun n => ∏ p ∈ P,∏ i ∈ Finset.range (N+1),
    if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1
  let M : ℝ := ((hi-lo:ℕ):ℝ)/(D:ℝ)*V
  have hRoot (r : ZMod D) :
      |(∑ n ∈ Finset.Ico lo hi, if Nat.ModEq D n r.val then f n else 0)-M| ≤
        M*L^(-E*(N:ℝ)) := by
    have hr := h active hactive hcard r.val lo hi hH eta offset heta
    change |(∑ n ∈ Finset.Ico lo hi,
      if Nat.ModEq D n r.val then f n else 0)-((hi-lo:ℕ):ℝ)/(D:ℝ)*V| ≤
        (((hi-lo:ℕ):ℝ)/(D:ℝ)*V)*L^(-E*(N:ℝ))
    simpa only [hD] using hr.2
  have hmain := b641_weighted_root_error D lo hi g hg f M (L^(-E*(N:ℝ))) hRoot
  have hDCast : (D:ℝ)=∏ p ∈ active,(p:ℝ) := by rw [hD,Nat.cast_prod]
  have hMean : M*(∑ r : ZMod D,g r) = ((hi-lo:ℕ):ℝ)*
      (∏ p ∈ active,(∑ r ∈ Finset.range p,w p r)/(p:ℝ))*V := by
    dsimp [M]
    rw [hsum,hDCast,Finset.prod_div_distrib]
    simp only [div_eq_mul_inv]
    ring
  rw [hMean] at hmain
  simpa only [hnat] using hmain
end Green64Analytic.SourceBlockSieve

end

end

