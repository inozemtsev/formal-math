module

public import Green64.Library.Correlation.Part020

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeStepCap

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeStepCap -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

private theorem b651_prod_exp_slots {α : Type*} (s : Finset α) (f : α → ℕ)
    (M : ℕ) (U : ℝ) (hU : 0 ≤ U) (hc : s.card ≤ M)
    (hf : ∀ a ∈ s, (f a : ℝ) ≤ Real.exp U) :
    (∏ a ∈ s, (f a : ℝ)) ≤ Real.exp ((M : ℝ)*U) := by
  calc
    _ ≤ ∏ _a ∈ s, Real.exp U :=
      Finset.prod_le_prod₀ (fun a ha => Nat.cast_nonneg _) hf
    _ = Real.exp ((s.card : ℝ)*U) := by
      rw [Finset.prod_const,←Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hU)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- A maximum of the literal full source step divisor. Every repeated
auxiliary draw is still a separate product factor. This bounds one D;
it is not an estimate for a sum of coefficient masses. -/
theorem b651_all_prime_D_cap434 (U : ℝ) (hU : 0 ≤ U)
    (hsmall : ∀ g p, (smallMod g p : ℝ) ≤ Real.exp U)
    (hbig : ∀ g p, (bigMod g p : ℝ) ≤ Real.exp U)
    {N : ℕ} (ω : B643AllPrimePath434 SP BP J ell m patterns N) (i : Fin N) :
    (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℝ) ≤
      Real.exp (2*((J+ell : ℕ):ℝ)*
        ((Fintype.card SG : ℝ)+(Fintype.card BG : ℝ))*U) := by
  let f := ω.2.2 i
  have hs (g : SG) :
      (∏ j ∈ sourceSmallShared J ell g,
        (smallMod g ((ω.1 i.castSucc g).val (f.2.2.2.1 g j)) : ℝ)) ≤
      Real.exp (2*((J+ell : ℕ):ℝ)*U) := by
    have hc : (sourceSmallShared (SG := SG) J ell g).card ≤ J+ell := by
      simpa only [Fintype.card_fin] using
        (Finset.card_le_univ (sourceSmallShared J ell g))
    apply (b651_prod_exp_slots _ _ (J+ell) U hU hc
      (fun j hj => hsmall g _)).trans
    apply Real.exp_le_exp.mpr
    have h : 0 ≤ ((J+ell : ℕ):ℝ)*U := mul_nonneg (Nat.cast_nonneg _) hU
    nlinarith
  have hb (g : BG) :
      (∏ j ∈ sourceBigShared J ell m (patterns f.1.1) g,
        (bigMod g ((ω.2.1 i.castSucc g).val (f.2.1 g j)) : ℝ)) *
      (∏ j : ↥((patterns f.1.1).free g), (bigMod g (f.1.2 g j) : ℝ)) ≤
      Real.exp (2*((J+ell : ℕ):ℝ)*U) := by
    have hc : (sourceBigShared J ell m (patterns f.1.1) g).card ≤ J+ell := by
      simpa only [Fintype.card_fin] using
        (Finset.card_le_univ (sourceBigShared J ell m (patterns f.1.1) g))
    have ha : (Finset.univ : Finset ↥((patterns f.1.1).free g)).card ≤ J+ell := by
      rw [Finset.card_univ,Fintype.card_coe]
      have hh : ((patterns f.1.1).free g).card ≤ J := by
        simpa only [Fintype.card_fin] using
          (Finset.card_le_univ ((patterns f.1.1).free g))
      omega
    have h1 := b651_prod_exp_slots _ _ (J+ell) U hU hc
      (fun j hj => hbig g ((ω.2.1 i.castSucc g).val (f.2.1 g j)))
    have h2 := b651_prod_exp_slots Finset.univ _ (J+ell) U hU ha
      (fun j hj => hbig g (f.1.2 g j))
    calc
      _ ≤ Real.exp (((J+ell : ℕ):ℝ)*U)*Real.exp (((J+ell : ℕ):ℝ)*U) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  dsimp only [b643AllPrimeD434]
  push_cast
  calc
    _ ≤ (∏ _g : SG, Real.exp (2*((J+ell : ℕ):ℝ)*U)) *
      (∏ _g : BG, Real.exp (2*((J+ell : ℕ):ℝ)*U)) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact Finset.prod_le_prod₀ (fun g hg => by positivity) (fun g hg => hs g)
      · exact Finset.prod_le_prod₀ (fun g hg => by positivity) (fun g hg => hb g)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ]
      rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      push_cast
      ring

/-- Every prefix of the literal signed path stays within N times the
maximum single displacement. No cancellation or merging of equal D is used. -/
theorem b651_all_prime_offset_cap434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N)
    (shift : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ i : Fin N,
      (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℝ) ≤ C)
    (t : ℕ) :
    |(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω shift t : ℝ)| ≤
      (N:ℝ)*|(shift:ℝ)| *C := by
  have hterm (i : Fin N) :
      |((if i.val < t then physicalAlternatingSign i.val*shift*
        (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ)
        else 0 : ℤ) : ℝ)| ≤ |(shift:ℝ)| *C := by
    split_ifs with hi
    · have hd0 : 0 ≤
          (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℝ) :=
        Nat.cast_nonneg _
      have ho : |(physicalAlternatingSign i.val : ℝ)| = 1 := by
        unfold physicalAlternatingSign
        split_ifs <;> norm_num
      calc
        _ = |(shift:ℝ)| *
            (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℝ) := by
          rw [Int.cast_mul,Int.cast_mul,Int.cast_natCast,abs_mul,abs_mul,ho,one_mul,
            abs_of_nonneg hd0]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hD i) (abs_nonneg _)
    · simp only [Int.cast_zero,abs_zero]
      exact mul_nonneg (abs_nonneg _) hC
  unfold b643AllPrimeOffset434
  rw [Int.cast_sum]
  calc
    _ ≤ ∑ i : Fin N, |((if i.val < t then physicalAlternatingSign i.val*shift*
        (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ)
        else 0 : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, |(shift:ℝ)| *C := Finset.sum_le_sum (fun i hi => hterm i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
end Green64FullPhysicalE

end

end

