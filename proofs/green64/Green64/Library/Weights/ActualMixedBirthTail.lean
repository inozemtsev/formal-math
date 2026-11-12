module

public import Green64.Library.Correlation.Part050
public import Green64.Library.Correlation.MemoryOldTerminalBirthCut

@[expose] public section

/-!
# Weights / ActualMixedBirthTail

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualMixedBirthTail -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem birth_reweight_norm (u : ℝ) (hu : 1 ≤ u) (H c : ℕ) (z : ℂ) :
    ‖if H<c then ((u:ℂ)^c)⁻¹*z else 0‖ ≤ (u^H)⁻¹*‖z‖ := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  by_cases hc : H<c
  · rw [if_pos hc,norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hu0.le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    have hp : u^H ≤ u^c := pow_right_mono₀ hu (Nat.le_of_lt hc)
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hu0 H) hp
  · rw [if_neg hc,norm_zero]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hu0.le H)) (norm_nonneg z)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- Genuine signed mixed-history birth-tail bound. The right side is
the explicitly defined complete positive tilted chain, with ALL active
G/E costs still present. No presumed norm or saving hypothesis occurs. -/
theorem source_original_ACTUAL_MIXED_background_birth_tail434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (hu : 1 ≤ u) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hzero : seen ∩ B=∅) (H : ℕ) :
    ‖sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk
      (fun out st => if H<(st ∩ B).card then F out st else 0) y seen‖ ≤
    (u^H)⁻¹ *
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk (fun out st => ‖F out st‖) y seen := by
  let T := fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) =>
    if H<(st ∩ B).card then ((u:ℂ)^(st ∩ B).card)⁻¹*F out st else 0
  have hu0 : 0<u := lt_of_lt_of_le zero_lt_one hu
  have hut : (u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu0)
  have ht (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) :
      (u:ℂ)^(st ∩ B).card*T out st =
        if H<(st ∩ B).card then F out st else 0 := by
    dsimp only [T]
    split_ifs
    · rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hut),one_mul]
    · rw [mul_zero]
  have hg := source_original_MEMORY_history_background_birth_terminal434
    SP sm BP bm J ell m cap patterns background hi q u Vs V mu K zeta theta k N
    T n h havoid start sk y seen hzero
  simp_rw [ht] at hg
  rw [← hg]
  have hm := source_original_ACTUAL_MIXED_absolute_majorant434
    SP sm BP bm J ell m cap patterns background q u Vs V mu K zeta theta k N
    T (fun out st => (u^H)⁻¹*‖F out st‖)
    (fun out st => birth_reweight_norm u hu H (st ∩ B).card (F out st))
    n h start sk y seen
  rw [source_original_ACTUAL_MIXED_absolute_smul434] at hm
  exact hm
end Green64Analytic.CorrelationSquare

end

end

