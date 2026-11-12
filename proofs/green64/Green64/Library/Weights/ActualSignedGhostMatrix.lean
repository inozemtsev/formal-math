module

public import Green64.Library.Weights.Part066

@[expose] public section

/-!
# Weights / ActualSignedGhostMatrix

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedGhostMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact complex signed ghost kernel on finite reachable
Fock output × cumulative numerical prime-history states. -/
def sourceOriginalActualSignedGhostMatrix434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    H → H → ℂ :=
  sourceOriginalSignedFiniteMatrix434
    (sourceOriginalActualSignedFiniteG434
      SP sm BP bm J ell cap q rho N i V mu)

private theorem source_original_ACTUAL_finite_G_zero434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : H) :
    sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap
      q rho N i V mu (fun _ => 0) a = 0 := by
  have hz := source_original_ACTUAL_finite_G_smul434
    SP sm BP bm J ell cap q rho N i V mu (0:ℂ)
    (fun _ : H => 0) a
  simpa only [zero_mul] using hz

/-- Matrix action equals the ORIGINAL finite G operator, without
dropping complex coefficients or averaging the chronological seen. -/
theorem source_original_ACTUAL_signed_G_matrix_exact434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : H → ℂ) (a : H) :
    sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu f a =
      ∑ b : H, sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        q rho N i V mu a b * f b := by
  let T := sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu
  exact source_original_signed_finite_matrix_apply434 T
    (fun f g a => source_original_ACTUAL_finite_G_add434
      SP sm BP bm J ell cap q rho N i V mu f g a)
    (fun c f a => source_original_ACTUAL_finite_G_smul434
      SP sm BP bm J ell cap q rho N i V mu c f a)
    (fun a => source_original_ACTUAL_finite_G_zero434
      SP sm BP bm J ell cap q rho N i V mu a) f a

/-- The ORIGINAL reachable ghost G output is a literal finite
complex matrix acting on the unmodified terminal Fock×seen values. -/
theorem source_original_ACTUAL_original_G_matrix_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hmu : ∀ g p, 0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu a.val.1 a.val.2 F =
    ∑ b : H, sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
      q rho N i V mu a b * F b.val.1 b.val.2 := by
  calc
    _ = sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap
        q rho N i V mu
        (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
        a := source_original_ACTUAL_signed_finite_G_exact434
          SP sm BP bm J ell cap hi hcap q rho N i Vs V mu hVs hmu F a
    _ = _ := source_original_ACTUAL_signed_G_matrix_exact434
      SP sm BP bm J ell cap q rho N i V mu
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F) a

/-- Genuine complex-bilinear forward/backward G pairing: the prefix
density is transported by the transpose of the exact Fock×seen
matrix, NOT by a positive history-max or independent resampling. -/
theorem source_original_ACTUAL_signed_G_prefix_suffix_pairing434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalActualSignedFiniteG434
      SP sm BP bm J ell cap q rho N i V mu f a) =
    ∑ b : H, (∑ a : H, w a *
      sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        q rho N i V mu a b) * f b := by
  let T := sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu
  exact source_original_signed_finite_matrix_pairing434 T
    (fun f g a => source_original_ACTUAL_finite_G_add434
      SP sm BP bm J ell cap q rho N i V mu f g a)
    (fun c f a => source_original_ACTUAL_finite_G_smul434
      SP sm BP bm J ell cap q rho N i V mu c f a)
    (fun a => source_original_ACTUAL_finite_G_zero434
      SP sm BP bm J ell cap q rho N i V mu a) w f
end Green64Analytic.CorrelationSquare

end

end

