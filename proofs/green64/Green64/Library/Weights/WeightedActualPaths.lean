module

public import Green64.Library.Sieve.Foundations.MarkedPathCRT

@[expose] public section

/-!
# Weights / WeightedActualPaths

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## WeightedActualPaths -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2000000

def b645ActualMarkedPathDensity434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g)
    (offset : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∏ p ∈ sourceNativeOriginalG434 20 L, ∏ i ∈ Finset.range (N+1),
    if p ∈ b645ActualActiveAt434 L hS M N sm bm i then
      (if (p:ℤ) ∣ (n:ℤ)+offset i then 1 else 0)
    else (if (p:ℤ) ∣ (n:ℤ)+offset i then sourceVisitQ (1/2:ℝ) N i else 1)

def b645ActualMarkedPathModel434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g)
    (offset : ℕ → ℤ) : ℝ :=
  ∏ p ∈ sourceNativeOriginalG434 20 L,
    (∑ r ∈ Finset.range p,
      b641PathPrimeWeight434 (Finset.range (N+1))
        (b645ActualActiveAt434 L hS M N sm bm) (sourceVisitQ (1/2:ℝ) N) offset p r)/(p:ℝ)

/-- Actual same-integer CRT for every finite COMPLEX signed path family.
The original coefficients are added coherently in the main term.
Only the accumulated error is charged to the true model-weighted absolute mass.
No hCRT, hError, independence, or cardinality premise is present. -/
theorem b645_eventually_actual_weighted_paths_CRT434
    (E gamma : ℝ) (hE : 0 ≤ E) (hgamma : 0 < gamma) (M : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    ∀ {Ω : Type} [Fintype Ω],
    ∀ (sm : Ω → Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
        Fin M → SourceNativeMemorySP434 20 L hS g)
      (bm : Ω → Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
        Fin M → SourceNativeMemoryBP434 20 L g)
      (coeff : Ω → ℂ) (offset : Ω → ℕ → ℤ) (lo hi : ℕ),
      Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
      ‖(∑ ω : Ω, coeff ω *
          ((∑ n ∈ Finset.Ico lo hi,
            b645ActualMarkedPathDensity434 L hS M N (sm ω) (bm ω) (offset ω) n : ℝ) : ℂ)) -
        (((hi-lo:ℕ):ℝ):ℂ) * (∑ ω : Ω, coeff ω *
          (b645ActualMarkedPathModel434 L hS M N (sm ω) (bm ω) (offset ω) : ℂ))‖ ≤
      ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) *
        ∑ ω : Ω, ‖coeff ω‖ *
          b645ActualMarkedPathModel434 L hS M N (sm ω) (bm ω) (offset ω) := by
  filter_upwards [b645_eventually_actual_all_marked_path_CRT434 E gamma hE hgamma M]
    with L h
  refine ⟨h.1, ?_⟩
  intro hS
  dsimp only
  intro Ω inst sm bm coeff offset lo hi hH
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let H : ℝ := ((hi-lo:ℕ):ℝ)
  let eps : ℝ := L^(-E*(N:ℝ))
  let V := fun ω : Ω => b645ActualMarkedPathModel434 L hS M N (sm ω) (bm ω) (offset ω)
  let S := fun ω : Ω => ∑ n ∈ Finset.Ico lo hi,
    b645ActualMarkedPathDensity434 L hS M N (sm ω) (bm ω) (offset ω) n
  have hcrt (ω : Ω) : |S ω - H*V ω| ≤ (H*V ω)*eps :=
    h.2 hS (sm ω) (bm ω) lo hi hH (offset ω)
  have he :
      (∑ ω : Ω, coeff ω * (S ω : ℂ)) -
        (H : ℂ) * (∑ ω : Ω, coeff ω * (V ω : ℂ)) =
      ∑ ω : Ω, coeff ω * ((S ω - H*V ω : ℝ) : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    push_cast
    ring
  change ‖(∑ ω : Ω, coeff ω * (S ω : ℂ)) -
      (H:ℂ) * (∑ ω : Ω, coeff ω * (V ω : ℂ))‖ ≤
    H*eps*(∑ ω : Ω, ‖coeff ω‖*V ω)
  rw [he]
  calc
    _ ≤ ∑ ω : Ω, ‖coeff ω * ((S ω-H*V ω:ℝ):ℂ)‖ := norm_sum_le _ _
    _ = ∑ ω : Ω, ‖coeff ω‖ * |S ω-H*V ω| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ ω : Ω, ‖coeff ω‖*((H*V ω)*eps) :=
      Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hcrt ω) (norm_nonneg _))
    _ = H*eps*(∑ ω : Ω, ‖coeff ω‖*V ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
end Green64Analytic.SourceBlockSieve

end

end

