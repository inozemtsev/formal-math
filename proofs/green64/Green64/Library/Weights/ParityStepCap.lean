module

public import Green64.Library.Analysis.Estimates.AllPrimeStepCap
public import Green64.Library.Correlation.Part035
public import Green64.Library.Correlation.MemoryActualDomain

@[expose] public section

/-!
# Weights / ParityStepCap

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualParityStepCap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

/-- Fixed before L, path length, marks, patterns and all repeated auxiliary draws. -/
def b651ParityDConstant434 (J : ℕ) : ℝ :=
  4*((J+1 : ℕ):ℝ)*(4+(Real.log 2)⁻¹)

theorem b651_parity_D_constant_pos434 (J : ℕ) : 0 < b651ParityDConstant434 J := by
  unfold b651ParityDConstant434
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

private theorem b651_small_mem_G (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : SourceNativeMemorySG434 20 L hS) (p : SourceNativeMemorySP434 20 L hS g) :
    p.val ∈ sourceNativeOriginalG434 20 L := by
  rw [source_native_original_G_identity434 20 L hS hL]
  cases g with
  | none => exact Finset.mem_union_left _ (Finset.mem_union_left _ p.property)
  | some i =>
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,p.property⟩))

private theorem b651_big_mem_G (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : sourceNativeOriginalBigType434 20 L) (p : SourceNativeMemoryBP434 20 L g) :
    p.val ∈ sourceNativeOriginalG434 20 L := by
  rw [source_native_original_G_identity434 20 L hS hL]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,p.property⟩)

/-- Actual r20 source D, with complete original SMALL/BIG groups. The
bound is derived from the literal prime range and the proved logarithmic
number of groups; no maximum-D or total-mass premise is supplied. -/
theorem b651_actual_parity_D_cap434 (J m : ℕ) (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    {N : ℕ} (ω : B643AllPrimePath434
      (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) J 1 m patterns N)
    (i : Fin N) :
    (b643AllPrimeD434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω i : ℝ) ≤
      Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)) := by
  have he : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr (by norm_num : (0:ℝ)<1))
  have hL1 : 1 < L := he.trans_le hL
  have hlog : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  let C0 : ℝ := 4+(Real.log 2)⁻¹
  have hcounts := source_native_original_group_upper_counts434 20 L hS (by norm_num) hL
  have hGs : (Fintype.card (SourceNativeMemorySG434 20 L hS):ℝ) ≤ C0*Real.log L := by
    simp only [SourceNativeMemorySG434,Fintype.card_option,Nat.cast_add,Nat.cast_one]
    dsimp [C0]
    nlinarith [hcounts.1]
  have hGb : (Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ) ≤ C0*Real.log L := by
    dsimp [C0]
    nlinarith [hcounts.2]
  have hU : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg (zero_le_one.trans hL1.le) _
  have hraw := b651_all_prime_D_cap434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns
    (L^(2/5:ℝ)) hU
    (fun g p => (b638_actual_full_P_range434 L hL1.le p.val
      (b651_small_mem_G L hL1 hS g p)).2.2)
    (fun g p => (b638_actual_full_P_range434 L hL1.le p.val
      (b651_big_mem_G L hL1 hS g p)).2.2) ω i
  apply hraw.trans (Real.exp_le_exp.mpr ?_)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hGs hGb)
      (show 0 ≤ 2*((J+1:ℕ):ℝ) by positivity)) hU
  dsimp [b651ParityDConstant434,C0] at hh ⊢
  nlinarith only [hh]

/-- Numerical maximum for the original shift 2k, retaining |k| in its hypothesis. -/
def b651ParityMaxStep434 (J : ℕ) (Ck L : ℝ) : ℝ :=
  2*L^Ck*Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))

private theorem b651_shift_two_abs (L Ck : ℝ) (k : ℤ)
    (hk : (k.natAbs : ℝ) ≤ L^Ck) : |((2*k:ℤ):ℝ)| ≤ 2*L^Ck := by
  have hk' : |(k:ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  calc
    _ = 2*|(k:ℝ)| := by push_cast; rw [abs_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hk' (by norm_num)

/-- True maximum physical displacement, including every repeated factor of D. -/
theorem b651_actual_parity_shift_D_cap434 (J m : ℕ) (Ck L : ℝ)
    (hL : Real.exp 1 ≤ L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    {N : ℕ} (ω : B643AllPrimePath434
      (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) J 1 m patterns N)
    (i : Fin N) (k : ℤ) (hk : (k.natAbs : ℝ) ≤ L^Ck) :
    |((2*k*(b643AllPrimeD434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω i : ℤ) : ℤ):ℝ)| ≤
      b651ParityMaxStep434 J Ck L := by
  have hD := b651_actual_parity_D_cap434 J m L hL hS patterns ω i
  have hk' := b651_shift_two_abs L Ck k hk
  have hd0 : 0 ≤
      (b643AllPrimeD434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω i : ℝ) :=
    Nat.cast_nonneg _
  unfold b651ParityMaxStep434
  rw [Int.cast_mul,Int.cast_natCast,abs_mul,abs_of_nonneg hd0]
  exact mul_le_mul hk' hD (Nat.cast_nonneg _) ((abs_nonneg _).trans hk')

/-- Every finite prefix of the complete actual r20 signed path has the
same proved radius, uniformly in all patterns, frames and ordered marks. -/
theorem b651_actual_parity_prefix_cap434 (J m : ℕ) (Ck L : ℝ)
    (hL : Real.exp 1 ≤ L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    {N : ℕ} (ω : B643AllPrimePath434
      (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) J 1 m patterns N)
    (k : ℤ) (hk : (k.natAbs : ℝ) ≤ L^Ck) (t : ℕ) :
    |(b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω (2*k) t : ℝ)| ≤
      (N:ℝ)*b651ParityMaxStep434 J Ck L := by
  have hh := b651_all_prime_offset_cap434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω (2*k)
    (Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))) (Real.exp_nonneg _)
    (fun i => b651_actual_parity_D_cap434 J m L hL hS patterns ω i) t
  have hs := mul_le_mul_of_nonneg_right (b651_shift_two_abs L Ck k hk)
    (Real.exp_nonneg (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)))
  have hN := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
  unfold b651ParityMaxStep434
  exact hh.trans (by nlinarith only [hN])
end Green64Analytic.SourceBlockSieve

end

end

