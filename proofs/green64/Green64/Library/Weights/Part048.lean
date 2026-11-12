module

public import Green64.Library.Correlation.PhysicalSum
public import Green64.Library.Weights.ParityDensity
public import Green64.Library.Weights.ParityLocalizationWindow
public import Green64.Library.Weights.Part004
public import Green64.Library.Correlation.Part021
public import Green64.Library.Correlation.Part035
public import Green64.Library.Correlation.MemoryActualDomain
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.R6CofinalBands
public import Green64.Library.Correlation.Part032
public import Mathlib
public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part013
public import Green64.Library.Weights.Part042

@[expose] public section

/-!
# Weights / Part048

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualParityReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000

local instance b653ActualReturnFrameFintype434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J ell m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m) :
    Fintype (MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- Source-exact physical Parity return expansion at every positive length.
This is the full physical B650 carrier/frame sum with one original mark
mass and freely summed final marks, rewritten into the ACTUAL all-P
same-integer density. Knu is preserved pointwise, never majorized. -/
theorem b653_actual_parity_physical_return434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J ell m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (N : ℕ) (hN : 0<N) (n : ℕ)
    (Vsmall : SourceNativeMemorySG434 20 L hS → ℝ)
    (Vbig : sourceNativeOriginalBigType434 20 L → ℝ)
    (Knu : SourcePatternK (SourceNativeMemoryBP434 20 L) J ell m patterns)
    (zeta : ℝ) (k : ℤ) :
    (b650IntegerStateMass434 J ell Vsmall Vbig : ℂ) *
      (∑ states : Fin (N+1) → B650IntegerPhysicalState434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell positions,
        ∑ frames : Fin N → MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
          (SourceNativeMemoryBP434 20 L) J ell m patterns,
          if (states 0).val.1.val=(n:ℤ) ∧ (states (Fin.last N)).val.1.val=(n:ℤ) then
            ∏ i : Fin N, b650IntegerFrameScalar434
              (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
              (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns positions
              (1/2:ℝ) Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
              (states i.castSucc) (states i.succ) (frames i)
          else 0) =
    ∑ ω : B643AllPrimePath434 (SourceNativeMemorySP434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J ell m patterns N,
      if (∀ t : Fin (N+1), (n:ℤ)+b643AllPrimeOffset434
          (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns ω k t.val ∈ positions) ∧
        b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns ω k N=0 then
        b643AllPrimeWeight434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns Vsmall Vbig Knu zeta 0 k ω *
        (b645ActualMarkedPathDensity434 L hS (J+ell) N
          (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val)
          (b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
            (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns ω k) n : ℂ)
      else 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [b653_physical_full_return_sum434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns positions r (n:ℤ)
    (1/2:ℝ) (by norm_num) Vsmall Vbig Knu zeta k]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [b653_actual_parity_integer_integrand434 L hL hS J ell m patterns (r+1) ω k n]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualIntervalWindow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- A finite signed integer carrier with the full original N-step margin
on both sides of the long physical interval. -/
def b654ParityIntervalWindow434 (J : ℕ) (Ck L : ℝ) (lo hi : ℕ) : Finset ℤ :=
  Finset.Icc ((lo:ℤ)-(b651ParityPathRadius434 J Ck L:ℤ))
    ((hi:ℤ)+(b651ParityPathRadius434 J Ck L:ℤ))

/-- The exact integer image of the original natural-number interval.
Only this seed set, not the enlarged carrier, enters the moment sum. -/
def b654ParitySeedPositions434 (lo hi : ℕ) : Finset ℤ :=
  (Finset.Ico lo hi).image (fun n : ℕ => (n:ℤ))

theorem b654_seed_positions_card434 (lo hi : ℕ) :
    (b654ParitySeedPositions434 lo hi).card=hi-lo := by
  unfold b654ParitySeedPositions434
  rw [Finset.card_image_of_injective _ (by
    intro a b h
    change (a:ℤ)=(b:ℤ) at h
    exact_mod_cast h)]
  exact Nat.card_Ico lo hi

theorem b654_sum_seed_positions434 {T : Type*} [AddCommMonoid T]
    (lo hi : ℕ) (F : ℤ → T) :
    (∑ n ∈ b654ParitySeedPositions434 lo hi,F n) =
      ∑ n ∈ Finset.Ico lo hi,F (n:ℤ) := by
  unfold b654ParitySeedPositions434
  apply Finset.sum_image
  intro a ha b hb h
  change (a:ℤ)=(b:ℤ) at h
  exact_mod_cast h

theorem b654_seed_mem_interval_window434 (J : ℕ) (Ck L : ℝ) (lo hi n : ℕ)
    (hn : n ∈ Finset.Ico lo hi) :
    (n:ℤ) ∈ b654ParityIntervalWindow434 J Ck L lo hi := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hn
  have hlo' : (lo:ℤ) ≤ (n:ℤ) := by exact_mod_cast hlo
  have hhi' : (n:ℤ) ≤ (hi:ℤ) := by exact_mod_cast Nat.le_of_lt hhi
  have hr : 0 ≤ (b651ParityPathRadius434 J Ck L:ℤ) := Int.natCast_nonneg _
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- Every original actual all-prime path beginning in the long source
interval stays inside the enlarged physical carrier. This removes the
finite-window indicator by an exact theorem, without dropping signed
paths or applying a global D20 mass bound. -/
theorem b654_actual_parity_path_in_interval_window434
    (J m : ℕ) (Ck L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (ω : B643AllPrimePath434
      (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L)
      J 1 m patterns (2*Nat.ceil (L^(13/25:ℝ))))
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (lo hi n : ℕ) (hn : n ∈ Finset.Ico lo hi) (t : ℕ) :
    (n:ℤ)+b643AllPrimeOffset434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns ω (2*k) t ∈ b654ParityIntervalWindow434 J Ck L lo hi := by
  have hw := b651_actual_parity_prefix_mem_window434 J m Ck L hL hS patterns ω k hk (n:ℤ) t
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hw
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hn
  have hlo' : (lo:ℤ) ≤ (n:ℤ) := by exact_mod_cast hlo
  have hhi' : (n:ℤ) ≤ (hi:ℤ) := by exact_mod_cast Nat.le_of_lt hhi
  apply Finset.mem_Icc.mpr
  constructor <;> omega
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualDyadicWindow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The original enlarged carrier fits in the positive prefix [0,3X]
when its exact original path radius is at most the dyadic length X. -/
theorem b660_dyadic_window_of_radius434 (J : ℕ) (Ck L : ℝ) (X : ℕ)
    (hRadius : b651ParityPathRadius434 J Ck L ≤ X) :
    ∀ n ∈ b654ParityIntervalWindow434 J Ck L X (2*X),
      0 ≤ n ∧ n ≤ ((3*X:ℕ):ℤ) := by
  intro n hn
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hn
  have hr : (b651ParityPathRadius434 J Ck L:ℤ) ≤ (X:ℤ) := by
    exact_mod_cast hRadius
  constructor <;> omega

/-- Actual physical dyads may reach exp(L) times a fixed polynomial and
the original full path window. In the SAME original L, this proves
radius<=X, the full carrier cutoff at 3X, and log X<=2L. The threshold
may depend on J and Cpos; no norm exponent or source tuple is changed.
The statement even permits an arbitrary real polynomial exponent. -/
theorem b660_eventually_actual_dyadic_window434
    (J : ℕ) (Ck Cpos gammaLong : ℝ) (hCk : 0 ≤ Ck) (hLong : 0 < gammaLong) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ ∀ X : ℕ,
      Real.exp (gammaLong*L) ≤ (X:ℝ) →
      (X:ℝ) ≤ 2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ) →
      1 ≤ X ∧ b651ParityPathRadius434 J Ck L ≤ X ∧
      (∀ n ∈ b654ParityIntervalWindow434 J Ck L X (2*X),
        0 ≤ n ∧ n ≤ ((3*X:ℕ):ℤ)) ∧
      (3*(X:ℝ)) ≤ Real.exp (2*L) ∧ Real.log (X:ℝ) ≤ 2*L := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J Ck hCk,
    b638_eventually_const_power434 (1/gammaLong) (1/2) 1 (by norm_num),
    b638_eventually_const_power434 2 (1/2) 1 (by norm_num),
    b638_eventually_poly_exp434 6 Cpos (1/2) (by norm_num) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with L hWindow hLongScale hSqrtScale hPoly hL
  refine ⟨hL,?_⟩
  intro X hLower hUpper
  have hLp : 0 < L := zero_lt_one.trans hL
  have hXpos : 0 < (X:ℝ) := (Real.exp_pos _).trans_le hLower
  have hX : 1 ≤ X := by exact_mod_cast (show 0 < X from by exact_mod_cast hXpos)
  have hLongScale'' : (1/gammaLong)*Real.sqrt L ≤ L := by
    simpa only [Real.rpow_one,←Real.sqrt_eq_rpow] using hLongScale
  have hLongScale' : Real.sqrt L / gammaLong ≤ L := by
    convert hLongScale'' using 1
    ring
  have hSqrtLong : Real.sqrt L ≤ gammaLong*L := by
    have hh := (div_le_iff₀ hLong).mp hLongScale'
    nlinarith only [hh]
  have hSqrtDouble : 2*Real.sqrt L ≤ L := by
    simpa only [Real.rpow_one,←Real.sqrt_eq_rpow] using hSqrtScale
  have hPoly' : 6*L^Cpos ≤ Real.exp (Real.sqrt L) := by
    simpa only [←Real.sqrt_eq_rpow] using hPoly
  have hRadius : (b651ParityPathRadius434 J Ck L:ℝ) ≤ (X:ℝ) :=
    (b651_parity_maxstep_window_bounds434 J Ck L hL.le).2.trans
      (hWindow.2.trans ((Real.exp_le_exp.mpr hSqrtLong).trans hLower))
  have hRadiusNat : b651ParityPathRadius434 J Ck L ≤ X := by exact_mod_cast hRadius
  have hTriple : 3*(X:ℝ) ≤ Real.exp (2*L) := by
    calc
      _ ≤ 3*(2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ)) := by
        nlinarith only [hUpper]
      _ = Real.exp L*(6*L^Cpos)*(b651ParityWindowSize434 J Ck L:ℝ) := by ring
      _ ≤ Real.exp L*Real.exp (Real.sqrt L)*Real.exp (Real.sqrt L) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hPoly' (Real.exp_nonneg _))
          hWindow.2 (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (L+2*Real.sqrt L) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hSqrtDouble])
  have hXE : (X:ℝ) ≤ Real.exp (2*L) :=
    (show (X:ℝ) ≤ 3*(X:ℝ) by nlinarith [hXpos]).trans hTriple
  have hLog : Real.log (X:ℝ) ≤ 2*L := by
    simpa only [Real.log_exp] using Real.log_le_log hXpos hXE
  exact ⟨hX,hRadiusNat,b660_dyadic_window_of_radius434 J Ck L X hRadiusNat,hTriple,hLog⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualFrameDyadCap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Every literal original frame divisor is bounded by the SAME rounded
physical window. No nonzero-row, CRT, support or mass condition is used.
All prime slots and auxiliary draws remain in the one-edge native path. -/
theorem b660_actual_parity_frame_D_window434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (Ck : ℝ) (hCk : 0 ≤ Ck)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) :
    (b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x f:ℝ) ≤ (b651ParityWindowSize434 J Ck L:ℝ) := by
  let omega := b643AllPrimePathOf434
    (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns (fun _ : Fin 2 => x) (fun _ : Fin 1 => f)
  have hD := b651_actual_parity_D_cap434 J m L hL hFamily patterns omega 0
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hPower : 1 ≤ L^Ck := Real.one_le_rpow hL1 hCk
  have hStep : Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)) ≤
      b651ParityMaxStep434 J Ck L := by
    unfold b651ParityMaxStep434
    have he0 := Real.exp_nonneg (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))
    have hm := mul_le_mul_of_nonneg_right hPower he0
    nlinarith only [hm,he0]
  have hWindow := b651_parity_maxstep_window_bounds434 J Ck L hL1
  exact hD.trans (hStep.trans (hWindow.1.trans hWindow.2))

/-- The actual frame cutoff range X<=n<=2 Z D and the source polynomial
Z-range imply precisely the upper dyad cap consumed by B660. In
particular the original Z may be as large as exp(L)*L^Cpos. -/
theorem b660_actual_frame_cutoff_dyad_cap434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (Ck Cpos : ℝ) (hCk : 0 ≤ Ck)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (X : ℕ) (n Z : ℝ) (hXn : (X:ℝ) ≤ n)
    (hn : n ≤ 2*Z*(b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x f:ℝ))
    (hZ : Z ≤ Real.exp L*L^Cpos) :
    (X:ℝ) ≤ 2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ) := by
  have hD := b660_actual_parity_frame_D_window434 L hL hFamily J m Ck hCk patterns x f
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  calc
    _ ≤ n := hXn
    _ ≤ _ := hn
    _ = 2*(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x f:ℝ)) := by ring
    _ ≤ 2*((Real.exp L*L^Cpos)*(b651ParityWindowSize434 J Ck L:ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hZ hD (Nat.cast_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _))) (by norm_num)
    _ = _ := by ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeActualAuxSetBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Exact forbidden-prime SET of actual native free B26 auxiliary draws,
built from the source-dependent pattern slots. Repeated draws are allowed:
Finset.image removes duplicate VALUES only for the forbidden membership,
never from the source probability law or original divisor. -/
noncomputable def sourceNativeOriginalAuxValueSet434
    (r : ℕ) (L : ℝ) (J m : ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat) : Finset ℕ :=
  (Finset.univ : Finset
    (Σ g : sourceNativeOriginalBigType434 r L, ↥(pat.free g))).image
      (fun z => (aux z.1 z.2).val)

/-- No invented number of auxiliary labels: the original
SourcePattern.free_bound supplies at most m labels per genuine BIG group.
All multiplicities remain in aux and only its forbidden SET is bounded. -/
theorem source_native_original_aux_value_set_card434
    (r : ℕ) (L : ℝ) (J m : ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat) :
    (sourceNativeOriginalAuxValueSet434 r L J m pat aux).card ≤
      m * Fintype.card (sourceNativeOriginalBigType434 r L) := by
  classical
  calc
    _ ≤ (Finset.univ : Finset
          (Σ g : sourceNativeOriginalBigType434 r L, ↥(pat.free g))).card :=
      Finset.card_image_le
    _ = ∑ g : sourceNativeOriginalBigType434 r L,
          (pat.free g).card := by
            simp [Fintype.card_sigma]
    _ ≤ ∑ _g : sourceNativeOriginalBigType434 r L, m := by
      apply Finset.sum_le_sum
      intro g hg
      exact pat.free_bound g
    _ = m * Fintype.card (sourceNativeOriginalBigType434 r L) := by
      simp [mul_comm]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalAllPJDirty -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- ORIGINAL source common RAW J slots exist in ALL P groups, including
S, remaining Ts, and all Tb. Independent full harmonic source law,
with repetitions, and the actual BIG free auxiliary indices are not
conditioned or resized.

An arbitrary complex continuation K bounded by B incurs an L^-D
loss on repeated J draws or any collision with the two original
ordinary endpoints or the true BIG auxiliary value set. The
source P-group count O(log L), genuine 1/(pV_g) masses and
source SourcePattern.free_bound provide ALL numerical inputs;
no external auxiliary-card or prime-mass hypotheses. This is the
correct ALL-P domain for the RAW R_J factor. -/
theorem eventually_native_original_ALL_P_J_dirty_true_aux434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ)
        (K : ((SourceNativeOriginalAllP434 r L) × Fin J → ℕ) → ℂ)
        (B : ℝ),
      0 ≤ B → 0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      (∀ s ∈ Fintype.piFinset
           (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
              SourceNativeOriginalAllPBand434 r L i.1), ‖K s‖ ≤ B) →
      ‖∑ s ∈ Fintype.piFinset
         (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
            SourceNativeOriginalAllPBand434 r L i.1),
        if sourceSharedClean434
            (fun _ => sourceSharedForbidden434 w wp
              (sourceNativeOriginalAuxValueSet434 r L J m pat aux)) s
        then (0:ℂ)
        else (sourceSharedLaw434
          (fun i => sourcePrimeSharedAtom434
            (sourceNativeOriginalAllPMass434 r L i.1)) s:ℂ) * K s‖ ≤
        B*L^(-D) := by
  classical
  let Cgroup : ℝ := 3+(Real.log 2)⁻¹
  let Cbound : ℝ := (tmax:ℝ)*Cgroup
  let Vfloor : ℝ := Real.log (6/5:ℝ)/2
  have hv : 0 < Vfloor :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hCG : 0 ≤ Cgroup := by
    dsimp [Cgroup]
    have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  have hCB : 0 ≤ Cbound := mul_nonneg (Nat.cast_nonneg _) hCG
  filter_upwards [
    eventually_source_actual_shared_arbitrary_envelope434
      (1/10:ℝ) Vfloor Cbound Cbound D
      (by norm_num) hv hCB hCB,
    eventually_native_original_ALL_P_masses434 r,
    eventually_source_native_original_group_masses434 r hr,
    eventually_ge_atTop (Real.exp 1)]
    with L hSave hVMass hMass hL
  refine ⟨hL, ?_⟩
  intro J m pat aux hJ hm w wp K B hB hw hwp hwSize hwpSize hK
  obtain ⟨_,hS,_⟩ := hMass
  let G := SourceNativeOriginalAllP434 r L
  have hCount : (Fintype.card G:ℝ) ≤ Cgroup*Real.log L := by
    simpa only [G,SourceNativeOriginalAllP434,
      sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hBigCount :
      (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      Cgroup*Real.log L :=
    (source_native_original_group_upper_counts434 r L hS hr hL).2
  have hLog : 0 ≤ Real.log L :=
    Real.log_nonneg ((Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)).trans hL)
  have hJR : (J:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hJ
  have hmR : (m:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hm
  have hCard : (Fintype.card (G × Fin J):ℝ) ≤
      Cbound*Real.log L := by
    have hProd : (Fintype.card G:ℝ)*(J:ℝ) ≤
        (Cgroup*Real.log L)*(tmax:ℝ) := by
      exact mul_le_mul hCount hJR
        (Nat.cast_nonneg _) (mul_nonneg hCG hLog)
    have hEq : (Fintype.card (G × Fin J):ℝ) =
        (Fintype.card G:ℝ)*(J:ℝ) := by simp
    rw [hEq]
    dsimp [Cbound]
    nlinarith [hProd]
  have hAuxNat := source_native_original_aux_value_set_card434
    r L J m pat aux
  have hAuxReal :
      ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      (m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) := by
    exact_mod_cast hAuxNat
  have hAux : ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      Cbound*Real.log L := by
    calc
      _ ≤ (m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) :=
        hAuxReal
      _ ≤ (tmax:ℝ)*(Cgroup*Real.log L) :=
        mul_le_mul hmR hBigCount
          (Nat.cast_nonneg _) (Nat.cast_nonneg tmax)
      _ = Cbound*Real.log L := by dsimp [Cbound]; ring
  have hV : ∀ i : G × Fin J,
      sourceNativeOriginalAllPMass434 r L i.1 =
        ∑ p ∈ SourceNativeOriginalAllPBand434 r L i.1, 1/(p:ℝ) := by
    intro i
    rfl
  have hVmin : ∀ i : G × Fin J,
      Vfloor ≤ sourceNativeOriginalAllPMass434 r L i.1 :=
    fun i => (hVMass i.1).1
  have hPmin : ∀ i : G × Fin J,
      ∀ p ∈ SourceNativeOriginalAllPBand434 r L i.1,
        Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) := by
    intro i p hp
    exact (source_native_original_ALL_P_prime_range434
      r L (by
        have : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        exact this.trans hL)
      i.1 p hp).2.1
  exact hSave
    (fun i : G × Fin J => SourceNativeOriginalAllPBand434 r L i.1)
    (fun i : G × Fin J => sourceNativeOriginalAllPMass434 r L i.1)
    w wp (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
    K B hB hw hwp hwSize hwpSize
    hCard hAux hV hVmin hPmin hK
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalBIGSharedRealAux -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Unconditional-on-aux-size native shared-draw defect on the ORIGINAL
full BIG family and actual SourcePattern.free / SourceBigAux slots. For
fixed tmax and exponent D, the exact forbidden set of all actual
auxiliary prime VALUES has the cardinality needed for arbitrary log
saving. This remains a one-shared-draw Green64 CLEAN/dirty expectation;
it is not a complete J-fold RAW R_J bound. -/
theorem eventually_native_original_BIG_shared_dirty_true_aux434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      m ≤ tmax →
      ∀ (w wp : ℕ)
        (K : (sourceNativeOriginalBigType434 r L → ℕ) → ℂ)
        (B : ℝ),
      0 ≤ B → 0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      (∀ s ∈ Fintype.piFinset (sourceNativeOriginalTb434 r L),
        ‖K s‖ ≤ B) →
      ‖∑ s ∈ Fintype.piFinset (sourceNativeOriginalTb434 r L),
        if sourceSharedClean434
             (fun _ => sourceSharedForbidden434 w wp
                (sourceNativeOriginalAuxValueSet434 r L J m pat aux)) s
        then (0:ℂ)
        else (sourceSharedLaw434
          (fun i => sourcePrimeSharedAtom434
            (sourceNativeOriginalVbig434 r L i)) s : ℂ) * K s‖ ≤
        B*L^(-D) := by
  classical
  let Cgroup : ℝ := 3+(Real.log 2)⁻¹
  let Ca : ℝ := (tmax:ℝ)*Cgroup
  have hCgroup : 0 ≤ Cgroup := by
    dsimp [Cgroup]
    have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  have hCa : 0 ≤ Ca := mul_nonneg (Nat.cast_nonneg _) hCgroup
  filter_upwards [
      eventually_native_original_BIG_shared_dirty_envelope434
        r hr Ca D hCa,
      eventually_source_native_original_group_masses434 r hr,
      eventually_ge_atTop (Real.exp 1)]
    with L hSave hMass hL
  refine ⟨hL, ?_⟩
  intro J m pat aux hm w wp K B hB hw hwp hwSize hwpSize hK
  obtain ⟨_, hS, _⟩ := hMass
  have hCount : (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      Cgroup * Real.log L := (source_native_original_group_upper_counts434
        r L hS hr hL).2
  have hlog : 0 ≤ Real.log L :=
    Real.log_nonneg ((Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)).trans hL)
  have hAuxNat := source_native_original_aux_value_set_card434 r L J m pat aux
  have hAuxReal : ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      (m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) := by
    exact_mod_cast hAuxNat
  have hmReal : (m:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hm
  have hAux : ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      Ca * Real.log L := by
    calc
      _ ≤ (m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) := hAuxReal
      _ ≤ (tmax:ℝ)*(Cgroup * Real.log L) := by
        exact mul_le_mul hmReal hCount
          (Nat.cast_nonneg _) (Nat.cast_nonneg tmax)
      _ = Ca * Real.log L := by dsimp [Ca]; ring
  exact hSave.2 w wp (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
    K B hB hw hwp hwSize hwpSize hAux hK
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalBIGJSharedDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The REAL original J-ordered independent harmonic BIG source law,
with all J slots per group, no distinctness conditioning, and the
exact source pattern dependent auxiliary prime set. The invalid event
includes same-group collisions, BOTH endpoint prime divisors and the
other auxiliary labels. A single threshold before all moving J<=tmax
and m<=tmax gives arbitrary logarithmic saving for arbitrary complex
physical kernel envelope B. This proves all-J BAD-MASS, NOT YET the
full weighted RAW ratio R_J-1 identity. -/
theorem eventually_native_original_BIG_J_shared_dirty_true_aux434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ)
        (K : ((sourceNativeOriginalBigType434 r L) × Fin J → ℕ) → ℂ)
        (B : ℝ),
      0 ≤ B → 0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      (∀ s ∈ Fintype.piFinset
           (fun i : (sourceNativeOriginalBigType434 r L) × Fin J =>
              sourceNativeOriginalTb434 r L i.1), ‖K s‖ ≤ B) →
      ‖∑ s ∈ Fintype.piFinset
         (fun i : (sourceNativeOriginalBigType434 r L) × Fin J =>
            sourceNativeOriginalTb434 r L i.1),
        if sourceSharedClean434
            (fun _ => sourceSharedForbidden434 w wp
              (sourceNativeOriginalAuxValueSet434 r L J m pat aux)) s
        then (0:ℂ)
        else (sourceSharedLaw434
          (fun i => sourcePrimeSharedAtom434
            (sourceNativeOriginalVbig434 r L i.1)) s:ℂ) * K s‖ ≤
        B*L^(-D) := by
  classical
  let Cgroup : ℝ := 3+(Real.log 2)⁻¹
  let Cbound : ℝ := (tmax:ℝ)*Cgroup
  let Vfloor : ℝ := Real.log (6/5:ℝ)/2
  have hv : 0 < Vfloor :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hCG : 0 ≤ Cgroup := by
    dsimp [Cgroup]
    have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  have hCB : 0 ≤ Cbound := mul_nonneg (Nat.cast_nonneg _) hCG
  filter_upwards [
      eventually_source_actual_shared_arbitrary_envelope434
        (3/10:ℝ) Vfloor Cbound Cbound D
        (by norm_num) hv hCB hCB,
      eventually_source_native_original_group_masses434 r hr,
      eventually_ge_atTop (Real.exp 1)]
    with L hSave hMass hL
  refine ⟨hL, ?_⟩
  intro J m pat aux hJ hm w wp K B hB hw hwp hwSize hwpSize hK
  obtain ⟨_, hS, hMasses⟩ := hMass
  let G := sourceNativeOriginalBigType434 r L
  have hCount : (Fintype.card G:ℝ) ≤ Cgroup * Real.log L :=
    (source_native_original_group_upper_counts434 r L hS hr hL).2
  have hLog : 0 ≤ Real.log L :=
    Real.log_nonneg ((Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)).trans hL)
  have hCard : (Fintype.card (G × Fin J):ℝ) ≤ Cbound * Real.log L := by
    have hJR : (J:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hJ
    have hProd : (Fintype.card G:ℝ)*(J:ℝ) ≤
        (Cgroup*Real.log L)*(tmax:ℝ) := by
      exact mul_le_mul hCount hJR
        (Nat.cast_nonneg _) (mul_nonneg hCG hLog)
    have hEq : (Fintype.card (G × Fin J):ℝ) =
        (Fintype.card G:ℝ)*(J:ℝ) := by simp
    rw [hEq]
    dsimp [Cbound]
    nlinarith [hProd]
  have hAuxNat := source_native_original_aux_value_set_card434
    r L J m pat aux
  have hmR : (m:ℝ) ≤ (tmax:ℝ) := by exact_mod_cast hm
  have hAuxReal :
      ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      (m:ℝ)*(Fintype.card G:ℝ) := by
    exact_mod_cast hAuxNat
  have hAux : ((sourceNativeOriginalAuxValueSet434 r L J m pat aux).card:ℝ) ≤
      Cbound*Real.log L := by
    calc
      _ ≤ (m:ℝ)*(Fintype.card G:ℝ) := hAuxReal
      _ ≤ (tmax:ℝ)*(Cgroup*Real.log L) := by
        exact mul_le_mul hmR hCount
          (Nat.cast_nonneg _) (Nat.cast_nonneg tmax)
      _ = Cbound*Real.log L := by dsimp [Cbound]; ring
  have hV : ∀ i : G × Fin J,
      sourceNativeOriginalVbig434 r L i.1 =
        ∑ p ∈ sourceNativeOriginalTb434 r L i.1, 1/(p:ℝ) := by
    intro i
    simp only [sourceNativeOriginalVbig434, one_div]
  have hVmin : ∀ i : G × Fin J,
      Vfloor ≤ sourceNativeOriginalVbig434 r L i.1 :=
    fun i => (hMasses hS).2.2 i.1 |>.1
  have hPmin : ∀ i : G × Fin J,
      ∀ p ∈ sourceNativeOriginalTb434 r L i.1,
        Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ) := by
    intro i p hp
    exact (source_native_original_Tb_prime_range434 r L i.1 p hp).2.1
  exact hSave
    (fun i : G × Fin J => sourceNativeOriginalTb434 r L i.1)
    (fun i : G × Fin J => sourceNativeOriginalVbig434 r L i.1)
    w wp (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
    K B hB hw hwp hwSize hwpSize
    hCard hAux hV hVmin hPmin hK
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CofinalOriginalGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The EXACT original r=6 finite SMALL P-group index set at
L_N = ((3/2) 2^N)^10, WITHOUT changing source interval endpoints:
all j between 8N+2 and 9N+2, inclusive. -/
theorem source_native_r6_cofinal_small_groups_exact434
    (N : ℕ) :
    sourceNativeOriginalSmallIndices434 6
      (sourceNativeR6CofinalL434 N) =
      Finset.Icc (8*N+2) (9*N+2) := by
  classical
  let L := sourceNativeR6CofinalL434 N
  have hu : (3/2:ℝ) ≤ sourceNativeR6CofinalRoot434 N := by
    unfold sourceNativeR6CofinalRoot434
    have h : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : 1 < L := by
    have hh : (1:ℝ)<sourceNativeR6CofinalRoot434 N := by
      linarith
    unfold L sourceNativeR6CofinalL434
    exact one_lt_pow₀ hh (by norm_num : (10:ℕ)≠0)
  ext j
  rw [Finset.mem_Icc]
  unfold sourceNativeOriginalSmallIndices434
  simp only [Finset.mem_filter]
  change (j ∈ sourceOriginalPAllGroupIndices 6 L ∧
      (L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(1/5:ℝ))) ↔
    8*N+2 ≤ j ∧ j ≤ 9*N+2
  rw [source_original_P_all_groups_mem_iff 6 L (by norm_num) hL]
  change (sourceOriginalPGroupIndex 6 L j ∧
      (L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(1/5:ℝ))) ↔ _
  have hBand := source_native_r6_cofinal_small_band_iff434 N j
  change (L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(1/5:ℝ)) ↔
    8*N+2 ≤ j ∧ j ≤ 9*N+2 at hBand
  dsimp [sourceOriginalPGroupIndex]
  constructor
  · intro h
    exact hBand.mp h.2
  · intro h
    have hsmall := hBand.mpr h
    exact ⟨Or.inl hsmall,hsmall⟩

/-- The EXACT native r=6 BIG indices are independent of the SMALL
count and equal [6N+1,7N] on the cofinal geometric scales. -/
theorem source_native_r6_cofinal_big_groups_exact434
    (N : ℕ) :
    sourceNativeOriginalBigIndices434 6
      (sourceNativeR6CofinalL434 N) =
      Finset.Icc (6*N+1) (7*N) := by
  classical
  let L := sourceNativeR6CofinalL434 N
  have hu : (3/2:ℝ) ≤ sourceNativeR6CofinalRoot434 N := by
    unfold sourceNativeR6CofinalRoot434
    have h : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : 1 < L := by
    have hh : (1:ℝ)<sourceNativeR6CofinalRoot434 N := by
      linarith
    unfold L sourceNativeR6CofinalL434
    exact one_lt_pow₀ hh (by norm_num : (10:ℕ)≠0)
  ext j
  rw [Finset.mem_Icc]
  unfold sourceNativeOriginalBigIndices434
  simp only [Finset.mem_filter]
  change (j ∈ sourceOriginalPAllGroupIndices 6 L ∧
      (L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(2/5:ℝ))) ↔
    6*N+1 ≤ j ∧ j ≤ 7*N
  rw [source_original_P_all_groups_mem_iff 6 L (by norm_num) hL]
  change (sourceOriginalPGroupIndex 6 L j ∧
      (L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(2/5:ℝ))) ↔ _
  have hBand := source_native_r6_cofinal_big_band_iff434 N j
  change (L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(2/5:ℝ)) ↔
    6*N+1 ≤ j ∧ j ≤ 7*N at hBand
  dsimp [sourceOriginalPGroupIndex]
  constructor
  · intro h
    exact hBand.mp h.2
  · intro h
    have hbig := hBand.mpr h
    exact ⟨Or.inr hbig,hbig⟩

/-- The original r=6 SMALL group count is EXACTLY N+1. -/
theorem source_native_r6_cofinal_small_card434 (N : ℕ) :
    (sourceNativeOriginalSmallIndices434 6
      (sourceNativeR6CofinalL434 N)).card = N+1 := by
  rw [source_native_r6_cofinal_small_groups_exact434,Nat.card_Icc]
  omega

/-- The original r=6 BIG group count is EXACTLY N, with N=0
giving the correctly empty BIG interval. -/
theorem source_native_r6_cofinal_big_card434 (N : ℕ) :
    (sourceNativeOriginalBigIndices434 6
      (sourceNativeR6CofinalL434 N)).card = N := by
  rw [source_native_r6_cofinal_big_groups_exact434,Nat.card_Icc]
  omega

/-- Every original P group appears exactly once, and the complete
source r=6 P group family has an ODD cardinal 2N+1 on L_N.
This is a cofinal selection of REAL ORIGINAL P intervals, NOT
a relabeling of the SMALL/BIG group families or an averaged claim. -/
theorem source_native_r6_cofinal_ALL_P_card434 (N : ℕ) :
    Fintype.card (SourceNativeOriginalAllP434 6
      (sourceNativeR6CofinalL434 N)) = 2*N+1 := by
  let L := sourceNativeR6CofinalL434 N
  have hu : (3/2:ℝ) ≤ sourceNativeR6CofinalRoot434 N := by
    unfold sourceNativeR6CofinalRoot434
    have h : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : 1 < L := by
    have hh : (1:ℝ)<sourceNativeR6CofinalRoot434 N := by linarith
    unfold L sourceNativeR6CofinalL434
    exact one_lt_pow₀ hh (by norm_num : (10:ℕ)≠0)
  have hPartition := source_native_original_group_partition434 6 L
  have hDisjoint := source_native_original_group_partition_disjoint434 6 L hL
  change Fintype.card (sourceOriginalPAllGroupType 6 L) = 2*N+1
  rw [show Fintype.card (sourceOriginalPAllGroupType 6 L) =
    (sourceOriginalPAllGroupIndices 6 L).card from Fintype.card_coe _]
  rw [←hPartition,Finset.card_union_of_disjoint hDisjoint]
  have hSmall := source_native_r6_cofinal_small_card434 N
  have hBig := source_native_r6_cofinal_big_card434 N
  change _ + _ = 2*N+1
  rw [hSmall,hBig]
  omega
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalFinBridge -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The exact ORIGINAL r=6 cofinal SMALL family is never empty:
it contains the real distinguished S and N further original Ts
groups, at the original geometric scale L_N. -/
theorem source_native_r6_cofinal_SMALL_nonempty434 (N : ℕ) :
    (sourceNativeOriginalSmallIndices434 6
      (sourceNativeR6CofinalL434 N)).Nonempty := by
  apply Finset.card_pos.mp
  rw [source_native_r6_cofinal_small_card434]
  omega

/-- EXACT original remaining SMALL Ts group count N after
removing the MINIMUM true source S index. No new source group
or artificial equal-cardinality assumption. -/
theorem source_native_r6_cofinal_Ts_card434
    (N : ℕ) :
    Fintype.card (sourceNativeOriginalTsType434 6
      (sourceNativeR6CofinalL434 N)
      (source_native_r6_cofinal_SMALL_nonempty434 N)) = N := by
  let L := sourceNativeR6CofinalL434 N
  let hS := source_native_r6_cofinal_SMALL_nonempty434 N
  simp only [sourceNativeOriginalTsType434,Fintype.card_coe]
  change ((sourceNativeOriginalSmallIndices434 6 L).erase
    (sourceNativeOriginalSIndex434 6 L hS)).card = N
  rw [Finset.card_erase_of_mem
    (source_native_original_s_index_min434 6 L hS).1]
  have hc := source_native_r6_cofinal_small_card434 N
  change (sourceNativeOriginalSmallIndices434 6 L).card=N+1 at hc
  rw [hc]
  omega

/-- Canonical SOURCE03 Fin N Ts index is EXACTLY equivalent to the
original FULL r=6 SMALL-minus-distinguished-S source group type. -/
noncomputable def source_native_r6_cofinal_Ts_Fin_equiv434
    (N : ℕ) : Fin N ≃
      sourceNativeOriginalTsType434 6
        (sourceNativeR6CofinalL434 N)
        (source_native_r6_cofinal_SMALL_nonempty434 N) :=
  (Fintype.equivFinOfCardEq
    (source_native_r6_cofinal_Ts_card434 N)).symm

/-- Canonical SOURCE03 Fin N BIG index is EXACTLY equivalent to
the entire original native r=6 BIG Tb group family at L_N. -/
noncomputable def source_native_r6_cofinal_Tb_Fin_equiv434
    (N : ℕ) : Fin N ≃
      sourceNativeOriginalBigType434 6
        (sourceNativeR6CofinalL434 N) :=
  (Fintype.equivFinOfCardEq
    (show Fintype.card (sourceNativeOriginalBigType434 6
      (sourceNativeR6CofinalL434 N))=N by
      simpa only [sourceNativeOriginalBigType434,Fintype.card_coe] using
        source_native_r6_cofinal_big_card434 N)).symm

/-- Exact N+1 source SMALL+N source BIG vs canonical
Option(Fin N)+Fin N source group carrier. Independent source
S/Ts/Tb groups, original distinguished minimum S, full disjoint
P-band union and all physical BIG prime labels are retained. -/
noncomputable def source_native_r6_cofinal_canonical_full_equiv434
    (N : ℕ) :
      Option (Fin N) ⊕ Fin N ≃
        sourceOriginalPAllGroupType 6 (sourceNativeR6CofinalL434 N) := by
  let L := sourceNativeR6CofinalL434 N
  have hS := source_native_r6_cofinal_SMALL_nonempty434 N
  have hL : 1 < L := by
    have hu : (1:ℝ)<sourceNativeR6CofinalRoot434 N := by
      unfold sourceNativeR6CofinalRoot434
      have hh : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
      nlinarith
    unfold L sourceNativeR6CofinalL434
    exact one_lt_pow₀ hu (by norm_num : (10:ℕ)≠0)
  let eSmall : Option (Fin N) ≃
      Option (sourceNativeOriginalTsType434 6 L hS) :=
    Equiv.optionCongr (source_native_r6_cofinal_Ts_Fin_equiv434 N)
  let eBig : Fin N ≃ sourceNativeOriginalBigType434 6 L :=
    source_native_r6_cofinal_Tb_Fin_equiv434 N
  exact (Equiv.sumCongr eSmall eBig).trans
    (sourceNativeOriginalFullEquiv434 6 L hS hL)

/-- Source original canonical n=N group cardinal constraints:
N <= C0 log L_N with real SOURCE03 C0=4, and
N+1 <= 4N when N>=1. The first is proved from the TRUE
cofinal geometric scale and elementary log 2 >= 1/2,
not a guessed abstract group count. -/
theorem source_native_r6_cofinal_n_log_budget434 (N : ℕ) :
    (N:ℝ) ≤ 4*Real.log (sourceNativeR6CofinalL434 N) := by
  let u := sourceNativeR6CofinalRoot434 N
  let L := sourceNativeR6CofinalL434 N
  have hu : (2:ℝ)^N ≤ u := by
    unfold u sourceNativeR6CofinalRoot434
    have hh : 0 ≤ (2:ℝ)^N := pow_nonneg (by norm_num) _
    nlinarith
  have hP : ((2:ℝ)^N)^10 ≤ L := by
    unfold L sourceNativeR6CofinalL434
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^N) hu _
  have hLog : Real.log (((2:ℝ)^N)^10) ≤ Real.log L :=
    Real.log_le_log (by positivity) hP
  have hLog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos
      (by norm_num : (0:ℝ)<(1/2:ℝ))
    have hExpr : Real.log (1/2:ℝ) = -Real.log 2 := by
      rw [show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,Real.log_inv]
    rw [hExpr] at hh
    linarith
  have hLogPow : Real.log (((2:ℝ)^N)^10) =
      (10:ℝ)*(N:ℝ)*Real.log 2 := by
    rw [Real.log_pow,Real.log_pow]
    ring
  rw [hLogPow] at hLog
  have hlogN := mul_le_mul_of_nonneg_left hLog2
    (Nat.cast_nonneg N)
  nlinarith [hLog,hlogN]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalPrimeFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Original r=6 full SOURCE03 canonical P family at the
actual geometric cofinal L_N with EXACTLY N true Ts groups,
the distinguished native S and N independent BIG Tb groups.
The equivalence is constructed from the checked original
SMALL and BIG index counts; no prime band is inserted or dropped. -/
noncomputable def source_native_r6_canonical_P434
    (N : ℕ) (g : Option (Fin N)) : Finset ℕ :=
  let L := sourceNativeR6CofinalL434 N
  let e := source_native_r6_cofinal_canonical_full_equiv434 N
  sourceOriginalPAllActualBands 6 L (e (Sum.inl g))

noncomputable def source_native_r6_canonical_Tb434
    (N : ℕ) (i : Fin N) : Finset ℕ :=
  let L := sourceNativeR6CofinalL434 N
  let e := source_native_r6_cofinal_canonical_full_equiv434 N
  sourceOriginalPAllActualBands 6 L (e (Sum.inr i))

theorem source_native_r6_canonical_P_none_real_S434 (N : ℕ) :
    source_native_r6_canonical_P434 N none =
      sourceNativeOriginalS434 6 (sourceNativeR6CofinalL434 N)
        (source_native_r6_cofinal_SMALL_nonempty434 N) := by
  rfl

theorem source_native_r6_canonical_P_some_real_Ts434
    (N : ℕ) (i : Fin N) :
    source_native_r6_canonical_P434 N (some i) =
      sourceNativeOriginalTs434 6 (sourceNativeR6CofinalL434 N)
        (source_native_r6_cofinal_SMALL_nonempty434 N)
        (source_native_r6_cofinal_Ts_Fin_equiv434 N i) := by
  rfl

theorem source_native_r6_canonical_Tb_real_Tb434
    (N : ℕ) (i : Fin N) :
    source_native_r6_canonical_Tb434 N i =
      sourceNativeOriginalTb434 6 (sourceNativeR6CofinalL434 N)
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i) := by
  rfl

/-- All canonical source P-groups are EXACT reindexings of
the actual original source P bands, and their true union is
the complete native r=6 G prime family. -/
theorem source_native_r6_canonical_prime_union_eq_G434
    (N : ℕ) :
    source_native_r6_canonical_P434 N none ∪
      (Finset.univ : Finset (Fin N)).biUnion
        (fun i => source_native_r6_canonical_P434 N (some i)) ∪
      (Finset.univ : Finset (Fin N)).biUnion
        (source_native_r6_canonical_Tb434 N) =
    sourceNativeOriginalG434 6 (sourceNativeR6CofinalL434 N) := by
  classical
  let e := source_native_r6_cofinal_canonical_full_equiv434 N
  have hEq := source_native_original_union_reindex434
    e (sourceOriginalPAllActualBands 6 (sourceNativeR6CofinalL434 N))
  unfold sourceNativeOriginalG434
  rw [←hEq]
  ext p
  simp only [Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · intro h
    rcases h with hSmall | hBig
    · rcases hSmall with hS | ⟨i,hi⟩
      · refine ⟨Sum.inl none, ?_⟩
        change p ∈ source_native_r6_canonical_P434 N none
        exact hS
      · refine ⟨Sum.inl (some i), ?_⟩
        change p ∈ source_native_r6_canonical_P434 N (some i)
        exact hi
    · obtain ⟨i,hi⟩ := hBig
      refine ⟨Sum.inr i, ?_⟩
      change p ∈ source_native_r6_canonical_Tb434 N i
      exact hi
  · rintro ⟨g,hg⟩
    cases g with
    | inl oi =>
      cases oi with
      | none =>
        apply Or.inl
        apply Or.inl
        change p ∈ source_native_r6_canonical_P434 N none
        exact hg
      | some i =>
        apply Or.inl
        apply Or.inr
        refine ⟨i, ?_⟩
        change p ∈ source_native_r6_canonical_P434 N (some i)
        exact hg
    | inr i =>
      apply Or.inr
      refine ⟨i, ?_⟩
      change p ∈ source_native_r6_canonical_Tb434 N i
      exact hg
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CofinalTendsto -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Original r=6 cofinal geometric scales
L_N=((3/2)*2^N)^10 are UNBOUNDED, in the exact real
asymptotic atTop sense. Combined with the checked source
SMALL/BIG counts this gives infinitely many original
scales with exact 2N+1 full-P groups. -/
theorem source_native_r6_cofinal_L_tendsto_atTop434 :
    Tendsto sourceNativeR6CofinalL434 atTop atTop := by
  have htwo :
      Tendsto (fun N : ℕ => (2:ℝ)^N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hdom (N : ℕ) :
      (2:ℝ)^N ≤ sourceNativeR6CofinalL434 N := by
    let u := sourceNativeR6CofinalRoot434 N
    have hPow : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hu : (2:ℝ)^N ≤ u := by
      dsimp [u,sourceNativeR6CofinalRoot434]
      nlinarith
    have hu1 : 1 ≤ u := hPow.trans hu
    have hten : u ≤ u^10 := by
      have hh := pow_le_pow_right₀ hu1
        (by norm_num : (1:ℕ) ≤ 10)
      simpa only [pow_one] using hh
    exact hu.trans hten
  exact Filter.tendsto_atTop_mono hdom htwo

/-- This is the ORIGINAL r=6 P-slice total parity on a TRUE
unbounded sequence of scales, not a numerical experiment:
the full native S/Ts/Tb group type has 2N+1 (ODD) groups. -/
theorem source_native_r6_cofinal_ALL_P_odd434 (N : ℕ) :
    Odd (Fintype.card (SourceNativeOriginalAllP434 6
      (sourceNativeR6CofinalL434 N))) := by
  rw [source_native_r6_cofinal_ALL_P_card434]
  exact ⟨N,by omega⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeRAWJRatioFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Literal source R_g: the set of J independently drawn BIG source primes.
The ORIGINAL sampling still permits repeated draws; the set is used only
for the overlap counts c_g=|R_g ∩ A_g|, d_g=|R_g ∩ B_g|. -/
noncomputable def sourceOriginalJDrawSet434
    {G : Type} [Fintype G] (J : ℕ)
    (s : G × Fin J → ℕ) (g : G) : Finset ℕ :=
  Finset.univ.image (fun j : Fin J => s (g,j))

/-- This is the exact real coefficient from raw stripping (6.1):
2^(c+d) ((a-c)/a) ((b-d)/b), with a=|A_g| and b=|B_g|.
If either endpoint has no original free mark, the physical pairing is
defined to be zero; such zero endpoints are excluded here by a>0,b>0. -/
noncomputable def sourceOriginalJRawGroupFactor434
    (A B R : Finset ℕ) : ℝ :=
  (2:ℝ)^((R ∩ A).card+(R ∩ B).card) *
    (((A.card-(R ∩ A).card:ℕ):ℝ)/(A.card:ℝ)) *
    (((B.card-(R ∩ B).card:ℕ):ℝ)/(B.card:ℝ))

/-- The actual repeated-draw group factor has value one on disjoint
source histories, and is never larger than 2^(2J). -/
theorem source_original_J_raw_group_factor_bounds434
    (J : ℕ) (A B R : Finset ℕ)
    (hA : 0 < A.card) (hB : 0 < B.card)
    (hR : R.card ≤ J) :
    0 ≤ sourceOriginalJRawGroupFactor434 A B R ∧
    sourceOriginalJRawGroupFactor434 A B R ≤ (2:ℝ)^(2*J) := by
  let c := (R ∩ A).card
  let d := (R ∩ B).card
  have hc : c ≤ J := (Finset.card_le_card (Finset.inter_subset_left)).trans hR
  have hd : d ≤ J := (Finset.card_le_card (Finset.inter_subset_left)).trans hR
  have hCA : c ≤ A.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hDB : d ≤ B.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have ha : (0:ℝ) < (A.card:ℝ) := Nat.cast_pos.mpr hA
  have hb : (0:ℝ) < (B.card:ℝ) := Nat.cast_pos.mpr hB
  have hfracA :
      0 ≤ (((A.card-c:ℕ):ℝ)/(A.card:ℝ)) ∧
      (((A.card-c:ℕ):ℝ)/(A.card:ℝ)) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one ha).mpr (by exact_mod_cast Nat.sub_le A.card c)
  have hfracB :
      0 ≤ (((B.card-d:ℕ):ℝ)/(B.card:ℝ)) ∧
      (((B.card-d:ℕ):ℝ)/(B.card:ℝ)) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hb).mpr (by exact_mod_cast Nat.sub_le B.card d)
  have hpower : (2:ℝ)^(c+d) ≤ (2:ℝ)^(2*J) :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  dsimp [sourceOriginalJRawGroupFactor434]
  constructor
  · positivity
  · calc
      _ ≤ (2:ℝ)^(c+d) * 1 * 1 := by
        gcongr
        · exact hfracA.2
        · exact hfracB.2
      _ = (2:ℝ)^(c+d) := by ring
      _ ≤ (2:ℝ)^(2*J) := hpower

theorem source_original_J_raw_group_factor_eq_one434
    (A B R : Finset ℕ)
    (hA : 0 < A.card) (hB : 0 < B.card)
    (hdA : Disjoint R A) (hdB : Disjoint R B) :
    sourceOriginalJRawGroupFactor434 A B R = 1 := by
  have ha : (A.card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hb : (B.card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hB)
  unfold sourceOriginalJRawGroupFactor434
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdA,
    Finset.disjoint_iff_inter_eq_empty.mp hdB]
  simp only [Finset.card_empty, Nat.zero_add, pow_zero, Nat.sub_zero,
    one_mul, mul_one, div_self ha, div_self hb]
end Green64ComparisonPartial

end

end

/-! ## SourceNativeRAWJRatioWeight -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Exact original R_J integrand: globally distinct J-per-group draws
(and thus no repeated BIG primes), with 2^(c_g+d_g) and both free-mark
factors for each group. Original P bands are disjoint, so global
distinctness and groupwise distinctness coincide ON SOURCE SUPPORT. -/
noncomputable def sourceOriginalJRawWeight434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (A B : G → Finset ℕ)
    (s : G × Fin J → ℕ) : ℝ :=
  if Function.Injective s then
    ∏ g : G, sourceOriginalJRawGroupFactor434 (A g) (B g)
      (sourceOriginalJDrawSet434 J s g)
  else 0

/-- Every original positive free-mark group gives nonnegative physical
ratio, and the exact two endpoint boosts cost at most 2^(2J|G|). -/
theorem source_original_J_raw_weight_bounds434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (A B : G → Finset ℕ)
    (ha : ∀ g, 0 < (A g).card)
    (hb : ∀ g, 0 < (B g).card)
    (s : G × Fin J → ℕ) :
    0 ≤ sourceOriginalJRawWeight434 J A B s ∧
      sourceOriginalJRawWeight434 J A B s ≤
      (2:ℝ)^(2*J*Fintype.card G) := by
  classical
  have hgroup : ∀ g : G,
      0 ≤ sourceOriginalJRawGroupFactor434
        (A g) (B g) (sourceOriginalJDrawSet434 J s g) ∧
      sourceOriginalJRawGroupFactor434
        (A g) (B g) (sourceOriginalJDrawSet434 J s g) ≤
          (2:ℝ)^(2*J) := by
    intro g
    apply source_original_J_raw_group_factor_bounds434 J
      (A g) (B g) _ (ha g) (hb g)
    unfold sourceOriginalJDrawSet434
    simpa using (Finset.card_image_le
      (s := (Finset.univ : Finset (Fin J)))
      (f := fun j => s (g,j))).trans_eq (by simp)
  have hprodnonneg : 0 ≤ ∏ g : G,
        sourceOriginalJRawGroupFactor434 (A g) (B g)
          (sourceOriginalJDrawSet434 J s g) :=
    Finset.prod_nonneg (fun g _ => (hgroup g).1)
  have hprod :
      (∏ g : G, sourceOriginalJRawGroupFactor434 (A g) (B g)
        (sourceOriginalJDrawSet434 J s g)) ≤
      (2:ℝ)^(2*J*Fintype.card G) := by
    calc
      _ ≤ ∏ _g : G, (2:ℝ)^(2*J) :=
        Finset.prod_le_prod₀ (fun g _ => (hgroup g).1)
          (fun g _ => (hgroup g).2)
      _ = (2:ℝ)^(2*J*Fintype.card G) := by
        simp only [Finset.prod_const, Finset.card_univ, nsmul_eq_mul]
        rw [←pow_mul]
  unfold sourceOriginalJRawWeight434
  split_ifs
  · exact ⟨hprodnonneg, hprod⟩
  · exact ⟨le_refl _, (pow_nonneg (by norm_num) _ )⟩

/-- Under the original unrestricted harmonic law, a clean J-array
has no collisions and avoids all endpoint primes. The exact R_J
multiplicity/free-mark factor is therefore literally ONE. -/
theorem source_original_J_raw_weight_clean_eq_one434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (A B : G → Finset ℕ)
    (ha : ∀ g, 0 < (A g).card)
    (hb : ∀ g, 0 < (B g).card)
    (F : Finset ℕ)
    (hA : ∀ g, A g ⊆ F) (hB : ∀ g, B g ⊆ F)
    (s : G × Fin J → ℕ)
    (hclean : sourceSharedClean434 (fun _ => F) s) :
    sourceOriginalJRawWeight434 J A B s = 1 := by
  classical
  unfold sourceOriginalJRawWeight434
  rw [if_pos hclean.1]
  apply Finset.prod_eq_one
  intro g hg
  apply source_original_J_raw_group_factor_eq_one434
      (A g) (B g) _ (ha g) (hb g)
  · apply Finset.disjoint_left.mpr
    intro p hpR hpA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpR
    exact (hclean.2 (g,j)) (hA g hpA)
  · apply Finset.disjoint_left.mpr
    intro p hpR hpB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpR
    exact (hclean.2 (g,j)) (hB g hpB)
end Green64ComparisonPartial

end

end

/-! ## SourceNativeRAWJRatioExpectation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Elementary but EXACT probability-to-R_J correction lemma:
the full unconditioned product probability remains one, and the
only loss occurs on a bad label array. On the clean event, the source
factor W is 1; on the bad event, 0≤W≤C. The source signed K is not
replaced by 1 here, since this treats just the scalar normalizing R_J. -/
theorem original_J_RAW_ratio_deviation_of_clean_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i, mu i p = 1)
    (hMu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (good : (ι → ℕ) → Prop)
    (W : (ι → ℕ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hOne : ∀ s ∈ Fintype.piFinset S,
      good s → W s = 1)
    (hW : ∀ s ∈ Fintype.piFinset S,
      0 ≤ W s ∧ W s ≤ C) :
    |(∑ s ∈ Fintype.piFinset S,
        sourceSharedLaw434 mu s * W s) - 1| ≤
      (1+C)*(∑ s ∈ Fintype.piFinset S,
        if good s then 0 else sourceSharedLaw434 mu s) := by
  classical
  let T := Fintype.piFinset S
  let mass := sourceSharedLaw434 mu
  have hm : ∀ s ∈ T, 0 ≤ mass s :=
    source_shared_law_nonneg434 S mu hMu
  have hTotal : (∑ s ∈ T, mass s) = 1 :=
    source_shared_law_total434 S mu hMass
  have hDiff : (∑ s ∈ T, mass s*W s)-1 =
      ∑ s ∈ T, if good s then 0 else mass s*(W s-1) := by
    calc
      _ = ∑ s ∈ T, (mass s*W s - mass s) := by
        rw [Finset.sum_sub_distrib,hTotal]
      _ = ∑ s ∈ T, if good s then 0 else mass s*(W s-1) := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases h : good s
        · simp [h, hOne s hs h]
        · simp [h]
          ring
  rw [hDiff]
  calc
    |∑ s ∈ T, if good s then 0 else mass s*(W s-1)| ≤
        ∑ s ∈ T, |if good s then 0 else mass s*(W s-1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ T, if good s then 0 else (1+C)*mass s := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases h : good s
      · simp [h]
      · simp only [if_neg h,abs_mul,abs_of_nonneg (hm s hs)]
        have hw := hW s hs
        have hErr : |W s - 1| ≤ 1+C :=
          abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hErr (hm s hs)
    _ = (1+C)*∑ s ∈ T, if good s then 0 else mass s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : good s <;> simp [h]
end Green64ComparisonPartial

end

end

/-! ## SourceNativeRAWJRatioNative -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64ComparisonPartial
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The FULL original harmonic BIG J-array expectation of the literal
R_J scalar weight from source (6.1), with actual Q/P source parameters.
The A/B sets contain original free BIG marks dividing the two endpoints.
This is the ratio on the legal nonzero mark-count sector only; sectors
with a_g=0 or b_g=0 contribute zero to W1(w)W1(w') R_J by definition. -/
noncomputable def sourceNativeOriginalRAWJRatio434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (A B : sourceNativeOriginalBigType434 r L → Finset ℕ) : ℝ :=
  ∑ s ∈ Fintype.piFinset
    (fun i : sourceNativeOriginalBigType434 r L × Fin J =>
      sourceNativeOriginalTb434 r L i.1),
    sourceSharedLaw434
      (fun i p => sourcePrimeSharedAtom434
        (sourceNativeOriginalVbig434 r L i.1) p) s *
      sourceOriginalJRawWeight434 J A B s

/-- Exact algebraic RAW compensation, with true independently normalized
source BIG law, true repeated J draws and the complete excluded set of
both endpoints and B26 auxiliary prime values. No assumed R_J≈1. -/
theorem source_native_original_RAW_J_ratio_loss_of_bad434
    (r : ℕ) (L : ℝ) (J m : ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (A B : sourceNativeOriginalBigType434 r L → Finset ℕ)
    (hA : ∀ g, 0 < (A g).card) (hB : ∀ g, 0 < (B g).card)
    (hAend : ∀ g, A g ⊆ w.primeFactors)
    (hBend : ∀ g, B g ⊆ wp.primeFactors)
    (hMass : ∀ g, 0 < sourceNativeOriginalVbig434 r L g) :
    |sourceNativeOriginalRAWJRatio434 r L J A B - 1| ≤
      (1+(2:ℝ)^(2*J*Fintype.card (sourceNativeOriginalBigType434 r L))) *
      (∑ s ∈ Fintype.piFinset
        (fun i : sourceNativeOriginalBigType434 r L × Fin J =>
          sourceNativeOriginalTb434 r L i.1),
        if sourceSharedClean434
          (fun _ => sourceSharedForbidden434 w wp
            (sourceNativeOriginalAuxValueSet434 r L J m pat aux)) s
        then 0
        else sourceSharedLaw434
          (fun i p => sourcePrimeSharedAtom434
            (sourceNativeOriginalVbig434 r L i.1) p) s) := by
  classical
  let G := sourceNativeOriginalBigType434 r L
  let S : G × Fin J → Finset ℕ :=
    fun i => sourceNativeOriginalTb434 r L i.1
  let mu : G × Fin J → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalVbig434 r L i.1) p
  let F := sourceSharedForbidden434 w wp
    (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
  let good : (G × Fin J → ℕ) → Prop := sourceSharedClean434 (fun _ => F)
  let W := sourceOriginalJRawWeight434 J A B
  have hM : ∀ i, ∑ p ∈ S i, mu i p = 1 := by
    intro i
    apply source_prime_shared_atom_total434
    · simp [S, sourceNativeOriginalVbig434, one_div]
    · exact (hMass i.1).ne'
  have hMU : ∀ i p, p ∈ S i → 0 ≤ mu i p := by
    intro i p hp
    have hpPrime := (source_native_original_Tb_prime_range434
      r L i.1 p hp).1
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpPrime.pos
    have hV0 : 0 < sourceNativeOriginalVbig434 r L i.1 := hMass i.1
    dsimp [mu,sourcePrimeSharedAtom434]
    positivity
  have hAsub : ∀ g, A g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (hAend g hp))
  have hBsub : ∀ g, B g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (hBend g hp))
  have hOne : ∀ s ∈ Fintype.piFinset S, good s → W s = 1 := by
    intro s hs hg
    exact source_original_J_raw_weight_clean_eq_one434 J A B hA hB
      F hAsub hBsub s hg
  have hW : ∀ s ∈ Fintype.piFinset S,
      0 ≤ W s ∧ W s ≤ (2:ℝ)^(2*J*Fintype.card G) := by
    intro s hs
    exact source_original_J_raw_weight_bounds434 J A B hA hB s
  exact original_J_RAW_ratio_deviation_of_clean_mass434
    S mu hM hMU good W _
    (pow_nonneg (by norm_num) _) hOne hW
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeRAWJBadMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- The true unconditioned independent REAL harmonic bad mass equals
the norm of its complex embedding (K=1). This is the precise scalar
bridge from a full complex source dirty-envelope theorem, not a
postulated equality between raw physical and comparison roots. -/
theorem original_RAW_bad_mass_complex_norm434
    {ι : Type} (T : Finset ι) (mu : ι → ℝ)
    (good : ι → Prop)
    (hmu : ∀ i ∈ T, 0 ≤ mu i) :
    (∑ i ∈ T, if good i then (0:ℝ) else mu i) =
    ‖∑ i ∈ T, if good i then (0:ℂ) else (mu i : ℂ)*(1:ℂ)‖ := by
  classical
  let bad : ℝ := ∑ i ∈ T, if good i then (0:ℝ) else mu i
  have hnonneg : 0 ≤ bad := by
    dsimp [bad]
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : good i
    · simp [h]
    · simpa [h] using hmu i hi
  have hcast : (∑ i ∈ T, if good i then (0:ℂ)
        else (mu i:ℂ)*(1:ℂ)) = (bad:ℂ) := by
    calc
      _ = ∑ i ∈ T, ((if good i then (0:ℝ) else mu i):ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : good i <;> simp [h]
      _ = (bad:ℂ) := by
        dsimp [bad]
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : good i <;> simp [h]
  change bad = ‖∑ i ∈ T, if good i then (0:ℂ) else (mu i:ℂ)*(1:ℂ)‖
  rw [hcast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
end Green64ComparisonPartial

end

end

/-! ## SourceNativeOriginalAllPJRatio -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Correct FULL SOURCE scalar R_J(w,w'): full J-fold harmonic draws in
every original P group (distinguished S, remaining Ts and all Tb),
allowing repeated primes before imposing the source distinctness
indicator. BIG-only R_J is not the physical RAW scalar. -/
noncomputable def sourceNativeOriginalALLPJRatio434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (A B : SourceNativeOriginalAllP434 r L → Finset ℕ) : ℝ :=
  ∑ s ∈ Fintype.piFinset
    (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1),
    sourceSharedLaw434
      (fun i p => sourcePrimeSharedAtom434
        (sourceNativeOriginalAllPMass434 r L i.1) p) s *
      sourceOriginalJRawWeight434 J A B s

/-- Full-P fixed-L exact source RAW scalar ratio error <=
(1+2^(2J|P|)) times the probability of bad common RAW J histories.
The complete ordinary endpoints and independently chosen BIG auxiliary
prime set are included in the bad predicate. -/
theorem source_native_original_ALL_P_RAW_J_ratio_loss_of_bad434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L) (J m : ℕ)
    (pat : Green64FullPhysicalE.SourcePattern
      (sourceNativeOriginalBigType434 r L) J m)
    (aux : Green64FullPhysicalE.SourceBigAux
      (SourceNativeMemoryBP434 r L) J m pat)
    (w wp : ℕ) (A B : SourceNativeOriginalAllP434 r L → Finset ℕ)
    (hA : ∀ g, 0 < (A g).card)
    (hB : ∀ g, 0 < (B g).card)
    (hAend : ∀ g, A g ⊆ w.primeFactors)
    (hBend : ∀ g, B g ⊆ wp.primeFactors)
    (hMass : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g) :
    |sourceNativeOriginalALLPJRatio434 r L J A B - 1| ≤
      (1+(2:ℝ)^(2*J*Fintype.card (SourceNativeOriginalAllP434 r L))) *
      (∑ s ∈ Fintype.piFinset
        (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
          SourceNativeOriginalAllPBand434 r L i.1),
        if sourceSharedClean434
          (fun _ => sourceSharedForbidden434 w wp
            (sourceNativeOriginalAuxValueSet434 r L J m pat aux)) s
        then 0
        else sourceSharedLaw434
          (fun i p => sourcePrimeSharedAtom434
            (sourceNativeOriginalAllPMass434 r L i.1) p) s) := by
  classical
  let G := SourceNativeOriginalAllP434 r L
  let S : G × Fin J → Finset ℕ :=
    fun i => SourceNativeOriginalAllPBand434 r L i.1
  let mu : G × Fin J → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p
  let F := sourceSharedForbidden434 w wp
    (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
  let good : (G × Fin J → ℕ) → Prop :=
    sourceSharedClean434 (fun _ => F)
  let W := sourceOriginalJRawWeight434 J A B
  have hM : ∀ i, ∑ p ∈ S i, mu i p = 1 := by
    intro i
    apply source_prime_shared_atom_total434
    · simp [S, sourceNativeOriginalAllPMass434, one_div]
    · exact (hMass i.1).ne'
  have hMU : ∀ i p, p ∈ S i → 0 ≤ mu i p := by
    intro i p hp
    have hpPrime := (source_native_original_ALL_P_prime_range434
      r L hL i.1 p hp).1
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpPrime.pos
    have hV0 : 0 < sourceNativeOriginalAllPMass434 r L i.1 :=
      hMass i.1
    dsimp [mu,sourcePrimeSharedAtom434]
    positivity
  have hAsub : ∀ g, A g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (hAend g hp))
  have hBsub : ∀ g, B g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (hBend g hp))
  have hOne : ∀ s ∈ Fintype.piFinset S, good s → W s = 1 := by
    intro s hs hg
    exact source_original_J_raw_weight_clean_eq_one434 J A B hA hB
      F hAsub hBsub s hg
  have hW : ∀ s ∈ Fintype.piFinset S,
      0 ≤ W s ∧ W s ≤ (2:ℝ)^(2*J*Fintype.card G) := by
    intro s hs
    exact source_original_J_raw_weight_bounds434 J A B hA hB s
  exact original_J_RAW_ratio_deviation_of_clean_mass434
    S mu hM hMU good W _
    (pow_nonneg (by norm_num) _) hOne hW
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalAllPJRatioSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The COMPLETE original common RAW R_J, summed over all S/Ts/Tb
source prime groups with the literal J-fold independent harmonic law
and group mark indicators, enjoys any fixed log saving:

  |R_J^allP(w,w')-1| ≤ L^-D.

All original dependent free BIG auxiliary labels are allowed to repeat
and are retained in the forbidden set. In every original P group the
true free endpoint counts a_g,b_g are positive and are subsets of
the two actual ordinary endpoint prime-divisor sets. The original
large-scale source cutoff w,w'≤exp(2L) is preserved.

The threshold is BEFORE all moving J,m≤tmax, all auxiliary draws and
all nonzero endpoint pairs. No standalone RAW/physical comparison
identity is claimed. -/
theorem eventually_native_original_ALL_P_RAW_J_ratio_log_saving434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : Green64FullPhysicalE.SourcePattern
          (sourceNativeOriginalBigType434 r L) J m)
        (aux : Green64FullPhysicalE.SourceBigAux
          (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) → (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      |sourceNativeOriginalALLPJRatio434 r L J A B - 1| ≤ L^(-D) := by
  classical
  let Cgroup : ℝ := 3+(Real.log 2)⁻¹
  let E : ℝ := 1+2*(tmax:ℝ)*Cgroup*Real.log 2
  have hCG : 0 ≤ Cgroup := by
    dsimp [Cgroup]
    have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
    eventually_native_original_ALL_P_J_dirty_true_aux434
      r hr tmax (D+E),
    eventually_native_original_ALL_P_masses434 r,
    eventually_ge_atTop (Real.exp 1)]
    with L hDirty hMass hL
  refine ⟨hL, ?_⟩
  intro J m pat aux hJ hm w wp hw hwp hwCap hwpCap
    A B hA hB hAsub hBsub
  let G := SourceNativeOriginalAllP434 r L
  let S : G × Fin J → Finset ℕ :=
    fun i => SourceNativeOriginalAllPBand434 r L i.1
  let mu : G × Fin J → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p
  let F := sourceSharedForbidden434 w wp
    (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
  let good : (G × Fin J → ℕ) → Prop :=
    sourceSharedClean434 (fun _ => F)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : (1:ℝ) ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hL
  have hL2 : (2:ℝ) ≤ L := by
    have hExp : (2:ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1:ℝ)]
    exact hExp.trans hL
  have hCount : (Fintype.card G:ℝ) ≤ Cgroup * Real.log L := by
    simpa only [G,SourceNativeOriginalAllP434,
      sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hBoost : 1+(2:ℝ)^(2*J*Fintype.card G) ≤ L^E :=
    original_RAW_J_boost_polynomial434
      L Cgroup J tmax _ hL2 hCG hJ hCount
  have hvPos : ∀ g : G, 0 < sourceNativeOriginalAllPMass434 r L g := by
    intro g
    exact ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive.trans_le
      (hMass g).1
  have hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p := by
    intro i p hp
    have hpPrime := (source_native_original_ALL_P_prime_range434
      r L hL1 i.1 p hp).1
    have hpPos : (0:ℝ) < p := by exact_mod_cast hpPrime.pos
    have hv := hvPos i.1
    dsimp [mu,sourcePrimeSharedAtom434]
    positivity
  have hLaw : ∀ s ∈ Fintype.piFinset S,
      0 ≤ sourceSharedLaw434 mu s :=
    source_shared_law_nonneg434 S mu hmu
  have hBase := source_native_original_ALL_P_RAW_J_ratio_loss_of_bad434
    r L hL1 J m pat aux w wp A B
    hA hB hAsub hBsub hvPos
  have hDirtyReal := hDirty.2 J m pat aux hJ hm w wp
    (fun _ => (1:ℂ)) (1:ℝ) (by norm_num)
    hw hwp hwCap hwpCap (by intro s hs; simp)
  have hBad := original_RAW_bad_mass_complex_norm434
    (Fintype.piFinset S) (sourceSharedLaw434 mu) good hLaw
  have hLost :
      (∑ s ∈ Fintype.piFinset S,
        if good s then 0 else sourceSharedLaw434 mu s) ≤
          L^(-(D+E)) := by
    calc
      _ = ‖∑ s ∈ Fintype.piFinset S,
            if good s then (0:ℂ)
            else ((sourceSharedLaw434 mu s:ℝ):ℂ)*(1:ℂ)‖ := hBad
      _ ≤ (1:ℝ)*L^(-(D+E)) := hDirtyReal
      _ = L^(-(D+E)) := by ring
  calc
    |sourceNativeOriginalALLPJRatio434 r L J A B-1| ≤
      (1+(2:ℝ)^(2*J*Fintype.card G)) *
        (∑ s ∈ Fintype.piFinset S,
          if good s then 0 else sourceSharedLaw434 mu s) := hBase
    _ ≤ (1+(2:ℝ)^(2*J*Fintype.card G))*L^(-(D+E)) :=
      mul_le_mul_of_nonneg_left hLost (by positivity)
    _ ≤ L^E * L^(-(D+E)) :=
      mul_le_mul_of_nonneg_right hBoost (Real.rpow_nonneg hLp.le _)
    _ = L^(-D) := by
      rw [←Real.rpow_add hLp]
      congr 1
      ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPPhaseWeightedRAW -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The TRUE signed RAW/Comparison correction is NOT \`R_J-1\`
without its physical pattern-dependent Ptw parity phase.
For ANY complex coherent phase depending on the complete original
J-array, bounded by one on the legal native all-P source support,
the correction
  sum_{hist} mu(hist) phase(hist) (R_J(hist)-1)
has arbitrary log-saving, with the REFERENCE
  sum_{hist} mu(hist) phase(hist).
It is NOT asserted that this signed reference equals 1.

All original S/Ts/Tb P groups, full J repeated draws, true BIG
auxiliary free labels, physical endpoint prime supports, and
original positive free-mark counts are quantified in the correct
source order. No prior assumption that physical Ptw equals full G. -/
theorem eventually_native_original_ALL_P_phase_weighted_RAW_saving434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ∀ (phase : (SourceNativeOriginalAllP434 r L × Fin J → ℕ) → ℂ),
      (∀ s ∈ Fintype.piFinset
        (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
          SourceNativeOriginalAllPBand434 r L i.1),
        ‖phase s‖ ≤ 1) →
      ‖∑ s ∈ Fintype.piFinset
        (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
          SourceNativeOriginalAllPBand434 r L i.1),
        (sourceSharedLaw434
          (fun i p => sourcePrimeSharedAtom434
            (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ) *
        phase s *
        (((sourceOriginalJRawWeight434 J A B s - 1:ℝ):ℂ))‖ ≤
      L^(-Dsave) := by
  classical
  let Cg : ℝ := 3+(Real.log 2)⁻¹
  let E : ℝ := 1+2*(tmax:ℝ)*Cg*Real.log 2
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
    eventually_native_original_ALL_P_J_dirty_true_aux434
      r hr tmax (Dsave+E),
    eventually_source_native_original_group_masses434 r hr,
    eventually_ge_atTop (Real.exp 1)]
    with L hDirty hGroups hL
  refine ⟨hL, ?_⟩
  intro J m pat aux hJ hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend phase hPhase
  let G := SourceNativeOriginalAllP434 r L
  let T : Finset (G × Fin J → ℕ) :=
    Fintype.piFinset (fun i : G × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1)
  let F := sourceSharedForbidden434 w wp
    (sourceNativeOriginalAuxValueSet434 r L J m pat aux)
  let good : (G × Fin J → ℕ) → Prop :=
    sourceSharedClean434 (fun _ => F)
  let W := sourceOriginalJRawWeight434 J A B
  let mu : (G × Fin J → ℕ) → ℝ := fun s =>
    sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s
  let Max : ℝ := (2:ℝ)^(2*J*Fintype.card G)
  let Kcorr : (G × Fin J → ℕ) → ℂ := fun s =>
    phase s * (((W s-1:ℝ):ℂ))
  have hNon : 0 ≤ Max := by dsimp [Max]; positivity
  have hW : ∀ s ∈ T, 0 ≤ W s ∧ W s ≤ Max := by
    intro s hs
    exact source_original_J_raw_weight_bounds434 J A B hA hB s
  have hPhaseBound : ∀ s ∈ T, ‖Kcorr s‖ ≤ 1+Max := by
    intro s hs
    have hw0 := (hW s hs).1
    have hw1 := (hW s hs).2
    have hAbs : |W s-1| ≤ 1+Max :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [Kcorr]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      ‖phase s‖*|W s-1| ≤ 1*|W s-1| :=
        mul_le_mul_of_nonneg_right (hPhase s hs) (abs_nonneg _)
      _ ≤ 1*(1+Max) :=
        mul_le_mul_of_nonneg_left hAbs (by norm_num)
      _ = 1+Max := by ring
  have hAsub : ∀ g, A g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (hAend g hp))
  have hBsub : ∀ g, B g ⊆ F := by
    intro g p hp
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (hBend g hp))
  have hClean : ∀ s ∈ T, good s → W s = 1 := by
    intro s hs hgood
    exact source_original_J_raw_weight_clean_eq_one434
      J A B hA hB F hAsub hBsub s hgood
  have hSumEq :
      (∑ s ∈ T, (mu s:ℂ)*phase s*(((W s-1:ℝ):ℂ))) =
      ∑ s ∈ T, if good s then (0:ℂ) else (mu s:ℂ)*Kcorr s := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hgood : good s
    · have hOne := hClean s hs hgood
      simp [hgood,Kcorr,hOne]
    · simp [hgood,Kcorr,mul_assoc]
  have hDirtyBound :
      ‖∑ s ∈ T, if good s then (0:ℂ)
          else (mu s:ℂ)*Kcorr s‖ ≤
      (1+Max)*L^(-(Dsave+E)) := by
    exact hDirty.2 J m pat aux hJ hm w wp
      Kcorr (1+Max) (by linarith) hw hwp hwCap hwpCap
      (by intro s hs; exact hPhaseBound s hs)
  obtain ⟨_,hSmall,_⟩ := hGroups
  have hCount : (Fintype.card G:ℝ) ≤ Cg*Real.log L := by
    simpa only [G,SourceNativeOriginalAllP434,
      sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL2 : (2:ℝ) ≤ L := by
    have hh : (2:ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1:ℝ)]
    exact hh.trans hL
  have hBoost : 1+Max ≤ L^E :=
    original_RAW_J_boost_polynomial434
      L Cg J tmax (Fintype.card G) hL2 hCg hJ hCount
  change ‖∑ s ∈ T, (mu s:ℂ)*phase s*(((W s-1:ℝ):ℂ))‖ ≤
    L^(-Dsave)
  rw [hSumEq]
  calc
    ‖∑ s ∈ T, if good s then (0:ℂ)
        else (mu s:ℂ)*Kcorr s‖ ≤
      (1+Max)*L^(-(Dsave+E)) := hDirtyBound
    _ ≤ L^E*L^(-(Dsave+E)) :=
      mul_le_mul_of_nonneg_right hBoost
        (Real.rpow_nonneg hLp.le _)
    _ = L^(-Dsave) := by
      rw [←Real.rpow_add hLp]
      congr 1
      ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalAllPDivisorCap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- FULL source common J labels in every original P group
(S, Ts, and Tb). The same product is used as raw shared physical
divisor D_R, before any repeated-draw distinctness gate. This
definition DOES NOT remove repeated prime values and uses no
independent comparison/free auxiliary group in place of SMALL. -/
noncomputable def sourceNativeOriginalAllPCommonDivisor434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (s : SourceNativeOriginalAllP434 r L × Fin J → ℕ) : ℕ :=
  ∏ i : SourceNativeOriginalAllP434 r L × Fin J, s i

/-- Literal original full-P J-fold common divisor is SUBEXPONENTIAL:
the number of groups is at most (3+1/log 2)log L, every selected P
prime is at most exp(L^0.4), and J is a FIXED source integer before L.
Thus D_R ≤ exp(J*(3+1/log 2)*L^0.4*log L).

No source band or interval is replaced, including the SMALL S/Ts.
Draws may repeat because only the product is being bounded. -/
theorem eventually_native_original_ALL_P_J_divisor_cap434
    (r : ℕ) (hr : 1 ≤ r) (J : ℕ) :
    let Cg : ℝ := 3+(Real.log 2)⁻¹
    let C : ℝ := (J:ℝ)*Cg
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (s : SourceNativeOriginalAllP434 r L × Fin J → ℕ),
        s ∈ Fintype.piFinset
          (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
            SourceNativeOriginalAllPBand434 r L i.1) →
        (sourceNativeOriginalAllPCommonDivisor434 r L J s:ℝ) ≤
          Real.exp (C*L^(2/5:ℝ)*Real.log L) := by
  classical
  let Cg : ℝ := 3+(Real.log 2)⁻¹
  let C : ℝ := (J:ℝ)*Cg
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
  refine ⟨hL, ?_⟩
  intro s hs
  let G := SourceNativeOriginalAllP434 r L
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hGc : (Fintype.card G:ℝ) ≤ Cg*Real.log L := by
    simpa only [G,SourceNativeOriginalAllP434,
      sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hPow : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hN : ((J*Fintype.card G:ℕ):ℝ) ≤ C*Real.log L := by
    have hh := mul_le_mul_of_nonneg_left hGc (Nat.cast_nonneg J)
    dsimp [C]
    push_cast
    nlinarith [hh]
  have hFactor :
      ∀ i : G × Fin J, (s i:ℝ) ≤
        Real.exp (L^(2/5:ℝ)) := by
    intro i
    have hp : s i ∈ SourceNativeOriginalAllPBand434 r L i.1 :=
      (Fintype.mem_piFinset.mp hs) i
    exact (source_native_original_ALL_P_prime_range434
      r L hL1 i.1 (s i) hp).2.2
  have hExp : 0 ≤ Real.exp (L^(2/5:ℝ)) :=
    (Real.exp_pos _).le
  have hProduct :
      (sourceNativeOriginalAllPCommonDivisor434 r L J s:ℝ) ≤
        (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card G) := by
    unfold sourceNativeOriginalAllPCommonDivisor434
    calc
      ((∏ i : G × Fin J, s i : ℕ):ℝ) =
        ∏ i : G × Fin J, (s i:ℝ) := by push_cast; rfl
      _ ≤ ∏ _i : G × Fin J, Real.exp (L^(2/5:ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Nat.cast_nonneg _
        · intro i hi
          exact hFactor i
      _ = (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card G) := by
        simp [mul_comm]
  have hExpCap :
      (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card G) ≤
        Real.exp (C*L^(2/5:ℝ)*Real.log L) := by
    calc
      _ = Real.exp (((J*Fintype.card G:ℕ):ℝ)*L^(2/5:ℝ)) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((C*Real.log L)*L^(2/5:ℝ)) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hN hPow)
      _ = Real.exp (C*L^(2/5:ℝ)*Real.log L) := by
        congr 1
        ring
  exact hProduct.trans hExpCap
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPSignedRAWReference -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Actual signed *COMMON J-history* phase on all original P groups,
including S/Ts/Tb, for arbitrary original Ptw and independent choices
of the source and target endpoint parity tests. Repeated values and
their full prime multiplicities contribute to the original
literalSourceParity. This may depend on the ENTIRE J-array and so
must not be pulled outside the source harmonic expectation. -/
noncomputable def sourceNativeOriginalALLPJHistoryPtwPhase434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (Ptw : Finset ℕ) (b1 b2 : Bool)
    (s : SourceNativeOriginalAllP434 r L × Fin J → ℕ) : ℂ :=
  (if b1 then literalSourceParity Ptw
     (sourceNativeOriginalAllPCommonDivisor434 r L J s) else 1) *
  (if b2 then literalSourceParity Ptw
     (sourceNativeOriginalAllPCommonDivisor434 r L J s) else 1)

theorem source_native_original_ALL_P_J_history_phase_unit434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (Ptw : Finset ℕ) (b1 b2 : Bool)
    (s : SourceNativeOriginalAllP434 r L × Fin J → ℕ) :
    ‖sourceNativeOriginalALLPJHistoryPtwPhase434
        r L J Ptw b1 b2 s‖ = 1 := by
  unfold sourceNativeOriginalALLPJHistoryPtwPhase434
  simpa [literalSourceParity] using
    source_shared_pattern_sign_norm434
      (∑ p ∈ Ptw,
        (sourceNativeOriginalAllPCommonDivisor434 r L J s).factorization p)
      b1 b2

/-- The correct finite signed full-P common-J RAW scalar:
sum mu(history)*phase_Ptw(history)*R_J(history).
No physical Ptw=G assumption and no prematurely dropped mixed signs. -/
noncomputable def sourceNativeOriginalALLPJHistorySignedRAW434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (Ptw : Finset ℕ) (b1 b2 : Bool)
    (A B : SourceNativeOriginalAllP434 r L → Finset ℕ) : ℂ :=
  ∑ s ∈ Fintype.piFinset
    (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1),
    (sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ) *
    sourceNativeOriginalALLPJHistoryPtwPhase434 r L J Ptw b1 b2 s *
    ((sourceOriginalJRawWeight434 J A B s:ℝ):ℂ)

/-- The correct signed comparator is the phase-weighted SAME source
unconditioned J-harmonic law, NOT unconditionally the number one.
This is where the ORIGINAL mixed Ptw parity source memory survives. -/
noncomputable def sourceNativeOriginalALLPJHistorySignedRef434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (Ptw : Finset ℕ) (b1 b2 : Bool) : ℂ :=
  ∑ s ∈ Fintype.piFinset
    (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1),
    (sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ) *
    sourceNativeOriginalALLPJHistoryPtwPhase434 r L J Ptw b1 b2 s

/-- Arbitrary original logarithmic saving for the FULL PHASED RAW
J-history coefficient relative to its TRUE signed reference,
simultaneously for all four source/target sign pairs. The correct
mixed-sign phase is kept INSIDE the J-history expectation, before
forming the four-sign projector. The original full SMALL/BIG
P-band law and independent BIG auxiliary exclusions are retained.

This closes the signed analog of the scalar ratio correction at
the common-J history level, but NOT the literal identification
of this J-history law with the whole Fock/OLD/memory SOURCE03
operator, which is still open. -/
theorem eventually_native_original_ALL_P_signed_J_RAW_reference434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ∀ (Ptw : Finset ℕ) (b1 b2 : Bool),
      ‖sourceNativeOriginalALLPJHistorySignedRAW434
          r L J Ptw b1 b2 A B -
        sourceNativeOriginalALLPJHistorySignedRef434
          r L J Ptw b1 b2‖ ≤
      L^(-Dsave) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_phase_weighted_RAW_saving434
      r hr tmax Dsave] with L h
  refine ⟨h.1, ?_⟩
  intro J m pat aux hJ hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend Ptw b1 b2
  let G := SourceNativeOriginalAllP434 r L
  let T : Finset (G × Fin J → ℕ) :=
    Fintype.piFinset (fun i : G × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1)
  let mu : (G × Fin J → ℕ) → ℝ := fun s =>
    sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s
  let ph : (G × Fin J → ℕ) → ℂ := fun s =>
    sourceNativeOriginalALLPJHistoryPtwPhase434 r L J Ptw b1 b2 s
  let W := sourceOriginalJRawWeight434 J A B
  have hPh : ∀ s ∈ T, ‖ph s‖ ≤ 1 := by
    intro s hs
    exact le_of_eq (source_native_original_ALL_P_J_history_phase_unit434
      r L J Ptw b1 b2 s)
  have hBound := h.2 J m pat aux hJ hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend ph hPh
  change ‖(∑ s ∈ T, (mu s:ℂ)*ph s*((W s:ℝ):ℂ)) -
      (∑ s ∈ T, (mu s:ℂ)*ph s)‖ ≤ L^(-Dsave)
  have hEq :
      (∑ s ∈ T, (mu s:ℂ)*ph s*((W s:ℝ):ℂ)) -
        (∑ s ∈ T, (mu s:ℂ)*ph s) =
      ∑ s ∈ T, (mu s:ℂ)*ph s*(((W s-1:ℝ):ℂ)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    push_cast
    ring
  rw [hEq]
  exact hBound
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPSignedRAWProjector -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The exact SOURCE four-sign projector is formed BEFORE bounding
the J-harmonic history: (00-10-01+11)/4.
Each original RAW channel retains its true history-dependent Ptw
phase and actual all-P source harmonic sampling law. -/
noncomputable def sourceNativeOriginalALLPJTrueProjectedRAW434
    (r : ℕ) (L : ℝ) (J : ℕ) (Ptw : Finset ℕ)
    (A B : SourceNativeOriginalAllP434 r L → Finset ℕ) : ℂ :=
  (sourceNativeOriginalALLPJHistorySignedRAW434
      r L J Ptw false false A B
    -sourceNativeOriginalALLPJHistorySignedRAW434
      r L J Ptw true false A B
    -sourceNativeOriginalALLPJHistorySignedRAW434
      r L J Ptw false true A B
    +sourceNativeOriginalALLPJHistorySignedRAW434
      r L J Ptw true true A B)/4

/-- The true projected signed comparison reference is NOT 1:
the unit Ptw phase remains INSIDE the same four-channel harmonic
expectation. The raw full source comparison root still needs the
B8/CRT physical operator alignment with this reference. -/
noncomputable def sourceNativeOriginalALLPJTrueProjectedRef434
    (r : ℕ) (L : ℝ) (J : ℕ) (Ptw : Finset ℕ) : ℂ :=
  (sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw false false
    -sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw true false
    -sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw false true
    +sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw true true)/4

/-- The ORIGINAL FOUR-SIGN Ptw-projected full-P source J-history RAW
coefficient differs from its CORRECT phase-weighted reference by an
arbitrary fixed L^-D for all moving source J≤tmax, free m≤tmax,
true S/Ts/Tb prime groups, true independent BIG auxiliary values,
both original endpoint free-mark sets and all original Ptw choices.

Crucially no mixed-sign phase is set to one and no independent
unsigned channel square is introduced. This is a statement on the
actual finite unconditioned J-harmonic source law; its identity with
the full Fock/OLD/Memory SOURCE03 kernel is an open interface. -/
theorem eventually_native_original_ALL_P_true_four_sign_J_saving434
    (r : ℕ) (hr : 1 ≤ r) (tmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (J m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat),
      J ≤ tmax → m ≤ tmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ∀ (Ptw : Finset ℕ),
      ‖sourceNativeOriginalALLPJTrueProjectedRAW434
          r L J Ptw A B -
        sourceNativeOriginalALLPJTrueProjectedRef434
          r L J Ptw‖ ≤
      L^(-Dsave) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_signed_J_RAW_reference434
      r hr tmax Dsave]
    with L h
  refine ⟨h.1, ?_⟩
  intro J m pat aux hJ hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend Ptw
  let error : Bool → Bool → ℂ := fun b1 b2 =>
    sourceNativeOriginalALLPJHistorySignedRAW434
       r L J Ptw b1 b2 A B -
    sourceNativeOriginalALLPJHistorySignedRef434
       r L J Ptw b1 b2
  have hError : ∀ b1 b2, ‖error b1 b2‖ ≤ L^(-Dsave) := by
    intro b1 b2
    exact h.2 J m pat aux hJ hm w wp hw hwp hwCap hwpCap
      A B hA hB hAend hBend Ptw b1 b2
  have hFour :
      ‖error false false-error true false-
        error false true+error true true‖ ≤ 4*L^(-Dsave) := by
    have h1 := norm_sub_le (error false false-error true false)
      (error false true)
    have h2 := norm_sub_le (error false false) (error true false)
    have h3 := norm_add_le
      (error false false-error true false-error false true)
      (error true true)
    have ha := hError false false
    have hb := hError true false
    have hc := hError false true
    have hd := hError true true
    linarith [h1,h2,h3]
  have hEq :
      sourceNativeOriginalALLPJTrueProjectedRAW434 r L J Ptw A B -
        sourceNativeOriginalALLPJTrueProjectedRef434 r L J Ptw =
      (error false false-error true false-
        error false true+error true true)/4 := by
    dsimp [sourceNativeOriginalALLPJTrueProjectedRAW434,
      sourceNativeOriginalALLPJTrueProjectedRef434,error]
    ring
  rw [hEq]
  rw [norm_div]
  have hden : ‖(4:ℂ)‖ = 4 := by norm_num
  rw [hden]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    (by nlinarith [hFour])
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPSignedFixedJ -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false

/-- In the TRUE source SOURCE03/Type II setup J0 is a FIXED physical
number of shared history slots, chosen before L, and is NOT bounded
by the original free-prime count cfg.tmax. Meanwhile the physical
pattern free index m≤ mmax is independent of J0.

The full original P=S/Ts/Tb J-harmonic SOURCE FOUR-SIGN parity
projected RAW correction has uniform L^-D relative to its
CORRECT Ptw-phase-weighted reference, for all source/target
physical endpoints. This does not assume the mixed parity phase is
one, nor does it tune J0 after the source residual parameter m. -/
theorem eventually_native_original_ALL_P_TRUE_FOUR_SIGN_FIXED_J0_saving434
    (r : ℕ) (hr : 1 ≤ r) (J0 mmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J0 m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J0 m pat),
      m ≤ mmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ∀ (Ptw : Finset ℕ),
      ‖sourceNativeOriginalALLPJTrueProjectedRAW434
          r L J0 Ptw A B -
        sourceNativeOriginalALLPJTrueProjectedRef434
          r L J0 Ptw‖ ≤
      L^(-Dsave) := by
  filter_upwards [
    eventually_native_original_ALL_P_true_four_sign_J_saving434
      r hr (max J0 mmax) Dsave] with L h
  refine ⟨h.1, ?_⟩
  intro m pat aux hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend Ptw
  exact h.2 J0 m pat aux (Nat.le_max_left _ _)
    (hm.trans (Nat.le_max_right _ _))
    w wp hw hwp hwCap hwpCap A B hA hB hAend hBend Ptw
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPTrueParityMean -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The exact original Ptw expectation over the unconditioned
all-P J common-history prime product; it is a complex number,
real ±1 at each history before averaging. This is NOT
automatically one in mixed-sign source/target parity channels. -/
noncomputable def sourceNativeOriginalALLPJHistoryPtwMean434
    (r : ℕ) (L : ℝ) (J : ℕ) (Ptw : Finset ℕ) : ℂ :=
  ∑ s ∈ Fintype.piFinset
    (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
      SourceNativeOriginalAllPBand434 r L i.1),
    (sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ) *
    literalSourceParity Ptw
      (sourceNativeOriginalAllPCommonDivisor434 r L J s)

/-- Original native P-harmonic law is exactly NORMALIZED, on all
S/Ts/Tb J-draws, with full repeated choices retained. -/
theorem source_native_original_ALL_P_J_law_total434
    (r : ℕ) (L : ℝ) (J : ℕ)
    (hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g) :
    (∑ s ∈ Fintype.piFinset
      (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
        SourceNativeOriginalAllPBand434 r L i.1),
      (sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
        (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ)) = 1 := by
  classical
  let G := SourceNativeOriginalAllP434 r L
  let S : G × Fin J → Finset ℕ :=
    fun i => SourceNativeOriginalAllPBand434 r L i.1
  let mu : G × Fin J → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p
  have hM : ∀ i, ∑ p ∈ S i, mu i p = 1 := by
    intro i
    apply source_prime_shared_atom_total434
    · simp [S,sourceNativeOriginalAllPMass434,one_div]
    · exact (hV i.1).ne'
  have ht := source_shared_law_total434 S mu hM
  change (∑ s ∈ Fintype.piFinset S,
    (sourceSharedLaw434 mu s:ℂ)) = 1
  have hCast : (∑ s ∈ Fintype.piFinset S,
    (sourceSharedLaw434 mu s:ℂ)) =
      ((∑ s ∈ Fintype.piFinset S, sourceSharedLaw434 mu s:ℝ):ℂ) := by
    push_cast
    rfl
  rw [hCast,ht]
  norm_num

/-- The correct original FOUR-SIGN reference on the unconditioned
common physical J-harmonic history is exactly
   PtwRef = (1 - E[epsilon_Ptw(D_R)])/2.
This is an exact original source parity projector BEFORE squaring;
it does not pretend the mixed-sign reference equals 1.

Its possible nontrivial phase depends on Ptw (only constrained by
Ptw⊆G in source comparison data), not on the fact that all
physical primes lie in the larger P union. -/
theorem source_native_original_ALL_P_J_true_four_sign_ref434
    (r : ℕ) (L : ℝ) (J : ℕ) (Ptw : Finset ℕ)
    (hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g) :
    sourceNativeOriginalALLPJTrueProjectedRef434 r L J Ptw =
      (1-sourceNativeOriginalALLPJHistoryPtwMean434 r L J Ptw)/2 := by
  classical
  let T : Finset (SourceNativeOriginalAllP434 r L × Fin J → ℕ) :=
    Fintype.piFinset
      (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
        SourceNativeOriginalAllPBand434 r L i.1)
  let mu : (SourceNativeOriginalAllP434 r L × Fin J → ℕ) → ℂ := fun s =>
    (sourceSharedLaw434 (fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p) s:ℂ)
  let eps : (SourceNativeOriginalAllP434 r L × Fin J → ℕ) → ℂ := fun s =>
    literalSourceParity Ptw (sourceNativeOriginalAllPCommonDivisor434 r L J s)
  have hFF : sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw false false = ∑ s ∈ T, mu s := by
    unfold sourceNativeOriginalALLPJHistorySignedRef434
    apply Finset.sum_congr rfl
    intro s hs
    simp [sourceNativeOriginalALLPJHistoryPtwPhase434,mu]
  have hTF : sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw true false = ∑ s ∈ T, mu s*eps s := by
    unfold sourceNativeOriginalALLPJHistorySignedRef434
    apply Finset.sum_congr rfl
    intro s hs
    simp [sourceNativeOriginalALLPJHistoryPtwPhase434,mu,eps]
  have hFT : sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw false true = ∑ s ∈ T, mu s*eps s := by
    unfold sourceNativeOriginalALLPJHistorySignedRef434
    apply Finset.sum_congr rfl
    intro s hs
    simp [sourceNativeOriginalALLPJHistoryPtwPhase434,mu,eps]
  have hTT : sourceNativeOriginalALLPJHistorySignedRef434
      r L J Ptw true true = ∑ s ∈ T, mu s := by
    unfold sourceNativeOriginalALLPJHistorySignedRef434
    apply Finset.sum_congr rfl
    intro s hs
    have hSquare := source_original_true_parity_square434 Ptw
      (sourceNativeOriginalAllPCommonDivisor434 r L J s)
    simp [sourceNativeOriginalALLPJHistoryPtwPhase434,mu,hSquare]
  have htotal : (∑ s ∈ T, mu s)=1 :=
    source_native_original_ALL_P_J_law_total434 r L J hV
  have hmean : (∑ s ∈ T, mu s*eps s) =
      sourceNativeOriginalALLPJHistoryPtwMean434 r L J Ptw := rfl
  unfold sourceNativeOriginalALLPJTrueProjectedRef434
  rw [hFF,hTF,hFT,hTT,htotal,hmean]
  ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPParityProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The true original SOURCE03 common J-history divisor is a LABELLED
product of all P-group J-prime draws. Its Ptw-multiplicity parity
is the EXACT product of per-draw prime Ptw parities even when a
selected prime appears repeatedly. The original unconditioned
full S/Ts/Tb harmonic sample space is unchanged. -/
theorem source_native_original_ALL_P_Ptw_history_parity_prod434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (Ptw : Finset ℕ)
    (s : SourceNativeOriginalAllP434 r L × Fin J → ℕ)
    (hs : s ∈ Fintype.piFinset
      (fun i : SourceNativeOriginalAllP434 r L × Fin J =>
        SourceNativeOriginalAllPBand434 r L i.1)) :
    literalSourceParity Ptw
      (sourceNativeOriginalAllPCommonDivisor434 r L J s) =
    ∏ i : SourceNativeOriginalAllP434 r L × Fin J,
      literalSourceParity Ptw (s i) := by
  classical
  let G := SourceNativeOriginalAllP434 r L
  have hNonzero : ∀ i : G × Fin J, s i ≠ 0 := by
    intro i
    have hMember := (Fintype.mem_piFinset.mp hs) i
    exact (source_native_original_ALL_P_prime_range434
      r L hL i.1 (s i) hMember).1.ne_zero
  have hProd (T : Finset (G × Fin J)) :
      literalSourceParity Ptw (∏ i ∈ T, s i) =
      ∏ i ∈ T, literalSourceParity Ptw (s i) := by
    induction T using Finset.induction_on with
    | empty =>
      simp [literalSourceParity]
    | @insert i T hi ih =>
      have hRest : (∏ j ∈ T, s j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j hj => hNonzero j)
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        source_literal_parity_mul434 Ptw _ _ (hNonzero i) hRest, ih]
  unfold sourceNativeOriginalAllPCommonDivisor434
  exact hProd Finset.univ

/-- EXACT original independent signed harmonic Ptw parity MEAN,
without any "random sign cancellation" assumption:
  E_{all P groups, all J slots} epsilon_Ptw(D_R)
  = product_{g in S/Ts/Tb} [
      sum_{p in P_g} (1/(p V_g)) epsilon_Ptw(p)
    ]^J.
This is an identity, and does NOT assert the signed prime harmonic
mass is small for any Ptw. In particular the original Ptw⊆G
case is retained; all repetitions count with their multiplicity. -/
theorem source_native_original_ALL_P_Ptw_mean_product434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (Ptw : Finset ℕ) :
    sourceNativeOriginalALLPJHistoryPtwMean434 r L J Ptw =
      ∏ g : SourceNativeOriginalAllP434 r L,
        (∑ p ∈ SourceNativeOriginalAllPBand434 r L g,
          ((sourcePrimeSharedAtom434
              (sourceNativeOriginalAllPMass434 r L g) p:ℝ):ℂ) *
            literalSourceParity Ptw p)^J := by
  classical
  let G := SourceNativeOriginalAllP434 r L
  let S : G × Fin J → Finset ℕ :=
    fun i => SourceNativeOriginalAllPBand434 r L i.1
  let mu : G × Fin J → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L i.1) p
  have hMem (s : G × Fin J → ℕ) (hs : s ∈ Fintype.piFinset S) :
      literalSourceParity Ptw
        (sourceNativeOriginalAllPCommonDivisor434 r L J s) =
      ∏ i : G × Fin J, literalSourceParity Ptw (s i) :=
    source_native_original_ALL_P_Ptw_history_parity_prod434
      r L hL J Ptw s hs
  calc
    sourceNativeOriginalALLPJHistoryPtwMean434 r L J Ptw =
      ∑ s ∈ Fintype.piFinset S,
        (∏ i : G × Fin J, ((mu i (s i):ℝ):ℂ)) *
        (∏ i : G × Fin J, literalSourceParity Ptw (s i)) := by
        unfold sourceNativeOriginalALLPJHistoryPtwMean434
        apply Finset.sum_congr rfl
        intro s hs
        rw [hMem s hs]
        simp only [sourceSharedLaw434, Complex.ofReal_prod]
        rfl
    _ = ∑ s ∈ Fintype.piFinset S,
        ∏ i : G × Fin J,
          ((mu i (s i):ℝ):ℂ)*literalSourceParity Ptw (s i) := by
        simp_rw [Finset.prod_mul_distrib]
    _ = ∏ i : G × Fin J,
        ∑ p ∈ S i, ((mu i p:ℝ):ℂ)*literalSourceParity Ptw p := by
        exact (Finset.prod_univ_sum S
          (fun i p => ((mu i p:ℝ):ℂ) *
            literalSourceParity Ptw p)).symm
    _ = ∏ g : G,
        (∑ p ∈ SourceNativeOriginalAllPBand434 r L g,
          ((sourcePrimeSharedAtom434
              (sourceNativeOriginalAllPMass434 r L g) p:ℝ):ℂ) *
              literalSourceParity Ptw p)^J := by
        rw [Fintype.prod_prod_type]
        apply Finset.prod_congr rfl
        intro g hg
        simp [S,mu]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativePtwPrimeSign -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact original valuation-multiplicity parity on ONE native
prime, for arbitrary Ptw⊆G. The sign is -1 iff the actual
prime value belongs to Ptw, regardless of how often the
same prime is selected by the unconditioned J-history. -/
theorem source_native_original_literal_Ptw_prime_sign434
    (Ptw : Finset ℕ) (p : ℕ) (hp : p.Prime) :
    literalSourceParity Ptw p =
      if p ∈ Ptw then (-1:ℂ) else 1 := by
  classical
  by_cases hmem : p ∈ Ptw
  · simp [hmem,source_literal_parity_prime434 Ptw p hp hmem]
  · unfold literalSourceParity
    rw [hp.factorization]
    have hsum : (∑ q ∈ Ptw, (Finsupp.single p (1:ℕ)) q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hneq : q ≠ p := by
        intro h
        exact hmem (h ▸ hq)
      simp [Finsupp.single_apply, hneq]
    rw [hsum]
    simp [hmem]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPTrueParityComparison -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The CORRECT original four-sign Ptw-projected finite RAW/Comparison
source interface, with the literal full P=S/Ts/Tb J-fold harmonic law:
the signed RAW projected history is close (arbitrary log-saving)
to the true expected Ptw parity projector
        (1-E_{hist}[epsilon_Ptw(Dhist)])/2,
NOT to an unconditional scalar one.

All four original endpoint sign channels are projected BEFORE norms;
the parity phase stays correlated with the shared source history.
The original fixed J0 may exceed mmax, chosen independently before L.
No claim is made that E epsilon=0 or 1 for arbitrary Ptw⊆G:
this is the remaining physical signed-memory/correlation object to
identify with the actual B8/CRT source K continuation. -/
theorem eventually_native_original_ALL_P_TRUE_PARITY_COMPARISON434
    (r : ℕ) (hr : 1 ≤ r) (J0 mmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J0 m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J0 m pat),
      m ≤ mmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ∀ (Ptw : Finset ℕ),
      ‖sourceNativeOriginalALLPJTrueProjectedRAW434
          r L J0 Ptw A B -
        (1-sourceNativeOriginalALLPJHistoryPtwMean434
          r L J0 Ptw)/2‖ ≤
      L^(-Dsave) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_TRUE_FOUR_SIGN_FIXED_J0_saving434
      r hr J0 mmax Dsave,
    eventually_native_original_ALL_P_masses434 r]
    with L hRaw hMass
  refine ⟨hRaw.1, ?_⟩
  intro m pat aux hm w wp hw hwp hwCap hwpCap A B
    hA hB hAend hBend Ptw
  have hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g := by
    intro g
    exact ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive.trans_le
      (hMass g).1
  have hMean := source_native_original_ALL_P_J_true_four_sign_ref434
    r L J0 Ptw hV
  rw [←hMean]
  exact hRaw.2 m pat aux hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend Ptw
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativePtwSignedMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- For an arbitrary genuine finite prime band S with a TRUE normalized
real harmonic law mu and original multiplicity Ptw parity, the EXACT
signed prime mass is
  1 - 2*mu(S ∩ Ptw).
No cancellation, density or random-sign hypothesis is inserted. -/
theorem source_native_original_Ptw_signed_prime_mass434
    (S Ptw : Finset ℕ) (mu : ℕ → ℝ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hmass : ∑ p ∈ S, mu p = 1) :
    (∑ p ∈ S, ((mu p:ℝ):ℂ)*literalSourceParity Ptw p) =
      1 - 2*((∑ p ∈ S.filter (fun p => p ∈ Ptw), mu p:ℝ):ℂ) := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ S) :
      ((mu p:ℝ):ℂ)*literalSourceParity Ptw p =
      (mu p:ℂ) -
        2*(if p∈Ptw then (mu p:ℂ) else 0) := by
    rw [source_native_original_literal_Ptw_prime_sign434
      Ptw p (hprime p hp)]
    by_cases h : p∈Ptw
    · simp [h]
      ring
    · simp [h]
  calc
    _ = ∑ p ∈ S, ((mu p:ℂ) -
        2*(if p∈Ptw then (mu p:ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hpoint p hp
    _ = (∑ p ∈ S, (mu p:ℂ)) -
        2*(∑ p ∈ S, if p∈Ptw then (mu p:ℂ) else 0) := by
      rw [Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
    _ = 1 - 2*((∑ p ∈ S.filter (fun p => p ∈ Ptw), mu p:ℝ):ℂ) := by
      rw [←Complex.ofReal_sum,hmass]
      rw [Finset.sum_filter]
      have hCast : (∑ p ∈ S, if p∈Ptw then (mu p:ℂ) else 0) =
          ((∑ p ∈ S, if p∈Ptw then mu p else 0:ℝ):ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : p∈Ptw <;> simp [h]
      rw [hCast]
      push_cast
      ring

/-- TRUE all-P signed harmonic group mass, expressed EXACTLY in terms
of the original overlapping prime harmonic mass:
 signedMass_g = 1 - 2 * V(Ptw ∩ P_g)/V_g.

This formula uses the original positive reciprocal source mass and
literal source full-group P bands, including SMALL and BIG. -/
theorem source_native_original_TRUE_Ptw_group_signed_mass434
    (r : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (g : SourceNativeOriginalAllP434 r L)
    (hV : 0 < sourceNativeOriginalAllPMass434 r L g)
    (Ptw : Finset ℕ) :
    (∑ p ∈ SourceNativeOriginalAllPBand434 r L g,
      ((sourcePrimeSharedAtom434
        (sourceNativeOriginalAllPMass434 r L g) p:ℝ):ℂ) *
        literalSourceParity Ptw p) =
      1 - 2*((∑ p ∈
        (SourceNativeOriginalAllPBand434 r L g).filter
          (fun p => p∈Ptw),
        sourcePrimeSharedAtom434
          (sourceNativeOriginalAllPMass434 r L g) p:ℝ):ℂ) := by
  classical
  apply source_native_original_Ptw_signed_prime_mass434
  · intro p hp
    exact (source_native_original_ALL_P_prime_range434
      r L hL g p hp).1
  · apply source_prime_shared_atom_total434
    · simp [sourceNativeOriginalAllPMass434,one_div]
    · exact hV.ne'
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeTruePtwHarmonicReference -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal normalized source Ptw mass within a genuine original
SMALL S/Ts or BIG Tb band, using the unchanged independent harmonic
prime sampling law 1/(p V_g). Defined on EVERY Ptw⊆G, without
assuming Ptw contains whole bands, is randomly balanced or is
squarefree. -/
noncomputable def sourceNativeOriginalPtwRelativeMass434
    (r : ℕ) (L : ℝ) (Ptw : Finset ℕ)
    (g : SourceNativeOriginalAllP434 r L) : ℝ :=
  ∑ p ∈ (SourceNativeOriginalAllPBand434 r L g).filter
      (fun p => p ∈ Ptw),
    sourcePrimeSharedAtom434
      (sourceNativeOriginalAllPMass434 r L g) p

/-- Exact ORIGINAL four-sign signed RAW comparator reference for all
source S/Ts/Tb J-harmonic draws, at any source Ptw⊆G:

  (1 - product_g (1 - 2*mu_g(Ptw))^J)/2.

This is a genuinely source-grounded finite identity, with complete
prime-band overlap weights and actual J. In general the RHS need
NOT be 1 or 1/2 and can be ZERO when all \`mu_g\` are 0 or 1
with the appropriate parity.

Thus no universal \`Ptw\` mean-square saving follows merely from
four-sign projection; the unresolved comparison/B8 transport must
preserve the true signed reference. -/
theorem eventually_source_original_TRUE_Ptw_projector_exact434
    (r J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (Ptw : Finset ℕ),
        sourceNativeOriginalALLPJTrueProjectedRef434 r L J Ptw =
        (1 - (∏ g : SourceNativeOriginalAllP434 r L,
          ((1:ℂ) - 2*
            ((sourceNativeOriginalPtwRelativeMass434 r L Ptw g:ℝ):ℂ))^J))/2 := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_masses434 r,
    eventually_ge_atTop (Real.exp 1)]
    with L hMass hL
  refine ⟨hL, ?_⟩
  intro Ptw
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hv : 0 < Real.log (6/5:ℝ)/2 :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g :=
    fun g => hv.trans_le (hMass g).1
  have hRef := source_native_original_ALL_P_J_true_four_sign_ref434
    r L J Ptw hV
  have hProduct := source_native_original_ALL_P_Ptw_mean_product434
    r L hL1 J Ptw
  rw [hRef,hProduct]
  congr 2
  apply Finset.prod_congr rfl
  intro g hg
  congr 1
  simpa only [sourceNativeOriginalPtwRelativeMass434] using
    source_native_original_TRUE_Ptw_group_signed_mass434
      r L hL1 g (hV g) Ptw
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeCanonicalFullPtwReference -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The TRUE original FULL parity twist Ptw=G contains EVERY
source prime in each actual SMALL S/Ts and BIG Tb group.
The groupwise Ptw harmonic mass is EXACTLY ONE, not an
unproved equidistribution statistic. All original P band
endpoints are unchanged. -/
theorem source_native_original_FULL_Ptw_group_mass_one434
    (r : ℕ) (L : ℝ)
    (g : SourceNativeOriginalAllP434 r L)
    (hV : 0 < sourceNativeOriginalAllPMass434 r L g) :
    sourceNativeOriginalPtwRelativeMass434 r L
      (sourceNativeOriginalG434 r L) g = 1 := by
  classical
  have hSubset :
      ∀ p ∈ SourceNativeOriginalAllPBand434 r L g,
        p∈sourceNativeOriginalG434 r L := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hp⟩
  unfold sourceNativeOriginalPtwRelativeMass434
  rw [Finset.filter_true_of_mem hSubset]
  apply source_prime_shared_atom_total434
  · simp [sourceNativeOriginalAllPMass434,one_div]
  · exact hV.ne'

/-- Exact ORIGINAL canonical four-sign Ptw=G reference:
  (1 - (-1)^(J*|all S/Ts/Tb groups|))/2.
There is NO "random mean" saving: the true full-G parity is
DETERMINISTIC because every J-selected prime contributes -1,
even if the same prime occurs repeatedly.

In particular the projected reference can vanish for even
J*|G|. The original source choice of J and the marked source
parity projectors must therefore be matched literally; a
generic Ptw⊆G or arbitrary cfg.tmax positive lower bound cannot
be inferred from the signed comparison theorem. -/
theorem eventually_source_native_CANONICAL_FULL_Ptw_ref434
    (r J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      sourceNativeOriginalALLPJTrueProjectedRef434 r L J
        (sourceNativeOriginalG434 r L) =
      (1 - (-1:ℂ)^(J*Fintype.card
        (SourceNativeOriginalAllP434 r L)))/2 := by
  classical
  filter_upwards [
    eventually_source_original_TRUE_Ptw_projector_exact434 r J,
    eventually_native_original_ALL_P_masses434 r,
    eventually_ge_atTop (Real.exp 1)]
    with L hExact hMass hL
  refine ⟨hL, ?_⟩
  have hRef := hExact.2 (sourceNativeOriginalG434 r L)
  rw [hRef]
  have hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g := by
    intro g
    exact ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive.trans_le
      (hMass g).1
  have hRel : ∀ g : SourceNativeOriginalAllP434 r L,
      sourceNativeOriginalPtwRelativeMass434 r L
        (sourceNativeOriginalG434 r L) g=1 := by
    intro g
    exact source_native_original_FULL_Ptw_group_mass_one434 r L g (hV g)
  simp_rw [hRel]
  simp only [Complex.ofReal_one]
  have hbase : (1:ℂ)-2*1 = -1 := by ring
  rw [hbase]
  simp [Finset.prod_const, Finset.card_univ, pow_mul, mul_comm]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalChebyshev64GeometricMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 220000

/-- ACTUAL unconditional lower reciprocal-prime mass for every
collection of contiparityus source factor-64 prime subbands.
No assumptions on prime locations, Mertens or group availability;
only the integer starting value u>=512. -/
theorem source_original_TRUE_prime_harmonic_geometric_sum434
    (u N : ℕ) (hu : 512 ≤ u) :
    (∑ i ∈ Finset.range N,
        (1:ℝ)/(16*Real.log
          (sourceOriginalChebyshevGeometricCut434 u i:ℝ))) ≤
      sourceOriginalPrimeBandHarmonicMass434 u
        (sourceOriginalChebyshevGeometricCut434 u N) := by
  have hmono := source_original_chebyshev_geometric_cut_mono434 u
  have hu0 : sourceOriginalChebyshevGeometricCut434 u 0 = u := by
    simp [sourceOriginalChebyshevGeometricCut434]
  have hi (i : ℕ) :
      512 ≤ sourceOriginalChebyshevGeometricCut434 u i := by
    have hh : u ≤ sourceOriginalChebyshevGeometricCut434 u i := by
      simpa only [hu0] using hmono (Nat.zero_le i)
    exact hu.trans hh
  have hpartition := source_original_TRUE_prime_harmonic_partition434
    (sourceOriginalChebyshevGeometricCut434 u) hmono N
  have hpartition' :
      sourceOriginalPrimeBandHarmonicMass434 u
        (sourceOriginalChebyshevGeometricCut434 u N) =
        ∑ i ∈ Finset.range N,
          sourceOriginalPrimeBandHarmonicMass434
            (sourceOriginalChebyshevGeometricCut434 u i)
            (sourceOriginalChebyshevGeometricCut434 u (i+1)) := by
    simpa only [hu0] using hpartition
  rw [hpartition']
  apply Finset.sum_le_sum
  intro i hii
  simpa only [sourceOriginalChebyshevGeometricCut434,
    pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    (source_original_TRUE_prime_harmonic_64block_lower434
      (sourceOriginalChebyshevGeometricCut434 u i) (hi i))
end Green64Analytic.CorrelationSquare

end

end

