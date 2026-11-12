module

public import Green64.Library.Weights.IndependentPathMass
public import Green64.Library.Weights.PolynomialPathBudget
public import Green64.Library.Correlation.MemoryActualDomain
public import Green64.Library.Correlation.LocalHaarPhysical
public import Green64.Library.Analysis.Estimates.AllPrimeSum
public import Green64.Library.Weights.MarkedPathReturn
public import Green64.Library.Correlation.Part042
public import Green64.Library.Correlation.PhysicalRowBudget
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Weights.Part048
public import Green64.Library.Weights.ParityLocalizationWindow
public import Green64.Library.Weights.Part072
public import Green64.Library.Weights.CleanCofactorGrowth
public import Mathlib
public import Green64.Library.Correlation.Part036
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.Part071
public import Green64.Library.Weights.Part067
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

/-!
# Weights / Part073

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualParityPathMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Sum of absolute values of the literal complete original Parity arrays.
Both initial masses, all patterns, and every physical marked Knu remain. -/
def b644ActualParityAbsoluteArrayMass434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (shift : ℤ) (N : ℕ) : ℝ := by
  classical
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  letI : Fintype (MemoryPrimitiveEFrame (SG := SourceNativeMemorySG434 20 L hS) BP J 1 m pats) := by
    unfold MemoryPrimitiveEFrame
    infer_instance
  exact ∑ states : Fin (N+1) →
      MemoryIndependentState SP (fun _ p => p.val) BP (fun _ p => p.val) J 1,
    ∑ frames : Fin N → MemoryPrimitiveEFrame (SG := SourceNativeMemorySG434 20 L hS) BP J 1 m pats,
      ‖memoryIndOriginalArrayWeight SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift states frames‖

/-- Actual complete moving Parity family. C is fixed after J,m,Cq,Cxi and
before L, shifts, Fourier phases, path length, and all path choices.
This is the cost used to sum CRT errors, not the signed root saving. -/
theorem b644_eventually_actual_parity_absolute_path_mass434
    (J m Cq Cxi : ℕ) (hmJ : m ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      0 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (Q : ℕ) (h xi zeta theta : ℝ) (shift : ℤ) (N : ℕ),
        (Q:ℝ) ≤ L^Cq → 0 < h → 0 < xi → xi⁻¹ ≤ L^Cxi →
        b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta shift N ≤
          L^(C*(N:ℝ)) := by
  let v : ℝ := Real.log (6/5:ℝ)/2
  let C0 : ℝ := 4+(Real.log 2)⁻¹
  let B : ℝ := b644RawComparisonExponent434 (J+1) m Cq Cxi (1/2:ℝ) v C0
  let C := max 0 B
  have hv : 0 < v := ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hC0 : 0 ≤ C0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C0]
    positivity
  refine ⟨C, le_max_left _ _, ?_⟩
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2:ℝ)] with L hMass hexp hL2
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  refine ⟨hL0, hMass.2.1, ?_⟩
  intro hS Q h xi zeta theta shift N hQ hh hxi hXi
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let Vs := SourceNativeMemorySmallMass434 20 L hS
  let Vb := sourceNativeOriginalVbig434 20 L
  let blockA := sourceNativeOriginalBigBlockA434 20 L
  let blockB := sourceNativeOriginalBigBlockB434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) Vb blockA blockB
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let Kcap := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  have hVs (g) : v ≤ Vs g := by
    cases g with
    | none => exact (hMass.2.2 hS).1.1
    | some i => exact ((hMass.2.2 hS).2.1 i).1
  have hVb (g) : v ≤ Vb g := ((hMass.2.2 hS).2.2 g).1
  have hVs0 (g) : 0 < Vs g := hv.trans_le (hVs g)
  have hVb0 (g) : 0 < Vb g := hv.trans_le (hVb g)
  have hHs (g) : Vs g = ∑ p : SP g, 1/(p.val:ℝ) := by
    cases g with
    | none =>
      simpa [Vs, SP, SourceNativeMemorySmallMass434, sourceNativeOriginalVs434,
        SourceNativeMemorySP434, one_div] using
        (Finset.sum_attach (sourceNativeOriginalS434 20 L hS) (fun p => (p:ℝ)⁻¹)).symm
    | some i =>
      simpa [Vs, SP, SourceNativeMemorySmallMass434, sourceNativeOriginalVsmall434,
        SourceNativeMemorySP434, one_div] using
        (Finset.sum_attach (sourceNativeOriginalTs434 20 L hS i) (fun p => (p:ℝ)⁻¹)).symm
  have hHb (g) : Vb g = ∑ p : BP g, 1/(p.val:ℝ) := by
    simpa [Vb, BP, sourceNativeOriginalVbig434, SourceNativeMemoryBP434, one_div] using
      (Finset.sum_attach (sourceNativeOriginalTb434 20 L g) (fun p => (p:ℝ)⁻¹)).symm
  have hcounts := source_native_original_group_upper_counts434 20 L hS (by norm_num) hexp
  have hGs : (Fintype.card (SourceNativeMemorySG434 20 L hS):ℝ) ≤ C0*Real.log L := by
    simp only [SourceNativeMemorySG434, Fintype.card_option, Nat.cast_add, Nat.cast_one]
    dsimp [C0]
    nlinarith [hcounts.1]
  have hGb : (Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ) ≤ C0*Real.log L := by
    dsimp [C0]
    nlinarith [hcounts.2]
  have hK0 (nu) : 0 ≤ Kcap nu :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu
  have hK (nu aux s t) : ‖Knu nu aux s t‖ ≤ Kcap nu :=
    source_original_memory_RAW_COMPARISON_K_cap434
      (sourceNativeOriginalTb434 20 L) Vb blockA blockB J 1 m hmJ Q
      (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi nu aux s t
  let cost := b644IndependentRowBudget434 J 1 m pats (1/2:ℝ) Vs Vb Kcap
  have hcost0 : 0 ≤ cost := b644_independent_row_budget_nonneg434 J 1 m pats
    (1/2:ℝ) Vs Vb (by norm_num) (by norm_num) hVs0 hVb0 Kcap hK0
  have hcost : cost ≤ L^B :=
    b644_raw_comparison_absolute_row_polynomial434 blockA blockB J 1 m Q Cq Cxi hmJ
      (1/2:ℝ) v C0 L xi (by norm_num) (by norm_num) hv hC0 hL2 hxi
      Vs Vb hVs hVb hGs hGb hQ hXi
  have hcostC : cost ≤ L^C :=
    hcost.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
  have hb := b644_original_independent_absolute_array434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats
    (1/2:ℝ) Vs Vb (by norm_num) (by norm_num) hVs0 hVb0 hHs hHb
    Knu Kcap hK0 hK zeta theta shift N
  change b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta shift N ≤ _
  calc
    _ ≤ cost^N := hb
    _ ≤ (L^C)^N := pow_le_pow_left₀ hcost0 hcostC N
    _ = L^(C*(N:ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityPhysicalRoot -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 18000

/-- The literal full original marked path sum over ONE physical integer.
All SMALL/BIG ordered injective marks, all patterns, auxiliary draws and
four permutations remain in the carrier. The coefficient has both
initial V masses, the canonical physical Knu, and every original phase.
Every prime and visit is tested at the same n+offset_i. -/
def b645ActualParityPhysicalPathSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ)
    (shift : ℤ) (N lo hi : ℕ) : ℂ := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact ∑ ω : B643AllPrimePath434 SP BP J 1 m pats N,
    b643AllPrimeWeight434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift ω *
    ((∑ n ∈ Finset.Ico lo hi,
      b645ActualMarkedPathDensity434 L hS (J+1) N
        (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val)
        (b643AllPrimeOffset434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m pats ω shift) n : ℝ) : ℂ)

/-- Complete physical signed root transfer. Its only error factor is the
EXACT complete original array mass; both the main signed sum and this
mass are identified by the proved all-prime transport bijection.
No hCRT, model identity, or missing SMALL-coordinate hypothesis appears. -/
theorem b645_eventually_actual_parity_physical_root_transfer434
    (E gamma : ℝ) (hE : 0≤E) (hgamma : 0<gamma) (J m : ℕ) (hmJ : m≤J) :
    ∀ᶠ L : ℝ in atTop,
    (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty,
    let SP := SourceNativeMemorySP434 20 L hS
    let BP := SourceNativeMemoryBP434 20 L
    let pats := sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    ∀ (Q : ℕ) (h xi zeta theta : ℝ) (shift : ℤ) (lo hi : ℕ),
    let Knu := sourceOriginalMemoryRawComparisonK434
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
    Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
    ‖b645ActualParityPhysicalPathSum434 L hS J m hmJ Q h xi zeta theta shift N lo hi -
      (((hi-lo:ℕ):ℝ):ℂ) * memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift
        (Nat.ceil (L^(13/25:ℝ)))‖ ≤
    ((hi-lo:ℕ):ℝ) * L^(-E*(N:ℝ)) *
      b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta shift N := by
  filter_upwards [b645_eventually_actual_weighted_paths_CRT434 E gamma hE hgamma (J+1),
    eventually_ge_atTop (2:ℝ)] with L hCRT hL
  refine ⟨hCRT.1,?_⟩
  intro hS
  dsimp only
  intro Q h xi zeta theta shift lo hi hH
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let R := Nat.ceil (L^(13/25:ℝ))
  let N := 2*R
  let Ω := B643AllPrimePath434 SP BP J 1 m pats N
  let W : Ω → ℂ := b643AllPrimeWeight434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift
  let off : Ω → ℕ → ℤ := fun ω => b643AllPrimeOffset434 SP (fun _ p => p.val)
    BP (fun _ p => p.val) J 1 m pats ω shift
  let model : Ω → ℝ := fun ω => b643AllPrimeHaarModel434 SP (fun _ p => p.val)
    BP (fun _ p => p.val) J 1 m pats (1/2:ℝ) ω shift
  have hR : 0<R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have hN : 0<N := by dsimp [N]; omega
  have hModel (ω : Ω) :
      b645ActualMarkedPathModel434 L hS (J+1) N
        (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) (off ω) = model ω :=
    (b645_actual_all_prime_model434 L (by linarith) hS J 1 m pats N ω shift).symm
  have hroot : (∑ ω : Ω, W ω*(model ω : ℂ)) =
      memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift R :=
    (b643_original_root_all_prime_Haar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats (1/2:ℝ) (by norm_num) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift R hR).symm
  have hmass : (∑ ω : Ω, ‖W ω‖*model ω) =
      b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta shift N := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    dsimp [Ω,W,model]
    rw [hn]
    exact (b643_all_prime_full_norm_sum434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats (1/2:ℝ) (by norm_num) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift n).symm
  let PM : Ω → ℝ := fun ω => b645ActualMarkedPathModel434 L hS (J+1) N
    (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) (off ω)
  have hsigned : (∑ ω : Ω, W ω*(PM ω:ℂ)) =
      memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta theta shift R := by
    calc
      _ = ∑ ω : Ω, W ω*(model ω:ℂ) := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact congrArg (fun t : ℝ => W ω*(t:ℂ)) (hModel ω)
      _ = _ := hroot
  have habs : (∑ ω : Ω, ‖W ω‖*PM ω) =
      b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta shift N := by
    calc
      _ = ∑ ω : Ω, ‖W ω‖*model ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact congrArg (fun t : ℝ => ‖W ω‖*t) (hModel ω)
      _ = _ := hmass
  have ht := hCRT.2 hS (Ω:=Ω)
    (fun ω i g => (ω.1 i g).val) (fun ω i g => (ω.2.1 i g).val) W off lo hi hH
  change ‖b645ActualParityPhysicalPathSum434 L hS J m hmJ Q h xi zeta theta shift N lo hi -
    (((hi-lo:ℕ):ℝ):ℂ)*(∑ ω : Ω, W ω*(PM ω:ℂ))‖ ≤
    ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ))*(∑ ω : Ω, ‖W ω‖*PM ω) at ht
  rw [hsigned,habs] at ht
  exact ht
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityReturn -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

/-- The actual complete Parity physical path sum with position return ONLY.
The final ordered SMALL/BIG marks remain independent of the initial marks.
Every source frame and both initial masses are retained. -/
def b648ActualParityReturnPathSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (N lo hi : ℕ) : ℂ := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact ∑ ω : B643AllPrimePath434 SP BP J 1 m pats N,
    if b643AllPrimeOffset434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats ω shift N=0 then
      b643AllPrimeWeight434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta 0 shift ω *
      ((∑ n ∈ Finset.Ico lo hi,
        b645ActualMarkedPathDensity434 L hS (J+1) N
          (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val)
          (b643AllPrimeOffset434 SP (fun _ p => p.val) BP (fun _ p => p.val)
            J 1 m pats ω shift) n : ℝ) : ℂ)
    else 0

/-- Literal physical return selection via genuine Lebesgue integration of
the original internal theta phase on [0,1], before taking any norm. -/
theorem b648_actual_parity_return_integral434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (N lo hi : ℕ) :
    (∫ theta : ℝ in (0:ℝ)..1,
      b645ActualParityPhysicalPathSum434 L hS J m hmJ Q h xi zeta theta shift N lo hi) =
    b648ActualParityReturnPathSum434 L hS J m hmJ Q h xi zeta shift N lo hi := by
  unfold b645ActualParityPhysicalPathSum434 b648ActualParityReturnPathSum434
  exact b648_all_prime_return_projection434 _ _ _ _ _ _ _ _ _ _ _ _ _ _
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityOperator -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

abbrev B654ActualParityState434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) :=
  B650IntegerPhysicalState434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions

/-- The complete actual r20 source physical matrix. Its coefficient is
the original RAW-plus-comparison Knu with every original parameter. -/
def b654ActualParityPhysicalMatrix434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (positions : Finset ℤ) :
    Matrix (B654ActualParityState434 L hS J positions)
      (B654ActualParityState434 L hS J positions) ℂ := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact b650IntegerPhysicalMatrix434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta 1 shift

def b654ActualParityPhysicalOperator434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (positions : Finset ℤ) :
    EuclideanSpace ℂ (B654ActualParityState434 L hS J positions) →ₗ[ℂ]
      EuclideanSpace ℂ (B654ActualParityState434 L hS J positions) :=
  (b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta shift positions).toEuclideanLin

/-- All original physical marks at n, with BOTH original harmonic
normalizations and with no normalization of the mark fibre itself. -/
def b654ActualParityPositionRoot434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (n : ℤ) :
    EuclideanSpace ℂ (B654ActualParityState434 L hS J positions) :=
  b650IntegerPhysicalRoot434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions
    (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) n

/-- The original physical positive-operator moment sum over the long
seed interval, with free terminal marks and the same source operator. -/
def b654ActualParityPhysicalMomentSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (positions : Finset ℤ) (R lo hi : ℕ) : ℂ :=
  let A := b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta shift positions
  ∑ n ∈ Finset.Ico lo hi,
    let u := b654ActualParityPositionRoot434 L hS J positions (n:ℤ)
    inner ℂ u (((A.comp A.adjoint)^R) u)

/-- Positivity of the ACTUAL original group masses, derived from the
proved reciprocal-prime lower bound rather than left as a domain premise. -/
theorem b654_eventually_actual_parity_masses_positive434 :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty,
        (∀ g, 0 < SourceNativeMemorySmallMass434 20 L hS g) ∧
        (∀ g, 0 < sourceNativeOriginalVbig434 20 L g) := by
  have hv : 0 < Real.log (6/5:ℝ)/2 :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num)] with L hMass
  refine ⟨hMass.1,hMass.2.1,?_⟩
  intro hS
  constructor
  · intro g
    cases g with
    | none => exact hv.trans_le (hMass.2.2 hS).1.1
    | some i => exact hv.trans_le ((hMass.2.2 hS).2.1 i).1
  · intro g
    exact hv.trans_le ((hMass.2.2 hS).2.2 g).1
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParitySchur -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 18000

/-- The literal full original r20 physical matrix has polynomial absolute
rows AND columns, uniformly in ALL real frequencies and arbitrary finite
integer carriers. C is fixed after J,m,Cq,Cxi and before L. Only original
Q,h,xi parameter budgets occur; the actual arithmetic mass/group/cap
facts are proved inside the theorem. This is an error budget only. -/
theorem b661_eventually_actual_parity_absolute_rows_columns434
    (J m Cq Cxi : ℕ) (hmJ : m ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      0 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (Q : ℕ) (h xi : ℝ),
        (Q:ℝ) ≤ L^Cq → 0 < h → 0 < xi → xi⁻¹ ≤ L^Cxi →
      ∀ (zeta : ℝ) (k : ℤ) (positions : Finset ℤ),
        (∀ x : B654ActualParityState434 L hS J positions,
          (∑ y : B654ActualParityState434 L hS J positions,
            ‖b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions x y‖) ≤ L^C) ∧
        (∀ y : B654ActualParityState434 L hS J positions,
          (∑ x : B654ActualParityState434 L hS J positions,
            ‖b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions x y‖) ≤ L^C) := by
  let v : ℝ := Real.log (6/5:ℝ)/2
  let C0 : ℝ := 4+(Real.log 2)⁻¹
  let B : ℝ := b644RawComparisonExponent434 (J+1) m Cq Cxi (1/2:ℝ) v C0
  let C := max 0 B
  have hv : 0 < v := ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hC0 : 0 ≤ C0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C0]
    positivity
  refine ⟨C,le_max_left _ _,?_⟩
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (2:ℝ)] with L hMass hexp hL2
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  refine ⟨hL0,hMass.2.1,?_⟩
  intro hS Q h xi hQ hh hxi hXi zeta k positions
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let Vs := SourceNativeMemorySmallMass434 20 L hS
  let Vb := sourceNativeOriginalVbig434 20 L
  let blockA := sourceNativeOriginalBigBlockA434 20 L
  let blockB := sourceNativeOriginalBigBlockB434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) Vb blockA blockB
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let Kcap := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  have hVs (g) : v ≤ Vs g := by
    cases g with
    | none => exact (hMass.2.2 hS).1.1
    | some i => exact ((hMass.2.2 hS).2.1 i).1
  have hVb (g) : v ≤ Vb g := ((hMass.2.2 hS).2.2 g).1
  have hVs0 (g) : 0 < Vs g := hv.trans_le (hVs g)
  have hVb0 (g) : 0 < Vb g := hv.trans_le (hVb g)
  have hHb (g) : (∑ p : BP g, 1/(p.val:ℝ)) = Vb g := by
    simpa [Vb,BP,sourceNativeOriginalVbig434,SourceNativeMemoryBP434,one_div] using
      Finset.sum_attach (sourceNativeOriginalTb434 20 L g) (fun p => (p:ℝ)⁻¹)
  have hcounts := source_native_original_group_upper_counts434 20 L hS (by norm_num) hexp
  have hGs : (Fintype.card (SourceNativeMemorySG434 20 L hS):ℝ) ≤ C0*Real.log L := by
    simp only [SourceNativeMemorySG434,Fintype.card_option,Nat.cast_add,Nat.cast_one]
    dsimp [C0]
    nlinarith [hcounts.1]
  have hGb : (Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ) ≤ C0*Real.log L := by
    dsimp [C0]
    nlinarith [hcounts.2]
  have hK0 (nu) : 0 ≤ Kcap nu :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu
  have hK (nu aux s t) : ‖Knu nu aux s t‖ ≤ Kcap nu :=
    source_original_memory_RAW_COMPARISON_K_cap434
      (sourceNativeOriginalTb434 20 L) Vb blockA blockB J 1 m hmJ Q
      (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi nu aux s t
  let cost := b644IndependentRowBudget434 J 1 m pats (1/2:ℝ) Vs Vb Kcap
  have hcost : cost ≤ L^B :=
    b644_raw_comparison_absolute_row_polynomial434 blockA blockB J 1 m Q Cq Cxi hmJ
      (1/2:ℝ) v C0 L xi (by norm_num) (by norm_num) hv hC0 hL2 hxi
      Vs Vb hVs hVb hGs hGb hQ hXi
  have hcostC : cost ≤ L^C :=
    hcost.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
  constructor
  · intro x
    exact (b661_physical_matrix_absolute_row434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats positions
      (1/2:ℝ) Vs Vb (by norm_num) (by norm_num) hVs0 hVb0 hHb
      Knu Kcap hK0 hK zeta 1 (2*k) x).trans hcostC
  · intro y
    exact (b661_physical_matrix_absolute_column434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats positions
      (1/2:ℝ) Vs Vb (by norm_num) (by norm_num) hVs0 hVb0 hHb
      Knu Kcap hK0 hK zeta (2*k) y).trans hcostC

/-- Source-exact physical Schur bound for Fourier tails. The entire
operator and bilinear form are controlled uniformly for EVERY real zeta,
every finite physical carrier and every integer shift 2k. No Schur/row/
column/mass/cap hypothesis remains; C depends on J,m,Cq,Cxi before L.
This polynomial bound is not a signed saving or a D20-mass assertion. -/
theorem b661_eventually_actual_parity_uniform_schur434
    (J m Cq Cxi : ℕ) (hmJ : m ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      0 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (Q : ℕ) (h xi : ℝ),
        (Q:ℝ) ≤ L^Cq → 0 < h → 0 < xi → xi⁻¹ ≤ L^Cxi →
      ∀ (zeta : ℝ) (k : ℤ) (positions : Finset ℤ),
        (∀ g : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions),
          ‖b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta (2*k) positions g‖ ≤
            L^C*‖g‖) ∧
        (∀ f g : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions),
          ‖inner ℂ f (b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta (2*k) positions g)‖ ≤
            L^C*‖f‖*‖g‖) := by
  obtain ⟨C,hC,hRows⟩ := b661_eventually_actual_parity_absolute_rows_columns434 J m Cq Cxi hmJ
  refine ⟨C,hC,?_⟩
  filter_upwards [hRows] with L hRows
  refine ⟨hRows.1,hRows.2.1,?_⟩
  intro hS Q h xi hQ hh hxi hXi zeta k positions
  obtain ⟨hr,hc⟩ := hRows.2.2 hS Q h xi hQ hh hxi hXi zeta k positions
  have hLC : 0 ≤ L^C := Real.rpow_nonneg hRows.1.le _
  constructor
  · intro g
    exact b661_finite_matrix_schur_norm434
      (b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions)
      (L^C) hLC hr hc g
  · intro f g
    exact b661_finite_matrix_schur_pairing434
      (b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions)
      (L^C) hLC hr hc f g
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualMomentReturn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 18000

/-- Exact moment of the COMPLETE actual source physical operator equals
the unrestricted signed return sum already estimated by B648. Every path
from the seed interval fits in the proved enlarged window, so no signed
path or terminal mark is discarded. All canonical Knu and both original
mark masses are the same on the two sides. -/
theorem b654_actual_parity_moment_eq_return434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (lo hi : ℕ)
    (hVs : ∀ g, 0 < SourceNativeMemorySmallMass434 20 L hS g)
    (hVb : ∀ g, 0 < sourceNativeOriginalVbig434 20 L g) :
    b654ActualParityPhysicalMomentSum434 L hS J m hmJ Q h xi zeta (2*k)
      (b654ParityIntervalWindow434 J Ck L lo hi)
      (Nat.ceil (L^(13/25:ℝ))) lo hi =
    b648ActualParityReturnPathSum434 L hS J m hmJ Q h xi zeta (2*k)
      (2*Nat.ceil (L^(13/25:ℝ))) lo hi := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let R := Nat.ceil (L^(13/25:ℝ))
  let N := 2*R
  let positions := b654ParityIntervalWindow434 J Ck L lo hi
  let Ω := B643AllPrimePath434 SP BP J 1 m pats N
  let off : Ω → ℕ → ℤ := fun ω =>
    b643AllPrimeOffset434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats ω (2*k)
  let W : Ω → ℂ := b643AllPrimeWeight434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta 0 (2*k)
  let density : Ω → ℕ → ℝ := fun ω => b645ActualMarkedPathDensity434 L hS (J+1) N
    (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) (off ω)
  let A := b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta (2*k) positions
  let u := b654ActualParityPositionRoot434 L hS J positions
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hL
  have hR : 0 < R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans hL1) _)
  have hN : 0 < N := by dsimp [N]; omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ico lo hi) :
      inner ℂ (u (n:ℤ)) (((A.comp A.adjoint)^R) (u (n:ℤ))) =
        ∑ ω : Ω, if off ω N=0 then W ω*(density ω n:ℂ) else 0 := by
    have h0 := b650_physical_root_moment_array434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats positions
      (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) hVs hVb Knu zeta (2*k) R (n:ℤ)
    have h1 := b653_actual_parity_physical_return434 L hL1 hS J 1 m pats
      positions N hN n (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta (2*k)
    have hh := h0.trans h1
    change inner ℂ (u (n:ℤ)) (((A.comp A.adjoint)^R) (u (n:ℤ))) =
      ∑ ω : Ω, if (∀ t : Fin (N+1), (n:ℤ)+off ω t.val ∈ positions) ∧ off ω N=0 then
        W ω*(density ω n:ℂ) else 0 at hh
    refine hh.trans ?_
    apply Finset.sum_congr rfl
    intro ω hω
    have hw : ∀ t : Fin (N+1), (n:ℤ)+off ω t.val ∈ positions := by
      intro t
      exact b654_actual_parity_path_in_interval_window434 J m Ck L hL hS pats ω k hk lo hi n hn t.val
    simp [hw]
  calc
    _ = ∑ n ∈ Finset.Ico lo hi, ∑ ω : Ω,
        if off ω N=0 then W ω*(density ω n:ℂ) else 0 := by
      unfold b654ActualParityPhysicalMomentSum434
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n hn
    _ = _ := by
      unfold b648ActualParityReturnPathSum434
      change (∑ n ∈ Finset.Ico lo hi, ∑ ω : Ω,
        if off ω N=0 then W ω*(density ω n:ℂ) else 0) =
        ∑ ω : Ω, if off ω N=0 then W ω*((∑ n ∈ Finset.Ico lo hi,density ω n : ℝ):ℂ) else 0
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hr : off ω N=0
      · simp only [hr,ite_true,Complex.ofReal_sum,Finset.mul_sum]
      · simp only [hr,ite_false,Finset.sum_const_zero]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityLocality -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The literal original RAW-plus-comparison physical matrix is local
in integer position. The bound is proved for each primitive frame from
its actual shift 2kD and the full-prime D cap; no support, mass or RMS
hypothesis is supplied. -/
theorem b655_actual_parity_matrix_locality434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (positions : Finset ℤ)
    (x y : B654ActualParityState434 L hS J positions)
    (hxy : b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions x y ≠ 0) :
    |y.val.1.val-x.val.1.val| ≤ (b651ParityWindowSize434 J Ck L:ℤ) := by
  classical
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let F := MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats
  let scalar : F → ℂ := fun f =>
    b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y f
  have hex : ∃ f : F, scalar f ≠ 0 := by
    by_contra! hh
    apply hxy
    change (∑ f : F, scalar f)=0
    exact Finset.sum_eq_zero fun f _ => hh f
  obtain ⟨f,hf⟩ := hex
  have ha : b650IntegerFrameAllowed434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats positions 1 (2*k) x y f := by
    by_contra hn
    exact hf (by simp [scalar,b650IntegerFrameScalar434,hn])
  let ω := b643AllPrimePathOf434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats (fun _ : Fin 2 => x.val.2) (fun _ : Fin 1 => f)
  have hD := b651_actual_parity_shift_D_cap434 J m Ck L hL hS pats ω 0 k hk
  have hoff : y.val.1.val-x.val.1.val =
      2*k*(b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats x.val.2 f : ℤ) := by
    rw [ha.2.2.2.2]
    ring
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hW := b651_parity_maxstep_window_bounds434 J Ck L hL1
  have hb : |((y.val.1.val-x.val.1.val:ℤ):ℝ)| ≤
      (b651ParityWindowSize434 J Ck L:ℝ) := by
    rw [hoff]
    exact hD.trans (hW.1.trans hW.2)
  exact_mod_cast hb
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CofinalPositiveRAW -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The original r=6 full-G Ptw four-sign harmonic reference is
EXACTLY ONE on the REAL cofinal geometric scales
L_N=((3/2)*2^N)^10 when the original fixed shared slot J is ODD.
This uses the full actual independently chosen SMALL S/Ts and
BIG Tb group geometry, with N+1 SMALL and N BIG groups.
No new dyadic P family or assumed matching number of groups. -/
theorem eventually_native_r6_COFINAL_ODD_J_full_Ptw_ref_one434
    (J : ℕ) (hJ : Odd J) :
    ∀ᶠ N : ℕ in atTop,
      sourceNativeOriginalALLPJTrueProjectedRef434 6
        (sourceNativeR6CofinalL434 N) J
        (sourceNativeOriginalG434 6
          (sourceNativeR6CofinalL434 N)) = 1 := by
  have hT := (source_native_r6_cofinal_L_tendsto_atTop434).eventually
    (eventually_source_native_CANONICAL_FULL_Ptw_ref434 6 J)
  filter_upwards [hT] with N hN
  rw [hN.2]
  have hCount := source_native_r6_cofinal_ALL_P_odd434 N
  have hSign : (-1:ℂ)^(J*Fintype.card
      (SourceNativeOriginalAllP434 6 (sourceNativeR6CofinalL434 N))) = -1 :=
    (hJ.mul hCount).neg_one_pow
  rw [hSign]
  norm_num

/-- A real mathematical positive LOCAL scalar baseline:
on original r=6 source P groups, at infinitely many (cofinal)
geometric L_N, for EVERY actual full S/Ts/Tb source J0-fold
harmonic/physical B26 auxiliary pattern, original nonempty
free-mark endpoint sets A,B, and original endpoint sizes,
the TRUE four-sign full-G projected RAW common-J coefficient
satisfies
   |RAW_phase_projected - 1| <= L_N^(-D)
for arbitrary fixed accuracy D.

The original J0 is ODD and chosen BEFORE N and independent of
the source free-mark cap mmax. This does NOT assert the complete
B8/CRT/OLD/Fock ROOT source operator equals this finite common-J
scalar, NOR that unconditional Type II or prime positivity follows.
It removes the purely arithmetic "parity could make the
baseline zero" issue on a genuine original cofinal subsequence. -/
theorem eventually_native_r6_COFINAL_ODD_J_TRUE_RAW_one434
    (J0 mmax : ℕ) (hJ : Odd J0) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp 1 ≤ sourceNativeR6CofinalL434 N ∧
      ∀ (m : ℕ)
        (pat : SourcePattern
          (sourceNativeOriginalBigType434 6
            (sourceNativeR6CofinalL434 N)) J0 m)
        (aux : SourceBigAux
          (SourceNativeMemoryBP434 6
            (sourceNativeR6CofinalL434 N)) J0 m pat),
      m ≤ mmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*sourceNativeR6CofinalL434 N) →
      (wp:ℝ) ≤ Real.exp (2*sourceNativeR6CofinalL434 N) →
      ∀ (A B : SourceNativeOriginalAllP434 6
        (sourceNativeR6CofinalL434 N) → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ‖sourceNativeOriginalALLPJTrueProjectedRAW434
        6 (sourceNativeR6CofinalL434 N) J0
        (sourceNativeOriginalG434 6 (sourceNativeR6CofinalL434 N))
        A B - 1‖ ≤
      (sourceNativeR6CofinalL434 N)^(-D) := by
  classical
  have hT := (source_native_r6_cofinal_L_tendsto_atTop434).eventually
    (eventually_native_original_CANONICAL_FULL_TWIST_RAW434
      6 (by norm_num) J0 mmax D)
  filter_upwards [hT] with N hRaw
  refine ⟨hRaw.1, ?_⟩
  intro m pat aux hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend
  have hBound := hRaw.2 m pat aux hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend
  have hCount := source_native_r6_cofinal_ALL_P_odd434 N
  have hSign : (-1:ℂ)^(J0*Fintype.card
      (SourceNativeOriginalAllP434 6 (sourceNativeR6CofinalL434 N))) = -1 :=
    (hJ.mul hCount).neg_one_pow
  simp only [hSign] at hBound
  norm_num at hBound
  exact hBound
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeFullPNonvacuousEndpoint -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64ComparisonPartial Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The ORIGINAL entire S/Ts/Tb P-bands admit a genuine
simultaneous single PRIME divisor at every group and positive
ordinary endpoint w <= exp(2L), uniformly for all sufficiently
large L. This checks the REAL nonvacuity of the original
RAW J=1 free-endpoint prime-mark requirements.

The constructed w is the integer product of a CHOSEN actual
prime from each original source P group, with duplicates and
multiplicities retained. It is bounded by the previously
kernel-certified original ALL-P J=1 shared-product cap; the
subexponential scale is absorbed below the source upper
endpoint exp(2L), not assumed. -/
theorem eventually_native_original_ALL_P_endpoint_marks_nonempty434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∃ (w : ℕ)
        (A : SourceNativeOriginalAllP434 r L → Finset ℕ),
        0 < w ∧ (w:ℝ) ≤ Real.exp (2*L) ∧
        (∀ g, 0 < (A g).card) ∧
        (∀ g, A g ⊆ w.primeFactors) := by
  classical
  let C : ℝ := 3+(Real.log 2)⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
    eventually_native_original_ALL_P_masses434 r,
    eventually_native_original_ALL_P_J_divisor_cap434 r hr 1,
    eventually_clean_cofactor_growth434 C (1/2) hC
      (by norm_num : (0:ℝ)<(1/2:ℝ)),
    eventually_ge_atTop (Real.exp 1)] with L hMass hDiv hGrow hL
  refine ⟨hL, ?_⟩
  let G := SourceNativeOriginalAllP434 r L
  let S : G → Finset ℕ := fun g => SourceNativeOriginalAllPBand434 r L g
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hV : ∀ g : G, 0 < sourceNativeOriginalAllPMass434 r L g := by
    intro g
    exact ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive.trans_le
      (hMass g).1
  have hS : ∀ g : G, (S g).Nonempty := by
    intro g
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hval := hV g
    have he' : SourceNativeOriginalAllPBand434 r L g = ∅ := he
    unfold sourceNativeOriginalAllPMass434 at hval
    simp [he'] at hval
  let p : G → ℕ := fun g => (S g).min' (hS g)
  have hp : ∀ g : G, p g ∈ S g := fun g => Finset.min'_mem _ _
  have hprime : ∀ g : G, (p g).Prime := by
    intro g
    exact (source_native_original_ALL_P_prime_range434 r L
      hL1 g (p g) (hp g)).1
  let w : ℕ := ∏ g : G, p g
  let A : G → Finset ℕ := fun g => {p g}
  have hwpos : 0 < w := by
    dsimp [w]
    apply Finset.prod_pos
    intro g hg
    exact (hprime g).pos
  have hAS : ∀ g : G, 0 < (A g).card := by
    intro g
    simp [A]
  have hAdiv : ∀ g : G, A g ⊆ w.primeFactors := by
    intro g x hx
    have hx' : x=p g := Finset.mem_singleton.mp hx
    subst x
    apply Nat.mem_primeFactors.mpr
    refine ⟨hprime g, ?_, Nat.ne_of_gt hwpos⟩
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ g)
  let s : G × Fin 1 → ℕ := fun gi => p gi.1
  have hs : s ∈ Fintype.piFinset
      (fun gi : G × Fin 1 =>
        SourceNativeOriginalAllPBand434 r L gi.1) := by
    apply Fintype.mem_piFinset.mpr
    intro gi
    exact hp gi.1
  have hwprod : sourceNativeOriginalAllPCommonDivisor434 r L 1 s = w := by
    unfold sourceNativeOriginalAllPCommonDivisor434
    rw [Fintype.prod_prod_type]
    simp only [s]
    change (∏ g : G, ∏ k : Fin 1, p g) = (∏ g : G, p g)
    simp
  have hDcap : (w:ℝ) ≤ Real.exp (C*L^(2/5:ℝ)*Real.log L) := by
    have hh := hDiv.2 s hs
    simpa [C,hwprod,one_mul] using hh
  have hLog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hP : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg (by linarith : (0:ℝ)≤L) _
  have hExpPos : 0 ≤ C*L^(2/5:ℝ)*Real.log L :=
    mul_nonneg (mul_nonneg hC hP) hLog
  have hGrow1 : Real.exp (C*L^(2/5:ℝ)*Real.log L) ≤
      Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hExpPos]
  have hBig : Real.exp (2*C*L^(2/5:ℝ)*Real.log L) ≤
      8*Real.exp L*L^(2*C)*
        Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
    have he : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hPow : 1 ≤ L^(2*C) := Real.one_le_rpow hL1 (by linarith)
    have hh : 1 ≤ 8*Real.exp L*L^(2*C) := by
      nlinarith [mul_le_mul_of_nonneg_left hPow
        (by positivity : 0 ≤ 8*Real.exp L)]
    have hx : 0 ≤ Real.exp (2*C*L^(2/5:ℝ)*Real.log L) :=
      (Real.exp_pos _).le
    have hh' := mul_le_mul_of_nonneg_right hh hx
    nlinarith [hh']
  have hWupper : (w:ℝ) ≤ Real.exp (2*L) := by
    apply le_of_lt
    calc
      (w:ℝ) ≤ Real.exp (C*L^(2/5:ℝ)*Real.log L) := hDcap
      _ ≤ Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := hGrow1
      _ ≤ 8*Real.exp L*L^(2*C)*
          Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := hBig
      _ < Real.exp (2*L) := by
        convert hGrow using 1 <;> ring
  exact ⟨w,A,hwpos,hWupper,hAS,hAdiv⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeActualTwoPPrimes -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- For the ORIGINAL source S/Ts/Tb closed dyadic P prime bands,
all original harmonic masses have a fixed positive vmin, while
every individual source P prime is >= exp(L^(1/10)).
Consequently for all sufficiently large REAL L each ORIGINAL
P-group contains at least TWO DISTINCT actual prime values.

The original prime family, every SMALL and BIG interval, exact
source cutoff and the independent prime support are unchanged.
This is necessary for constructing a TRUE nonempty BIG free
auxiliary that avoids its endpoint mark; a mere nonempty band
or a dummy auxiliary would not suffice. -/
theorem eventually_native_original_ALL_P_two_distinct_primes434
    (r : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ g : SourceNativeOriginalAllP434 r L,
        1 < (SourceNativeOriginalAllPBand434 r L g).card := by
  classical
  let vmin : ℝ := Real.log (6/5:ℝ)/2
  have hv : 0 < vmin := by
    dsimp [vmin]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hGrow :
      Tendsto (fun L : ℝ => Real.exp (L^(1/10:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<(1/10:ℝ)))
  filter_upwards [
    eventually_native_original_ALL_P_masses434 r,
    hGrow.eventually (eventually_gt_atTop ((1:ℝ)/vmin)),
    eventually_ge_atTop (1:ℝ)] with L hMass hHuge hL
  refine ⟨hL, ?_⟩
  intro g
  let band := SourceNativeOriginalAllPBand434 r L g
  have hMassLower : vmin ≤ ∑ p ∈ band, (1:ℝ)/(p:ℝ) := by
    exact (hMass g).1
  have hCardPos : 0 < band.card := by
    by_contra hn
    have hz : band.card=0 := by omega
    have hempty : band = ∅ := Finset.card_eq_zero.mp hz
    simp [hempty] at hMassLower
    linarith [hv]
  by_contra hAtMost
  change ¬ 1 < band.card at hAtMost
  have hCardOne : band.card=1 := by omega
  obtain ⟨p,hSingleton⟩ := Finset.card_eq_one.mp hCardOne
  have hpMem : p ∈ band := by rw [hSingleton]; simp
  have hpRange := source_native_original_ALL_P_prime_range434
    r L hL g p hpMem
  have hpPos : (0:ℝ)<p := by exact_mod_cast hpRange.1.pos
  have hSmall : vmin ≤ (1:ℝ)/(p:ℝ) := by
    simpa [hSingleton] using hMassLower
  have hLower : Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) := hpRange.2.1
  have hLarge : (1:ℝ)<vmin*(p:ℝ) := by
    have he : (1:ℝ)<vmin*Real.exp (L^(1/10:ℝ)) := by
      have ht := (div_lt_iff₀ hv).mp hHuge
      nlinarith [ht]
    nlinarith [mul_le_mul_of_nonneg_left hLower hv.le]
  have hUpper : vmin*(p:ℝ)≤1 :=
    (le_div_iff₀ hpPos).mp hSmall
  linarith
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalSlice -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ACTUAL original SOURCE03 canonical r=6 prime slice from the
real original P-index geometry along the cofinal geometric scales.
Both source option SMALL S/Ts and BIG Tb families are reindexed
EXACTLY as Option(Fin N) and Fin N, with no inserted/removed
primes, genuine harmonic V and exact BIG prime intervals.

At a fixed L_N this constructor requires only the ALREADY
PROVED original all-P prime harmonic floors and at least two
source primes per group. Both are discharged asymptotically
in the exported theorem below. The fixed comparison config's
arithmetic exponent fields are exactly those of the actual
sourceNativeOriginalR6Fixed434 configuration. It constructs
the genuine canonical prime-slice, NOT the entire
SourceComparisonData434 endpoint or Fock/CRT/OLD operator. -/
noncomputable def source_native_r6_original_canonical_prime_slice434
    (N : ℕ) (hN : 1 ≤ N)
    (cfg : SourceComparisonFixed434)
    (ha : cfg.aexp = 1/10)
    (hb : cfg.bexp = 1/5)
    (hc : cfg.cexp = 3/10)
    (hC0 : cfg.C0 = 4)
    (hv : cfg.vmin = Real.log (6/5:ℝ)/2)
    (hMass : ∀ g : SourceNativeOriginalAllP434 6
        (sourceNativeR6CofinalL434 N),
        Real.log (6/5:ℝ)/2 ≤
          sourceNativeOriginalAllPMass434 6
            (sourceNativeR6CofinalL434 N) g ∧
          sourceNativeOriginalAllPMass434 6
            (sourceNativeR6CofinalL434 N) g ≤ 4)
    (hTwo : ∀ g : SourceNativeOriginalAllP434 6
        (sourceNativeR6CofinalL434 N),
        1 < (SourceNativeOriginalAllPBand434 6
          (sourceNativeR6CofinalL434 N) g).card) :
    SourceOriginalSource03CanonicalPrimeSlice434
      N cfg (sourceNativeR6CofinalL434 N) (2/5) 5 1 := by
  classical
  let L := sourceNativeR6CofinalL434 N
  let e := source_native_r6_cofinal_canonical_full_equiv434 N
  let eb := source_native_r6_cofinal_Tb_Fin_equiv434 N
  let P : Option (Fin N) → Finset ℕ :=
    source_native_r6_canonical_P434 N
  let Tb : Fin N → Finset ℕ := source_native_r6_canonical_Tb434 N
  let V : Option (Fin N) → ℝ := fun g =>
    ∑ p ∈ P g, (1:ℝ)/(p:ℝ)
  let lo : Fin N → ℕ := fun i =>
    sourceNativeOriginalBigLo434 6 L (eb i)
  let hi : Fin N → ℕ := fun i =>
    sourceNativeOriginalBigHi434 6 L (eb i)
  have hsmall : 0 < Real.log (6/5:ℝ)/2 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hLgt : 1 < L := by
    have hu : (1:ℝ) < sourceNativeR6CofinalRoot434 N := by
      unfold sourceNativeR6CofinalRoot434
      have hpow : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
      nlinarith
    unfold L sourceNativeR6CofinalL434
    exact one_lt_pow₀ hu (by norm_num : (10:ℕ) ≠ 0)
  have hL1 : 1 ≤ L := hLgt.le
  have hLog : 0 < Real.log L := Real.log_pos hLgt
  have hSmallLog : (N:ℝ) ≤ cfg.C0*Real.log L := by
    rw [hC0]
    exact source_native_r6_cofinal_n_log_budget434 N
  have hTcounts : ((N+1:ℕ):ℝ) ≤ cfg.C0*(N:ℝ) := by
    rw [hC0]
    have hh : 1 ≤ N := hN
    exact_mod_cast (show N+1 ≤ 4*N by omega)
  have hSmallNonempty : ∀ g : Option (Fin N), (P g).Nonempty := by
    intro g
    have hc := hTwo (e (Sum.inl g))
    apply Finset.card_pos.mp
    change 1 < (P g).card at hc
    omega
  have hBigNonempty : ∀ i : Fin N, (Tb i).Nonempty := by
    intro i
    have hc := hTwo (e (Sum.inr i))
    apply Finset.card_pos.mp
    change 1 < (Tb i).card at hc
    omega
  have hBigRoot (i : Fin N) :
      Tb i = sourceOriginalActualPrimeBand434 (lo i) (hi i) :=
    (source_native_original_BIG_root_band_fields434
      6 L hL1 (eb i)).1
  have hPsource (g : Option (Fin N)) :
      P g = SourceNativeOriginalAllPBand434 6 L
        (e (Sum.inl g)) := rfl
  have hTbsource (i : Fin N) :
      Tb i = SourceNativeOriginalAllPBand434 6 L
        (e (Sum.inr i)) := rfl
  have hPrime : ∀ g : Option (Fin N), ∀ p ∈ P g,
      p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(1/5:ℝ)) := by
    intro g p hp
    cases g with
    | none =>
      change p ∈ source_native_r6_canonical_P434 N none at hp
      rw [source_native_r6_canonical_P_none_real_S434] at hp
      exact source_native_original_S_prime_range434 6 L
        (source_native_r6_cofinal_SMALL_nonempty434 N) p hp
    | some i =>
      change p ∈ source_native_r6_canonical_P434 N (some i) at hp
      rw [source_native_r6_canonical_P_some_real_Ts434] at hp
      exact source_native_original_Ts_prime_range434 6 L
        (source_native_r6_cofinal_SMALL_nonempty434 N)
        (source_native_r6_cofinal_Ts_Fin_equiv434 N i) p hp
  have hPmass : ∀ g : Option (Fin N),
      Real.log (6/5:ℝ)/2 ≤ V g ∧ V g ≤ 4 := by
    intro g
    have h := hMass (e (Sum.inl g))
    change Real.log (6/5:ℝ)/2 ≤ (∑ p ∈ P g,(1:ℝ)/(p:ℝ)) ∧
      (∑ p ∈ P g,(1:ℝ)/(p:ℝ)) ≤ 4 at h
    exact h
  have hBmass : ∀ i : Fin N,
      Real.log (6/5:ℝ)/2 ≤
        sourceOriginalPrimeBandHarmonicMass434 (lo i) (hi i) ∧
      sourceOriginalPrimeBandHarmonicMass434 (lo i) (hi i) ≤ 4 := by
    intro i
    have h := hMass (e (Sum.inr i))
    change Real.log (6/5:ℝ)/2 ≤ (∑ p ∈ Tb i,(1:ℝ)/(p:ℝ)) ∧
      (∑ p ∈ Tb i,(1:ℝ)/(p:ℝ)) ≤ 4 at h
    simpa only [hBigRoot i,sourceOriginalPrimeBandHarmonicMass434] using h
  have hBigRange : ∀ i : Fin N, ∀ p ∈
      sourceOriginalActualPrimeBand434 (lo i) (hi i),
      p.Prime ∧ Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
    intro i p hp
    rw [←hBigRoot i] at hp
    change p ∈ source_native_r6_canonical_Tb434 N i at hp
    rw [source_native_r6_canonical_Tb_real_Tb434] at hp
    exact source_native_original_Tb_prime_range434
      6 L (eb i) p hp
  have hOrdered : ∀ i : Fin N, lo i < hi i := by
    intro i
    obtain ⟨p,hp⟩ := hBigNonempty i
    have hMem : p ∈ sourceOriginalActualPrimeBand434 (lo i) (hi i) := by
      rw [←hBigRoot i]
      exact hp
    have hInterval := (Finset.mem_filter.mp hMem).1
    have hiInterval := Finset.mem_Ioc.mp hInterval
    omega
  have hDisj := source_original_P_actual_all_disjoint 6 L
    (by norm_num) (by linarith : (0:ℝ)<L)
  have hSS : ∀ g h : Option (Fin N), g≠h → Disjoint (P g) (P h) := by
    intro g h hne
    apply Finset.disjoint_left.mpr
    intro p hp hph
    have hgroup := hDisj (e (Sum.inl g)) (e (Sum.inl h))
      p (by change p ∈ P g; exact hp)
        (by change p ∈ P h; exact hph)
    have hg : Sum.inl g = (Sum.inl h : Option (Fin N) ⊕ Fin N) :=
      e.injective hgroup
    exact hne (Sum.inl.inj hg)
  have hBB : ∀ i j : Fin N, i≠j →
      Disjoint (sourceOriginalActualPrimeBand434 (lo i) (hi i))
        (sourceOriginalActualPrimeBand434 (lo j) (hi j)) := by
    intro i j hne
    apply Finset.disjoint_left.mpr
    intro p hp hpj
    have hgroup := hDisj (e (Sum.inr i)) (e (Sum.inr j))
      p (by change p ∈ Tb i; rw [hBigRoot i]; exact hp)
        (by change p ∈ Tb j; rw [hBigRoot j]; exact hpj)
    have hg : Sum.inr i = (Sum.inr j : Option (Fin N) ⊕ Fin N) :=
      e.injective hgroup
    exact hne (Sum.inr.inj hg)
  have hSB : ∀ g : Option (Fin N), ∀ i : Fin N,
      Disjoint (P g) (sourceOriginalActualPrimeBand434 (lo i) (hi i)) := by
    intro g i
    apply Finset.disjoint_left.mpr
    intro p hp hpi
    have hgroup := hDisj (e (Sum.inl g)) (e (Sum.inr i))
      p (by change p ∈ P g; exact hp)
        (by change p ∈ Tb i; rw [hBigRoot i]; exact hpi)
    have hg : Sum.inl g = (Sum.inr i : Option (Fin N) ⊕ Fin N) :=
      e.injective hgroup
    cases hg
  exact {
    T := N
    P := P
    V := V
    left := lo
    right := hi
    hTpos := hN
    hTlog := hLog
    hTlower := by exact_mod_cast hN
    hTcountsLow := by norm_num
    hTcountsHigh := hTcounts
    hSmallLog := hSmallLog
    hBigLog := hSmallLog
    hSmallNonempty := hSmallNonempty
    hSmallBand := by
      intro g p hp
      rw [ha,hb]
      exact hPrime g p hp
    hSmallHarmonic := fun g => rfl
    hSmallMass := by
      intro g
      have h := hPmass g
      rw [hv]
      exact ⟨h.1,h.2.trans_lt (by norm_num)⟩
    hBigOrdered := hOrdered
    hBigBand := by
      intro i p hp
      rw [hc]
      exact hBigRange i p hp
    hBigMass := by
      intro i
      have h := hBmass i
      rw [hv]
      exact ⟨h.1,h.2.trans_lt (by norm_num)⟩
    hSS := hSS
    hBB := hBB
    hSB := hSB
  }
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeAllPSpareAuxiliary -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- TRUE source P-band disjointness + primality:
for a physical endpoint containing one chosen prime p_g in
EVERY original group g, another distinct prime q_g chosen from
the same group cannot divide the endpoint product w=prod_g p_g.

This checks a genuinely arithmetic part of the original
BIG free auxiliary ban; no invented dummy prime, no reweighting
and no declaration that the entire Fock edge is legal. -/
theorem source_native_original_all_P_spare_prime_excluded434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (p q : SourceNativeOriginalAllP434 r L → ℕ)
    (hp : ∀ g, p g ∈ SourceNativeOriginalAllPBand434 r L g)
    (hq : ∀ g, q g ∈ SourceNativeOriginalAllPBand434 r L g)
    (hNe : ∀ g, q g ≠ p g) :
    ∀ g, q g ∉
      (∏ h : SourceNativeOriginalAllP434 r L, p h).primeFactors := by
  classical
  let G := SourceNativeOriginalAllP434 r L
  intro g hMem
  have hPrimeQ : (q g).Prime :=
    (source_native_original_ALL_P_prime_range434
      r L hL g (q g) (hq g)).1
  have hDiv : q g ∣ (∏ h : G, p h) :=
    (Nat.mem_primeFactors.mp hMem).2.1
  obtain ⟨h,hh,hDivh⟩ :=
    (Prime.dvd_finsetProd_iff hPrimeQ.prime p).mp hDiv
  have hPrimeP : (p h).Prime :=
    (source_native_original_ALL_P_prime_range434
      r L hL h (p h) (hp h)).1
  have hEq : p h = q g :=
    (hPrimeP.dvd_iff_eq hPrimeQ.ne_one).mp hDivh
  have hGroup : g=h :=
    source_original_P_actual_all_disjoint r L hr
      (by linarith : 0<L) g h (q g) (hq g)
      (by simpa [hEq] using hp h)
  have hhNe : q g ≠ p g := hNe g
  apply hhNe
  simpa [hGroup] using hEq.symm

/-- For ALL sufficiently large L the real original S/Ts/Tb
prime family supports TWO actual independent selections:
p_g in each source P-band to create an ordinary endpoint w,
q_g in the same band for a potential nonempty BIG free auxiliary,
with each q_g forbidden from w because ALL source groups are
pairwise disjoint and all q_g != p_g. In particular every original
BIG group offers a real auxiliary prime avoiding endpoint P-divisors.

This does not assert the exact SOURCE03 OLD/CRT/Fock legality or
conditional SourceComparisonData434 Hprime fields. -/
theorem eventually_native_original_ALL_P_spare_auxiliary434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∃ (p q : SourceNativeOriginalAllP434 r L → ℕ),
        (∀ g, p g ∈ SourceNativeOriginalAllPBand434 r L g) ∧
        (∀ g, q g ∈ SourceNativeOriginalAllPBand434 r L g) ∧
        (∀ g, q g ≠ p g) ∧
        (∀ g, q g ∉ (∏ h : SourceNativeOriginalAllP434 r L, p h).primeFactors) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_two_distinct_primes434 r]
    with L hTwo
  refine ⟨hTwo.1, ?_⟩
  let G := SourceNativeOriginalAllP434 r L
  let S : G → Finset ℕ := fun g => SourceNativeOriginalAllPBand434 r L g
  have hpos : ∀ g : G, (S g).Nonempty := by
    intro g
    apply Finset.card_pos.mp
    have hc := hTwo.2 g
    dsimp only [S]
    omega
  let p : G → ℕ := fun g => (S g).min' (hpos g)
  have hp : ∀ g : G, p g ∈ S g := fun g => Finset.min'_mem _ _
  have hqpos : ∀ g : G, ((S g).erase (p g)).Nonempty := by
    intro g
    apply Finset.card_pos.mp
    have hc := Finset.card_erase_of_mem (hp g)
    have hTwoCard := hTwo.2 g
    change 1<(S g).card at hTwoCard
    omega
  let q : G → ℕ := fun g => ((S g).erase (p g)).min' (hqpos g)
  have hqMem : ∀ g : G, q g ∈ S g := by
    intro g
    exact (Finset.mem_erase.mp (Finset.min'_mem _ _)).2
  have hqNe : ∀ g : G, q g ≠ p g := by
    intro g
    exact (Finset.mem_erase.mp (Finset.min'_mem _ _)).1
  have hAvoid := source_native_original_all_P_spare_prime_excluded434
    r L hr hTwo.1 p q hp hqMem hqNe
  exact ⟨p,q,hp,hqMem,hqNe,hAvoid⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6NonvacuousPositiveRAW -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64ComparisonPartial Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The literal physical SOURCE03 dependent pattern with one
genuine common J=1 label in EVERY BIG Tb group and ZERO free
auxiliary slots. The source bound m=0 is exactly satisfied;
there is NO fake auxiliary prime or added dummy source branch. -/
noncomputable def source_native_actual_J1_m0_pattern434
    (r : ℕ) (L : ℝ) :
    SourcePattern (sourceNativeOriginalBigType434 r L) 1 0 where
  free := fun _ => ∅
  free_bound := by
    intro g
    simp

/-- The exact source free-BIG auxiliary type at m=0 is a
PRODUCT OVER EMPTY DEPENDENT SETS and has a genuine element.
No auxiliary prime chosen from an empty prime band. -/
noncomputable def source_native_actual_J1_m0_aux434
    (r : ℕ) (L : ℝ) :
    SourceBigAux (SourceNativeMemoryBP434 r L) 1 0
      (source_native_actual_J1_m0_pattern434 r L) := by
  intro g j
  have hj : False := by
    have h : j.val ∈
      (source_native_actual_J1_m0_pattern434 r L).free g := j.property
    simpa [source_native_actual_J1_m0_pattern434] using h
  exact False.elim hj

/-- On actual ORIGINAL cofinal r=6 P groups, a SINGLE explicit
nonempty family of source endpoint PRIME marks and a positive
integer w<=exp(2L_N) exists and satisfies every hypothesis of
the TRUE canonical full-G FOUR-SIGN unconditioned J=1 RAW
common-history scalar theorem. The original BIG free count m=0,
dependent pattern and empty independent aux ARE CONSTRUCTED,
not quantified vacuously.

For all sufficiently large N, the physical coefficient is
within L_N^-1 of the canonical baseline 1, and in particular
its REAL PART is >=1/2. This proves a genuinely NONVACUOUS
LOCAL signed RAW common-J scalar positivity at infinitely many
true source r=6 scales, but NOT the full SOURCE03 B8/CRT/OLD
Fock operator, D61 comparison-integral or Green64.green_64. -/
theorem eventually_native_r6_NONVACUOUS_J1_RAW_positive434 :
    ∀ᶠ N : ℕ in atTop,
      ∃ (w : ℕ)
        (A : SourceNativeOriginalAllP434 6
          (sourceNativeR6CofinalL434 N) → Finset ℕ),
        0 < w ∧
        (w:ℝ) ≤ Real.exp (2*sourceNativeR6CofinalL434 N) ∧
        (∀ g, 0 < (A g).card) ∧
        (∀ g, A g ⊆ w.primeFactors) ∧
        ‖sourceNativeOriginalALLPJTrueProjectedRAW434 6
            (sourceNativeR6CofinalL434 N) 1
            (sourceNativeOriginalG434 6
              (sourceNativeR6CofinalL434 N)) A A - 1‖ ≤
          (sourceNativeR6CofinalL434 N)^(-1:ℝ) ∧
        (1/2:ℝ) ≤
          (sourceNativeOriginalALLPJTrueProjectedRAW434 6
            (sourceNativeR6CofinalL434 N) 1
            (sourceNativeOriginalG434 6
              (sourceNativeR6CofinalL434 N)) A A).re := by
  classical
  have hCof := source_native_r6_cofinal_L_tendsto_atTop434
  filter_upwards [
    hCof.eventually (eventually_native_original_ALL_P_endpoint_marks_nonempty434
      6 (by norm_num)),
    eventually_native_r6_COFINAL_ODD_J_TRUE_RAW_one434
      1 0 (by norm_num : Odd 1) 1,
    hCof.eventually (eventually_ge_atTop (2:ℝ))]
    with N hEx hRaw hL2
  let L := sourceNativeR6CofinalL434 N
  obtain ⟨w,A,hw,hWcap,hApos,hAsub⟩ := hEx.2
  let pat : SourcePattern (sourceNativeOriginalBigType434 6 L) 1 0 :=
    source_native_actual_J1_m0_pattern434 6 L
  let aux : SourceBigAux (SourceNativeMemoryBP434 6 L) 1 0 pat :=
    source_native_actual_J1_m0_aux434 6 L
  let Z : ℂ := sourceNativeOriginalALLPJTrueProjectedRAW434
    6 L 1 (sourceNativeOriginalG434 6 L) A A
  have hZ : ‖Z-1‖ ≤ L^(-1:ℝ) :=
    hRaw.2 0 pat aux (by norm_num) w w hw hw
      hWcap hWcap A A hApos hApos hAsub hAsub
  have hLp : 0 < L := by linarith
  have hInv : L^(-1:ℝ) ≤ (1/2:ℝ) := by
    rw [Real.rpow_neg_one]
    rw [← one_div]
    apply (div_le_iff₀ hLp).mpr
    nlinarith [hL2]
  have hReal : (1/2:ℝ) ≤ Z.re := by
    have habs : |Z.re-1| ≤ ‖Z-1‖ := by
      simpa only [Complex.sub_re, Complex.one_re]
        using Complex.abs_re_le_norm (Z-1)
    have hlow := (abs_le.mp habs).1
    linarith [hZ,hInv,hlow]
  exact ⟨w,A,hw,hWcap,hApos,hAsub,hZ,hReal⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalActualSourceSmallTorusPathFilter -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Exact compatibility of one chronological source03 Fock×seen
state path with the ORIGINAL SMALL prime-residue torus frequency
transport in the chosen real source group (S or a Ts group).
The path's endpoint is the actual last state, not an arbitrary
new sample. -/
def sourceOriginalActualSourcePathSmallCompatible434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ) (g : Option ι)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d : ℤ) : Prop :=
  Green64SmallHaar.residues
    (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
    (J+ell)
    ((sourceOriginalSignedLaurentPathTerminal434 (2*R)
      path.1 path.2).val.1.1 g) =
  Green64SmallHaar.translate
    (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
    d
    (Green64SmallHaar.residues
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
      (J+ell) (path.1.val.1.1 g))

/-- The EXACT source03 original DIRTY Fourier coefficient can be
summed over ONLY the authentic state paths satisfying the physical
SMALL Haar transport equation at ANY chosen SMALL group g.
All noncompatible terms are identically ZERO, not bounded away
by a fabricated smallness estimate. Joint comparison signs and
the real chronological first-DIRTY insertion are untouched. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_source_small_path_filter434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (g : Option ι) (d : ℤ) :
    (sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T).coeff d =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    ∑ path ∈ (Finset.univ :
        Finset ((sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
          (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))).filter
        (fun path => sourceOriginalActualSourcePathSmallCompatible434 u J ell R g path d),
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T path d := by
  classical
  rw [source_original_ACTUAL_SOURCE_DIRTY_true_path_coefficient434]
  congr 1
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro path hpath
  by_cases hc : sourceOriginalActualSourcePathSmallCompatible434 u J ell R g path d
  · simp [hc]
  · have hz := source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g path d hc
    simp [hc,hz]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSmallTorusPairCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Exact Hermitian signed Gram for any FINITE selected subset of
complex chronological paths; no positivity termwise. -/
theorem source_original_finite_selected_complex_gram434
    {I : Type} [DecidableEq I] (s : Finset I) (A : I → ℂ) :
    (((‖∑ i ∈ s, A i‖^2 : ℝ)) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (A i) * A j := by
  have hn (z : ℂ) : (((‖z‖^2 : ℝ)) : ℂ) = star z * z := by
    calc
      _ = z * star z := by
        simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using
          (Complex.mul_conj z).symm
      _ = _ := mul_comm _ _
  rw [hn,star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- The TRUE source03 physical first-DIRTY Fourier Gram can restrict
BOTH paths in a collision pair to those obeying the genuine SMALL
modular-residue transport law in any chosen real source SMALL group.
Every excluded pair is EXACTLY ZERO. No arithmetic log saving or
fake cross-path orthogonality is asserted. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_small_compatible_pair_gram434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (g : Option ι) (d : ℤ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    let s : Finset Paths := Finset.univ.filter
      (fun path => sourceOriginalActualSourcePathSmallCompatible434
        u J ell R g path d)
    (((‖P.coeff d‖^2 : ℝ)) : ℂ) =
      (((‖Base‖^2 : ℝ)) : ℂ) *
      ∑ path ∈ s, ∑ other ∈ s,
        star (sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T path d) *
        sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T other d := by
  dsimp only
  let P := sourceOriginalActualSourceDIRTYLaurentRoot434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
  let Base : ℂ := physicalSourceBaselineProduct
    (fun g : β => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R)
  let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
    (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
  let s : Finset Paths := Finset.univ.filter
    (fun path => sourceOriginalActualSourcePathSmallCompatible434
      u J ell R g path d)
  let A : Paths → ℂ := fun path =>
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path d
  have hcoeff := source_original_ACTUAL_SOURCE_DIRTY_source_small_path_filter434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T g d
  have hg := source_original_finite_selected_complex_gram434 s A
  calc
    (((‖P.coeff d‖^2 : ℝ)) : ℂ) =
      (((‖Base‖^2 : ℝ)) : ℂ) *
      (((‖∑ path ∈ s, A path‖^2 : ℝ)) : ℂ) := by
        rw [hcoeff,norm_mul,mul_pow]
        push_cast
        rfl
    _ = _ := by
        rw [hg]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallClosedPathDivisibility -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- If the SMALL torus endpoint agrees with its start, and a
signed integer frequency d has transported it by d, then the
modulus of EVERY coordinate divides d. This is true arithmetic
ZMod divisibility, not a probabilistic resonance heuristic. -/
theorem source_original_ACTUAL_small_closed_coordinate_dvd434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (a b : Green64SmallHaar.SmallTorus modulus)
    (d : ℤ)
    (htrans : b = Green64SmallHaar.translate modulus d a)
    (p : P) (hclose : b p=a p) :
    (modulus p : ℤ) ∣ d := by
  have hp := congrArg (fun y : Green64SmallHaar.SmallTorus modulus => y p) htrans
  have hp' : a p = a p + (d : ZMod (modulus p)) := by
    simpa only [hclose,Green64SmallHaar.translate] using hp
  have hz : (d : ZMod (modulus p)) = 0 := by
    apply Eq.symm
    apply add_left_cancel (a := a p)
    simpa using hp'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd d (modulus p)).mp hz

/-- For the TRUE original source03 S+Ts/Tb first-DIRTY
Fock×seen path, if one SMALL group's endpoint is a CLOSED
residue loop and its signed complex frequency-d contribution
is NONZERO, then d is divisible by EVERY actual prime modulus
in that chosen SMALL group. This is a consequence of certified
physical transport; it does not assume SMALL disjointness or
claim the true source root has closed SMALL endpoints. -/
theorem source_original_ACTUAL_SOURCE_closed_SMALL_path_prime_dvd434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (g : Option ι)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d : ℤ)
    (hclose :
      Green64SmallHaar.residues
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        (J+ell)
        ((sourceOriginalSignedLaurentPathTerminal434 (2*R)
          path.1 path.2).val.1.1 g) =
      Green64SmallHaar.residues
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        (J+ell) (path.1.val.1.1 g))
    (hAneq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path d ≠ 0) :
    ∀ p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g},
      (p.val : ℤ) ∣ d := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1
      g p.val p.property).ne_zero⟩
  let sm : SP g → ℕ := fun p => p.val
  let a := Green64SmallHaar.residues sm (J+ell) (path.1.val.1.1 g)
  let b := Green64SmallHaar.residues sm (J+ell)
    ((sourceOriginalSignedLaurentPathTerminal434 (2*R)
      path.1 path.2).val.1.1 g)
  have ht : b=Green64SmallHaar.translate sm d a := by
    by_contra hb
    exact hAneq (source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g path d hb)
  intro p
  exact source_original_ACTUAL_small_closed_coordinate_dvd434 sm a b d ht
    p (congrArg (fun y => y p) hclose)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallTorusSpectralDifference -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Two REAL SMALL-torus transports between equal initial torus
states and equal terminal torus states impose congruent TOTAL
signed Fourier frequencies at EVERY coordinate modulus. -/
theorem source_original_TRUE_SMALL_torus_equal_endpoints_frequency_dvd434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (a b a' b' : Green64SmallHaar.SmallTorus modulus)
    (d e : ℤ) (ha : a = a') (hb : b = b')
    (ht : b = Green64SmallHaar.translate modulus d a)
    (ht' : b' = Green64SmallHaar.translate modulus e a')
    (p : P) : (modulus p : ℤ) ∣ d-e := by
  have h := congrArg (fun z : Green64SmallHaar.SmallTorus modulus => z p)
    (ht.symm.trans (hb.trans ht'))
  have hp : a p + (d : ZMod (modulus p)) =
      a p + (e : ZMod (modulus p)) := by
    simpa only [ha, Green64SmallHaar.translate] using h
  have heq : (d : ZMod (modulus p)) =
      (e : ZMod (modulus p)) := add_left_cancel hp
  have hzero : ((d-e : ℤ) : ZMod (modulus p)) = 0 := by
    rw [Int.cast_sub,heq,sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (d-e) (modulus p)).mp hzero

/-- If ALL genuine distinct prime coordinates of a SMALL group
divide the same signed spectral gap, their FULL prime product does.
Nothing has been averaged over characters or path histories. -/
theorem source_original_TRUE_prime_group_product_divides_gap434
    (P : Finset ℕ) (hp : ∀ q ∈ P, q.Prime)
    (d e : ℤ)
    (hcoord : ∀ q ∈ P, (q : ℤ) ∣ d-e) :
    P.prod id ∣ (d-e).natAbs := by
  apply Int.natCast_dvd.mp
  have hcast : ((P.prod id : ℕ) : ℤ) = ∏ q ∈ P, (q : ℤ) := by
    simp only [Nat.cast_prod]
    rfl
  rw [hcast]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact ((Nat.coprime_primes (hp a ha) (hp b hb)).mpr hab).isCoprime
  · intro a ha
    exact hcoord a ha

/-- A nonzero signed integer frequency gap cannot fit strictly
inside a positive modulus that divides its absolute magnitude. -/
theorem source_original_TRUE_dvd_gap_below_modulus_eq434
    (Q : ℕ) (d e : ℤ)
    (hQ : Q ∣ (d-e).natAbs)
    (hwindow : (d-e).natAbs < Q) : d=e := by
  have hz : (d-e).natAbs = 0 := by
    by_contra hn
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hQ
    omega
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYTorusSpectralLattice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Original source03 ACTUAL SMALL residue torus at the initial
Fock×seen state of a genuine chronological first-DIRTY path. -/
def sourceOriginalActualSourceDIRTYStartTorus434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ) (g : Option ι)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)) :
    Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val) :=
  Green64SmallHaar.residues
    (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
    (J+ell) (path.1.val.1.1 g)

/-- Last actual chronological state, not an independent terminal
sample; holds all original source SMALL and BIG history. -/
def sourceOriginalActualSourceDIRTYTerminalTorus434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ) (g : Option ι)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)) :
    Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val) :=
  Green64SmallHaar.residues
    (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
    (J+ell) ((sourceOriginalSignedLaurentPathTerminal434
      (2*R) path.1 path.2).val.1.1 g)

/-- TRUE full first-DIRTY Fock×seen state paths p,q with equal
SMALL initial and final torus residues can BOTH have nonzero
signed TOTAL Fourier amplitudes only at frequencies congruent
modulo the FULL genuine prime product of any chosen source03
SMALL group (distinguished S or any Ts).
This retains the TRUE four-sign-compatible RAW/comparison joint K
and all chronological first-DIRTY insertion positions. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_equal_small_endpoints_gap_product434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (g : Option ι)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstart : sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hend : sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0) :
    (sourceOriginalActualSmallPrimeSets434 u g).prod id ∣ (d-e).natAbs := by
  classical
  let P := sourceOriginalActualSmallPrimeSets434 u g
  let sm : {r : ℕ // r ∈ P} → ℕ := fun r => r.val
  have hp : ∀ r ∈ P, r.Prime :=
    (source_original_ACTUAL_SMALL_source_bounds434 u).1 g
  letI (r : {r : ℕ // r ∈ P}) : NeZero (sm r) :=
    ⟨(hp r.val r.property).ne_zero⟩
  let a := sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p
  let b := sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p
  let a' := sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q
  let b' := sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q
  have ht : b = Green64SmallHaar.translate sm d a := by
    by_contra hb
    apply hnp
    apply source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g p d
    exact hb
  have ht' : b' = Green64SmallHaar.translate sm e a' := by
    by_contra hb
    apply hnq
    apply source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g q e
    exact hb
  apply source_original_TRUE_prime_group_product_divides_gap434 P hp d e
  intro r hr
  have hcoord := source_original_TRUE_SMALL_torus_equal_endpoints_frequency_dvd434
    sm a b a' b' d e hstart hend ht ht' ⟨r,hr⟩
  simpa only [sm] using hcoord

/-- REAL source03 single chronological Fock×seen path supports
nonzero Fourier amplitudes only in ONE residue class modulo the
FULL true SMALL prime product (per group). No averaging/saving. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_same_path_spectral_lattice434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (g : Option ι)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p e ≠ 0) :
    (sourceOriginalActualSmallPrimeSets434 u g).prod id ∣ (d-e).natAbs := by
  exact source_original_ACTUAL_SOURCE_DIRTY_equal_small_endpoints_gap_product434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T g p p d e rfl rfl hnp hnq
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYTorusEndpointFrequency -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Exact endpoint selection on genuine chronological paths:
equal initial SMALL residue tori and equal nonzero Fourier mode
force equal terminal SMALL residue tori. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_same_start_same_frequency_end434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (heq : freq = freq')
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) :
    ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q := by
  have hp (g : Option ι) :
      sourceOriginalActualSourcePathSmallCompatible434
        u J ell R g p freq := by
    by_contra hb
    exact hnp (source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g p freq hb)
  have hq (g : Option ι) :
      sourceOriginalActualSourcePathSmallCompatible434
        u J ell R g q freq' := by
    by_contra hb
    exact hnq (source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T g q freq' hb)
  intro g
  have htp :
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
      Green64SmallHaar.translate
        (fun p : {r : ℕ // r ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        freq (sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p) :=
      hp g
  have htq :
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q =
      Green64SmallHaar.translate
        (fun p : {r : ℕ // r ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        freq' (sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q) :=
      hq g
  calc
    _ = Green64SmallHaar.translate
      (fun p : {r : ℕ // r ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
      freq (sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p) := htp
    _ = Green64SmallHaar.translate
      (fun p : {r : ℕ // r ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
      freq' (sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q) := by
        rw [heq, hstarts g]
    _ = _ := htq.symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYAllSmallSpectralModulus -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The REAL ORIGINAL SOURCE DATA SMALL modulus (distinguished S and
EVERY Ts), with duplicates removed by FINSET UNION. No disjointness
of arbitrary SourceComparisonData434.Ts families is invented. -/
noncomputable def sourceOriginalActualSourceALLSmallModulus434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) : ℕ :=
  (u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts).prod id

/-- Every prime in the genuine full source S + all Ts union occurs
as a coordinate in one ACTUAL physical source03 SMALL torus. -/
theorem source_original_ACTUAL_SOURCE_ALL_SMALL_group_coordinate434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (q : ℕ) (hq : q ∈ u.S ∪
      (Finset.univ : Finset ι).biUnion u.Ts) :
    ∃ g : Option ι, q ∈ sourceOriginalActualSmallPrimeSets434 u g := by
  rcases Finset.mem_union.mp hq with hs | hts
  · exact ⟨none, by simpa [sourceOriginalActualSmallPrimeSets434,
      sourceOriginalFullGroupPrimeSets434] using hs⟩
  · obtain ⟨g,hg,hqg⟩ := Finset.mem_biUnion.mp hts
    exact ⟨some g, by simpa [sourceOriginalActualSmallPrimeSets434,
      sourceOriginalFullGroupPrimeSets434] using hqg⟩

/-- The TOTAL original SMALL union is genuinely a finite set of
primes, including possibly overlapping Ts groups only once. -/
theorem source_original_ACTUAL_SOURCE_ALL_SMALL_primes434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) :
    ∀ q ∈ u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts, q.Prime := by
  intro q hq
  rcases Finset.mem_union.mp hq with hs | hts
  · exact u.hSPrime q hs
  · obtain ⟨g,hg,hqg⟩ := Finset.mem_biUnion.mp hts
    exact u.hTsPrime g q hqg

/-- When two TRUE chronological first-DIRTY Fock×seen paths have
equal initial and final SMALL torus residues in ALL genuine
source groups S+Ts, nonzero complex signed coefficients at modes
d,e force their spectral gap to be divisible by the FULL true
squarefree product of every original SMALL prime.
No use of iid, absolute TV bounds, or character averaging. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0) :
    sourceOriginalActualSourceALLSmallModulus434 u ∣ (d-e).natAbs := by
  classical
  let P := u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts
  have hp : ∀ a ∈ P, a.Prime :=
    source_original_ACTUAL_SOURCE_ALL_SMALL_primes434 u
  change P.prod id ∣ (d-e).natAbs
  apply source_original_TRUE_prime_group_product_divides_gap434 P hp d e
  intro a ha
  obtain ⟨g,hg⟩ := source_original_ACTUAL_SOURCE_ALL_SMALL_group_coordinate434
    u a ha
  have hdiv := source_original_ACTUAL_SOURCE_DIRTY_equal_small_endpoints_gap_product434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T g p q d e (hstarts g) (hends g) hnp hnq
  have ha : a ∣ (sourceOriginalActualSmallPrimeSets434 u g).prod id :=
    Finset.dvd_prod_of_mem id hg
  exact Int.natCast_dvd.mpr (ha.trans hdiv)

/-- The individual ORIGINAL full first-DIRTY Fock×seen path amplitude
has Fourier support inside ONE residue class modulo ALL genuine
SMALL prime coordinates simultaneously. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_same_path_ALL_SMALL_lattice434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p e ≠ 0) :
    sourceOriginalActualSourceALLSmallModulus434 u ∣ (d-e).natAbs := by
  apply source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    p p d e (fun _ => rfl) (fun _ => rfl) hnp hnq

/-- Exact SAME-initial-and-final-SMALL-path spectral uniqueness
inside any window narrower than the TRUE full SMALL modulus.
This is a substantive arithmetic no-return criterion, but a
separate moving-R bound on physical Fourier windows is still
required to use it asymptotically. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_short_window_unique434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0)
    (hwin : (d-e).natAbs < sourceOriginalActualSourceALLSmallModulus434 u) :
    d = e := by
  exact source_original_TRUE_dvd_gap_below_modulus_eq434
    (sourceOriginalActualSourceALLSmallModulus434 u) d e
    (source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
      p q d e hstarts hends hnp hnq)
    hwin
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYNoReturnWindow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- TRUE quantitative no-return theorem at original 2R visits.
If the full actual source03 SMALL prime modulus is larger than
TWICE the reachable chronological Fourier radius, then two
nonzero physical first-DIRTY path amplitudes with identical
initial and terminal SMALL tori must have exactly the SAME
TOTAL INTEGER frequency. All Fock/seen histories, alternating
G_i/E_i, joint K and the two endpoint OLD masks stay physical.
The premise is an EXPLICIT ARITHMETIC SIZE CONDITION: this theorem
does not yet establish it uniformly for growing R and moving L. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_full_radius_no_return434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hwindow :
      2 * ((2*R) * (k.natAbs *
        sourceOriginalActualSourceGEDualDivisorCap434
          u blockA blockB J ell m hmJ k)) <
        sourceOriginalActualSourceALLSmallModulus434 u)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q e ≠ 0) : d = e := by
  have hd := source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p d hnp
  have he := source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T q e hnq
  have hTriangle := Int.natAbs_sub_le d e
  have hshort : (d-e).natAbs <
      sourceOriginalActualSourceALLSmallModulus434 u := by
    omega
  exact source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_short_window_unique434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p q d e hstarts hends hnp hnq hshort

/-- In the short-window regime, EACH COMPLETE GENUINE
first-DIRTY Fock×seen state path has AT MOST ONE total signed
frequency with nonzero complex coefficient. This is stronger
than a mere k-lattice restriction but does NOT remove coherent
cross-PATH collisions at that common frequency. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_single_path_monochromatic434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hwindow :
      2 * ((2*R) * (k.natAbs *
        sourceOriginalActualSourceGEDualDivisorCap434
          u blockA blockB J ell m hmJ k)) <
        sourceOriginalActualSourceALLSmallModulus434 u)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hd : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p d ≠ 0)
    (he : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p e ≠ 0) : d=e := by
  exact source_original_ACTUAL_SOURCE_DIRTY_full_radius_no_return434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hwindow p p d e
    (fun _ => rfl) (fun _ => rfl) hd he
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeTorus -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The exact physical chronological relative SMALL-torus
displacement: for EVERY distinguished S/Ts prime coordinate,
terminal residue MINUS initial residue. Unlike endpoint keys,
this is independent of which physical start torus a path uses. -/
def sourceOriginalActualSourceDIRTYRelativeTorus434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)) :
    (g : Option ι) →
      Green64SmallHaar.SmallTorus
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val) :=
  fun g p => sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g path p -
    sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g path p

/-- A nonzero signed coefficient on a REAL complete first-DIRTY
Fock×seen path fixes its ENTIRE relative S+Ts torus to the
diagonal image of its original TOTAL signed integer frequency.
All original alternating orientations and joint RAW/comparison K
remain literal; NO equality between initial states is assumed. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq : ℤ)
    (hn : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq ≠ 0) :
    ∀ (g : Option ι)
      (p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g}),
    sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R path g p =
      (freq : ZMod p.val) := by
  have hc (g : Option ι) :
      sourceOriginalActualSourcePathSmallCompatible434
        u J ell R g path freq := by
    by_contra hb
    exact hn
      (source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T g path freq hb)
  intro g p
  have h := congrArg (fun torus :
      Green64SmallHaar.SmallTorus
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val) =>
          torus p) (hc g)
  change sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g path p =
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g path p +
        (freq : ZMod p.val) at h
  change sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g path p -
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g path p =
        (freq : ZMod p.val)
  rw [h]
  simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeGap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Equality of true RELATIVE S+Ts torus displacements for two
different physical first-DIRTY paths forces their signed TOTAL
Fourier frequency difference to be divisible by the FULL actual
SMALL prime modulus. Unlike prior matched-endpoint results,
NO equal initial or equal terminal Fock torus is assumed. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_equal_relative_ALL_SMALL_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hrelative : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R p = sourceOriginalActualSourceDIRTYRelativeTorus434
        u J ell R q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) :
    sourceOriginalActualSourceALLSmallModulus434 u ∣
      (freq-freq').natAbs := by
  let S := u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts
  change S.prod id ∣ (freq-freq').natAbs
  apply source_original_TRUE_prime_group_product_divides_gap434 S
    (source_original_ACTUAL_SOURCE_ALL_SMALL_primes434 u) freq freq'
  intro a ha
  obtain ⟨g,hga⟩ :=
    source_original_ACTUAL_SOURCE_ALL_SMALL_group_coordinate434 u a ha
  let atom : {v : ℕ // v ∈ sourceOriginalActualSmallPrimeSets434 u g} :=
    ⟨a,hga⟩
  have h1 := source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p freq hnp g atom
  have h2 := source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T q freq' hnq g atom
  have hcoord := congrArg (fun f => f g atom) hrelative
  rw [h1,h2] at hcoord
  have hzero : ((freq-freq':ℤ):ZMod a)=0 := by
    rw [Int.cast_sub,hcoord,sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (freq-freq') a).mp hzero
/-- At a fixed TOTAL physical Fourier frequency, EVERY pair
of nonzero TRUE path amplitudes has the SAME relative SMALL-torus
displacement, even when their initial and terminal Fock states
are unrelated. An unconditional unaveraged signed collision rule. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_equal_frequency_relative_eq434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq : ℤ)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq ≠ 0) :
    sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R p =
      sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R q := by
  funext g atom
  rw [source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p freq hnp g atom,
    source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T q freq hnq g atom]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeCrossGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- ORIGINAL unaveraged, complex RAW/comparison first-DIRTY
chronological source03 cross-path Gram vanishes EXACTLY between
ANY two families with DIFFERENT relative S+Ts torus
displacements, with NO common start- or end-state hypothesis.
This is pointwise at the SAME total signed integer frequency,
independent of L or any asymptotic size condition. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_cross_relative_torus_gram_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (FR FC : Finset ((sourceOriginalActualSourceDIRTYPathState434
      u J ell) × (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434
        u J ell)))
    (hsep : ∀ p ∈ FR, ∀ q ∈ FC,
      sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R p ≠
        sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R q)
    (freq : ℤ) :
    (∑ p ∈ FR, ∑ q ∈ FC,
      star (sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T p freq) *
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T q freq) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hpn : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq = 0
  · simp [hpn]
  · by_cases hqn : sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T q freq = 0
    · simp [hqn]
    · have hEq := source_original_ACTUAL_SOURCE_DIRTY_equal_frequency_relative_eq434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T p q freq hpn hqn
      exact (hsep p hp q hq hEq).elim
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYSmallQuantitativeGap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Real
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Unconditional TRUE original SOURCE DATA lower bound for the
COMPLETE SMALL spectral modulus using the actual distinguished S
prime band. Does NOT assume Ts disjoint, since union removes
duplicates. The exp(L^a) factor comes from SourceComparisonData.hSmall. -/
theorem source_original_ACTUAL_SOURCE_all_SMALL_modulus_exp_lower434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) :
    (Real.exp (L^cfg.aexp))^(u.S.card) ≤
      (sourceOriginalActualSourceALLSmallModulus434 u : ℝ) := by
  let P := u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts
  have hP : ∀ a ∈ P, a.Prime :=
    source_original_ACTUAL_SOURCE_ALL_SMALL_primes434 u
  have hQpos : 0 < (P.prod id : ℕ) := by
    apply Finset.prod_pos
    intro p hp
    exact (hP p hp).pos
  have hsubset : u.S ⊆ P := Finset.subset_union_left
  have hdiv : u.S.prod id ∣ P.prod id :=
    Finset.prod_dvd_prod_of_subset u.S P id hsubset
  have hSle : u.S.prod id ≤ P.prod id :=
    Nat.le_of_dvd hQpos hdiv
  have hprod : (Real.exp (L^cfg.aexp))^u.S.card ≤
      ((u.S.prod id : ℕ):ℝ) := by
    calc
      _ = ∏ q ∈ u.S, Real.exp (L^cfg.aexp) := by
        simp only [Finset.prod_const]
      _ ≤ ∏ q ∈ u.S, (q:ℝ) := by
        apply Finset.prod_le_prod₀
        · intro q hq
          exact (Real.exp_pos _).le
        · intro q hq
          exact (u.hSmall q hq).1
      _ = ((u.S.prod id:ℕ):ℝ) := by
        simp only [Nat.cast_prod]
        rfl
  calc
    _ ≤ ((u.S.prod id:ℕ):ℝ) := hprod
    _ ≤ ((P.prod id : ℕ) : ℝ) := by exact_mod_cast hSle
    _ = _ := rfl

/-- For two true chronological Fock×seen source03 paths with the
SAME initial and terminal SMALL tori, a DIFFERENT signed total
Fourier frequency must be at least exp(L^a)^card(S) away. This is
a REAL quantitative arithmetic gap, not an asymptotic log saving. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_S_exponential_frequency_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0)
    (hneq : d ≠ e) :
    (Real.exp (L^cfg.aexp))^(u.S.card) ≤ ((d-e).natAbs : ℝ) := by
  have hdiv := source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    p q d e hstarts hends hnp hnq
  have hdiffpos : 0 < (d-e).natAbs := by
    have hh : d-e ≠ 0 := sub_ne_zero.mpr hneq
    exact Int.natAbs_pos.mpr hh
  have hle : sourceOriginalActualSourceALLSmallModulus434 u ≤
      (d-e).natAbs := Nat.le_of_dvd hdiffpos hdiv
  calc
    _ ≤ (sourceOriginalActualSourceALLSmallModulus434 u : ℝ) :=
      source_original_ACTUAL_SOURCE_all_SMALL_modulus_exp_lower434 u
    _ ≤ ((d-e).natAbs : ℝ) := by exact_mod_cast hle
/-- ALL true source03 first-DIRTY path Fourier coefficients
at matched SMALL endpoints have a UNIQUE total frequency inside
any window narrower than the ORIGINAL distinguished S exponential
product size. This holds even with arbitrary original K joint signs
and 2R actual alternating state transitions. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_S_narrow_window_unique434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0)
    (hwidth : ((d-e).natAbs : ℝ) <
      (Real.exp (L^cfg.aexp))^(u.S.card)) : d=e := by
  have hle := source_original_ACTUAL_SOURCE_all_SMALL_modulus_exp_lower434 u
  have hlt : ((d-e).natAbs : ℝ) <
      (sourceOriginalActualSourceALLSmallModulus434 u : ℝ) :=
    hwidth.trans_le hle
  have hwin : (d-e).natAbs <
      sourceOriginalActualSourceALLSmallModulus434 u := by
    exact_mod_cast hlt
  exact source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_short_window_unique434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    p q d e hstarts hends hnp hnq hwin
end Green64Analytic.CorrelationSquare

end

end

