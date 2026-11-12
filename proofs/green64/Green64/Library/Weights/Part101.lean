module

public import Green64.Library.Weights.Part100
public import Green64.Library.Weights.LiteralD61StrippedCore
public import Green64.Library.Correlation.Part069
public import Green64.Library.Weights.FullCoupledSlice

@[expose] public section

/-!
# Weights / Part101

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualD61NativeCommon -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The B578 alpha at the ORIGINAL b0/4 slack is exactly the sigma-one
D61 alpha, including the full D20 cell, both D36 inequalities and terminal
clip. No cofactor, cell or bin is changed. -/
theorem b608_original_D61_alpha_identity434 (a eta b0 L : ℝ) :
    sourceB578OriginalD36UpperAlpha434 a eta (b0/4) L =
      sourceNativeB563OriginalD61Alpha434 a eta b0 L := by
  have he : Real.exp (a*L)=(Real.exp L)^a := by
    rw [mul_comm a L,Real.exp_mul]
  funext n
  simp only [sourceB578OriginalD36UpperAlpha434,
    sourceNativeB563OriginalD61Alpha434,Real.rpow_neg_one,one_div,he]

/-- Exact original nativeCommon at sigma=1 D61. The arbitrary supplied
Lambda, the ORIGINAL negative Q frequency array, physical n, character
modulus |k|, and every SMALL marked factor remain literally present.
No norm or assumption about the profile is used. -/
theorem b608_actual_D61_native_common434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta b0 : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) :
    sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta (b0/4) k chi
      sigma0 sigma1 Lambda n =
    Lambda n * primeSlotCoreValue (sourceB578ActualAllGroups434 L hS)
      (sourceNativePrimeCore 6 (sourceOriginalLiteralDepth 6 L) L b slot delta (-freq)
        (Finset.Icc lo hi) (sourceNativeB563OriginalD61Alpha434 a eta b0 L)
        k.natAbs chi sigma0 sigma1) n * sourceB578ActualSmallMarkedFactor434 L hS n := by
  unfold sourceB578ActualNativeCommon434
  rw [b608_original_D61_alpha_identity434]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualProjectedD61Pair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Literal B578 Q data with the exact D61 alpha in complete actual P
coordinates. The original negative Fourier array is retained. -/
def b608ActualD61AllPCore434
    (L : ℝ) (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta b0 : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (n : ℕ) : ℂ :=
  primeSlotCoreValue (sourceOriginalPAllActualBands 6 L)
    (sourceNativePrimeCore 6 (sourceOriginalLiteralDepth 6 L) L b slot delta (-freq)
      (Finset.Icc lo hi) (sourceNativeB563OriginalD61Alpha434 a eta b0 L)
      k.natAbs chi sigma0 sigma1) n

/-- Apply the exact original group-union reindex to nativeCommon itself.
The entire supplied Lambda is kept, with no profile-norm hypothesis. -/
theorem b608_actual_D61_native_common_allP434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta b0 : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) :
    sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta (b0/4) k chi
      sigma0 sigma1 Lambda n =
    Lambda n * b608ActualD61AllPCore434 L b slot delta freq lo hi a eta b0 k chi
      sigma0 sigma1 n * sourceB578ActualSmallMarkedFactor434 L hS n := by
  rw [b608_actual_D61_native_common434,b604_actual_B578_prime_core434 L hS hL]
  rfl

/-- Exact original B578 nativeCommon pair, complete BIG full-ban slice
and both original projectors, now in the actual all-P D61 coordinates.
The two Q arrays, masks and cofactor supports are independent parameters.
Source conjugation, both Lambdas, the true |k| character and every marked
kernel factor are preserved BEFORE a norm or square. This pointwise
identity can be rewritten inside the original physical gate and measures;
it does not assert a signed saving or an upper bound for arbitrary Lambda. -/
theorem b608_actual_B578_projected_D61_pair434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b b' : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot slot' : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (delta' : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b' slot').length → Bool)
    (freq' : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b' slot').length → ℝ)
    (lo hi lo' hi' : ℕ) (a eta b0 : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigmaF0 sigmaF1 sigmaG0 sigmaG1 : ℝ) (LambdaF LambdaG : ℕ → ℂ) (w wp : ℕ) :
    sourceB578ActualPatternProjector434 L m nu w *
      sourceB578ActualPatternProjector434 L m nu wp *
      (star (sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta (b0/4)
        k chi sigmaF0 sigmaF1 LambdaF w) *
       sourceB578ActualNativeCommon434 L hS b' slot' delta' freq' lo' hi' a eta (b0/4)
        k chi sigmaG0 sigmaG1 LambdaG wp *
       sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux (1/2) w wp) =
    (star (LambdaF w)*LambdaG wp) *
      (star (b608ActualD61AllPCore434 L b slot delta freq lo hi a eta b0 k chi
        sigmaF0 sigmaF1 w) *
       b608ActualD61AllPCore434 L b' slot' delta' freq' lo' hi' a eta b0 k chi
        sigmaG0 sigmaG1 wp) *
      (b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) w *
       b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) wp *
       sourceB574CanonicalStrippedSlice434 J 1 m hmJ (b604ActualLiftedPattern434 6 L m nu)
        Q hA hB xi (sourceOriginalPAllActualBands 6 L) (sourceNativeOriginalAllPMass434 6 L)
        (b604ActualLiftedAux434 6 L m nu aux) (1/2) w wp) := by
  rw [b608_actual_D61_native_common_allP434 L hS hL,
    b608_actual_D61_native_common_allP434 L hS hL]
  simp only [star_mul]
  have hs := b604_actual_B578_projected_slice434 L hS hL J m hmJ nu Q hA hB xi aux w wp
  calc
    _ = (star (LambdaF w)*LambdaG wp) *
      (star (b608ActualD61AllPCore434 L b slot delta freq lo hi a eta b0 k chi
        sigmaF0 sigmaF1 w) *
       b608ActualD61AllPCore434 L b' slot' delta' freq' lo' hi' a eta b0 k chi
        sigmaG0 sigmaG1 wp) *
      (sourceB578ActualPatternProjector434 L m nu w *
       sourceB578ActualPatternProjector434 L m nu wp *
       (star (sourceB578ActualSmallMarkedFactor434 L hS w) *
        sourceB578ActualSmallMarkedFactor434 L hS wp *
        sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi
          (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux (1/2) w wp)) := by ring
    _ = _ := by rw [hs]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualAllPGatedChart -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 14000

/-- The LITERAL original B578 separated P-gated native chart, now with
actual all-P D61 cores and full lifted marked Knu. All actual profiles and
phases, signed wp=w+2kD, modulus |k|, both original P-part gates, both
projectors BEFORE any square, the full target-list carrier, one exterior
Z_j and exactly one kappa remain. This is an exact equality, not a profile
bound, not a Fourier integration, and not an RMS-saving claim. -/
theorem b608_actual_allP_D61_native_P_gated_chart434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta b0 : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (U V K : ℝ) (j : ℕ) (ja jb : ℤ)
    (rho : ℝ) (zeta : Fin 3 → ℝ) (t : ℝ) (Spos R : Finset ℕ) :
    let Z := sourceCorrectedDyadicScale U V (L^K) j
    let Y := Z*(Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB))
    let D := sourceOriginalProbeDA434 m nu aux*sourceOriginalProbeDB434 m nu aux
    let wp := fun w : ℕ=>((w:ℤ)+2*k*(D:ℤ)).toNat
    let sigmaF := 2*Real.pi*rho-2*Real.pi*zeta 1
    let sigmaG := 2*Real.pi*zeta 0+2*Real.pi*rho
    let LambdaF := fun n : ℕ=>sourceB578EndpointProfile434 true ((n:ℝ)/Y)*
      sourcePhase n (-(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t))
    let LambdaG := fun n : ℕ=>sourceB578EndpointProfile434 false ((n:ℝ)/Y)*
      sourcePhase n (-2*Real.pi*rho)
    let gate := fun w : ℕ=>0<w ∧ 0<(w:ℤ)+2*k*(D:ℤ) ∧
      sourceOriginalPPrimePart (sourceNativeOriginalG434 6 L) w ∈ R ∧
      sourceOriginalPPrimePart (sourceNativeOriginalG434 6 L) (wp w) ∈ R
    (Z:ℂ)/(Y:ℂ)*(∑ w ∈ Spos,
      if gate w then
        (star (LambdaF w)*LambdaG (wp w)) *
        (star (b608ActualD61AllPCore434 L b slot delta freq lo hi a eta b0 k chi
          sigmaF 0 w) *
         b608ActualD61AllPCore434 L b slot delta freq lo hi a eta b0 k chi
          sigmaG 0 (wp w)) *
        (b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) w *
         b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) (wp w) *
         sourceB574CanonicalStrippedSlice434 J 1 m hmJ (b604ActualLiftedPattern434 6 L m nu)
          Q hA hB xi (sourceOriginalPAllActualBands 6 L) (sourceNativeOriginalAllPMass434 6 L)
          (b604ActualLiftedAux434 6 L m nu aux) (1/2) w (wp w))
      else 0) =
    (Z:ℂ)*(sourceB578CanonicalRowScale434 Q xi:ℂ)/(Y:ℂ)*(∑ w ∈ Spos,
      if gate w then
        (∑ target ∈ bigMarkLists (sourceNativeOriginalTb434 6 L)
            (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) (wp w),
          star (sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux true target
            b slot delta freq lo hi a eta (b0/4) k chi sigmaF 0 LambdaF w)*
          sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux false target
            b slot delta freq lo hi a eta (b0/4) k chi sigmaG 0 LambdaG (wp w))*
        sourceB578ActualPatternProjector434 L m nu w*
        sourceB578ActualPatternProjector434 L m nu (wp w)
      else 0) := by
  dsimp only
  have hold := source_B578_actual_stripped_P_gated_chart434 L hS J m hmJ nu Q hA hB xi aux
    b slot delta freq lo hi a eta (b0/4) k chi U V K j ja jb rho zeta t Spos R
  dsimp only at hold
  rw [←hold]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs with hg
  · have hp := b608_actual_B578_projected_D61_pair434 L hS hL J m hmJ nu Q hA hB xi aux
      b b slot slot delta freq delta freq lo hi lo hi a eta b0 k chi
      (2*Real.pi*rho-2*Real.pi*zeta 1) 0 (2*Real.pi*zeta 0+2*Real.pi*rho) 0
      (fun n : ℕ=>sourceB578EndpointProfile434 true
        ((n:ℝ)/(sourceCorrectedDyadicScale U V (L^K) j*
          (Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)))) *
        sourcePhase n (-(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t)))
      (fun n : ℕ=>sourceB578EndpointProfile434 false
        ((n:ℝ)/(sourceCorrectedDyadicScale U V (L^K) j*
          (Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)))) *
        sourcePhase n (-2*Real.pi*rho))
      w (((w:ℤ)+2*k*((sourceOriginalProbeDA434 m nu aux*
        sourceOriginalProbeDB434 m nu aux:ℕ):ℤ)).toNat)
    convert hp.symm using 1
    ring
  · rfl
end Green64Analytic.SourceBlockSieve

end

end

