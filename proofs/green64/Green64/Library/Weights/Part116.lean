module

public import Green64.Library.Analysis.Estimates.Part016
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part040
public import Green64.Library.Weights.Part100
public import Green64.Library.Weights.Part110
public import Green64.Library.Weights.Part023
public import Green64.Library.Correlation.Part072
public import Green64.Library.Weights.Part113
public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.Part033

@[expose] public section

/-!
# Weights / Part116

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualCellCoupledPhase -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Exact Mellin scale separation on the true positive auxiliary product.
The common frequency zeta-2*pi*s occurs in BOTH prime-block tests; the
remaining exp(-2*pi*s*log Z*i) is independent of every auxiliary draw. -/
theorem parity_mellin_scale_product_factor434
    (Z zeta s : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    sourceOriginalPureMellinPhase434 zeta (a*b)*parityScaleMellinFactor434 Z (a*b) s =
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
      (sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) a *
        sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) b) := by
  have hPhase : sourceOriginalPureMellinPhase434 zeta (a*b) *
      sourceOriginalPureMellinPhase434 (-2*Real.pi*s) (a*b) =
      sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (a*b) := by
    unfold sourceOriginalPureMellinPhase434
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold parityScaleMellinFactor434
  calc
    _ = Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
        (sourceOriginalPureMellinPhase434 zeta (a*b) *
          sourceOriginalPureMellinPhase434 (-2*Real.pi*s) (a*b)) := by ring
    _ = _ := by
      rw [hPhase,source_original_pure_mellin_product_factor434 _ a b ha hb]

/-- Exact signed additive Fourier convention at the original shift 2*k*c.
This uses the certified source Fourier/integerPhase identification, with
no conversion of 2*pi into the independent Mellin frequency. -/
theorem parity_signed_aux_fourier_phase434 (k : ℤ) (c : ℕ) (theta : ℝ) :
    fourier (-((2*k)*(c : ℤ))) (theta : AddCircle (1 : ℝ)) =
      Green64SourceC6.integerPhase (-(2*(k : ℝ))*theta) (c : ℤ) := by
  rw [source_fourier_integer_phase434]
  unfold Green64SourceC6.integerPhase
  congr 1
  push_cast
  ring

/-- The actual coupled kernel is the literal original physical primitive
cell Fourier sum with two Mellin-twisted independent input tests. The
additive phase remains coupled at DA*DB. Both inverse cell masses and the
source sign remain outside, and the original shift is exactly 2*k. -/
theorem parity_actual_cell_coupled_kernel_source_phase434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s theta : ℝ) :
    let P := sourceNativeOriginalTb434 20 L
    let V := sourceNativeOriginalVbig434 20 L
    let SA : nu.1 → Finset ℕ := fun z => P z.val.1
    let SB : nu.2 → Finset ℕ := fun z => P z.val.1
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
        (theta : AddCircle (1 : ℝ)) =
      (-((-1 : ℂ)^(nu.1.card+nu.2.card)) *
        (sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu hA)
          (sourceOriginalProbeCellB434 m P V nu hB) r.1.1 r.2.1 : ℂ)) *
      (Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
       ∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.1 *
          sourceOriginalGramPrimeMass434 SB (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.2 : ℝ) : ℂ) *
        (sourceOriginalPrimitiveInputCellMode434 Q hA r.1.1 r.1.2 (pa ab.1) *
          sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pa ab.1)) *
        (sourceOriginalPrimitiveInputCellMode434 Q hB r.2.1 r.2.2 (pb ab.2) *
          sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pb ab.2)) *
        Green64SourceC6.integerPhase (-(2*(k : ℝ))*theta) ((pa ab.1*pb ab.2 : ℕ) : ℤ)) := by
  dsimp only
  rw [parity_actual_cell_coupled_kernel_gram434 L J m hmJ nu hnu]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  have ha : 0 < sourceOriginalGramPrimeProduct434
      (fun z : nu.1 => sourceNativeOriginalTb434 20 L z.val.1) ab.1 := by
    apply Finset.prod_pos
    intro z hz
    exact (source_native_original_Tb_prime_range434 20 L z.val.1 (ab.1 z).val (ab.1 z).property).1.pos
  have hb : 0 < sourceOriginalGramPrimeProduct434
      (fun z : nu.2 => sourceNativeOriginalTb434 20 L z.val.1) ab.2 := by
    apply Finset.prod_pos
    intro z hz
    exact (source_native_original_Tb_prime_range434 20 L z.val.1 (ab.2 z).val (ab.2 z).property).1.pos
  rw [parity_mellin_scale_product_factor434 Z zeta s _ _ ha hb,
    parity_signed_aux_fourier_phase434]
  ring
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledMinor -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 28000

/-- Exact squared-norm correspondence with the genuine source two-sided
physical bilinear kernel. Both inverse original cell masses occur in the
explicit squared cost. The source multiplier has signed shift 2*k;
the two unit-modulus Mellin input phases are retained in their own blocks. -/
theorem parity_actual_cell_coupled_kernel_bilinear_norm_sq434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s theta : ℝ) :
    let P := sourceNativeOriginalTb434 20 L
    let V := sourceNativeOriginalVbig434 20 L
    let SA : nu.1 → Finset ℕ := fun z => P z.val.1
    let SB : nu.2 → Finset ℕ := fun z => P z.val.1
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun a => (sourceOriginalGramPrimeMass434 SA (fun z p => (1/(p : ℝ))/(V z.val.1)) a : ℂ)
    let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun b => (sourceOriginalGramPrimeMass434 SB (fun z p => (1/(p : ℝ))/(V z.val.1)) b : ℂ)
    let fA := fun a : SourceOriginalGramPrimeTuple434 SA =>
      if sourceOriginalLiteralLogCell434 hA r.1.1 (pa a) then
        star (r.1.2.2 (pa a : ZMod (r.1.2.1.val+1))) *
          sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pa a) else 0
    let fB := fun b : SourceOriginalGramPrimeTuple434 SB =>
      if sourceOriginalLiteralLogCell434 hB r.2.1 (pb b) then
        star (r.2.2.2 (pb b : ZMod (r.2.2.1.val+1))) *
          sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pb b) else 0
    ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
        (theta : AddCircle (1 : ℝ))‖^2 =
      (sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu hA)
        (sourceOriginalProbeCellB434 m P V nu hB) r.1.1 r.2.1)^2 *
      ‖sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb fA fB
        (fun q => Green64SourceC6.integerPhase (-((2*k : ℤ) : ℝ)*theta)
          ((pa q.1*pb q.2 : ℕ) : ℤ))‖^2 := by
  dsimp only
  have he := parity_actual_cell_coupled_kernel_source_phase434
    L J m hmJ nu hnu hA hB r zeta Z k s theta
  dsimp only at he
  rw [he]
  have hExp : ‖Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I)‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_I_mul_ofReal _
  have hPhase : -(2*(k : ℝ))*theta = -((2*k : ℤ) : ℝ)*theta := by push_cast; rfl
  simp only [sourceOriginalFiniteTwoSidedMinorBilinear434,
    sourceOriginalPrimitiveInputCellMode434,ite_mul,zero_mul,Complex.ofReal_mul,hPhase]
  simp only [Complex.ofReal_mul] at hExp
  simp only [norm_mul,hExp,norm_neg,norm_pow,norm_one,one_pow,one_mul,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,sq_abs]

/-- Genuine minor-arc bound for the actual coupled kernel, using the
certified full-cell C6 estimate and actual r20 B636 group gates. The
source comparison record contributes ONLY its genuine original group
geometry and masses, expressed by the six exact fields; no arc or kernel
smallness is assumed. Fixed precision and exponent losses precede L.
The denominator is the literal (2*k).natAbs*ceil(L^(D+1)); both inverse
cell masses remain in the squared coefficient outside the bound. -/
theorem parity_eventually_actual_cell_coupled_minor434
    (cfg : SourceComparisonFixed434) (hcexp : cfg.cexp = (3/10 : ℝ))
    (D Bsave : ℝ) (hD : 0 ≤ D) (C : ℕ)
    (hExponent : cfg.C0*Real.log
      (((cfg.tmax.factorial : ℕ) : ℝ)*(max (1 : ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C : ℝ))
    (hSaving : Bsave+2*(C : ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2 : ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (x Y Hp : ℝ)
        (data : SourceComparisonData434 (sourceNativeOriginalTsType434 20 L hS)
          (sourceNativeOriginalBigType434 20 L) cfg x L Y Hp),
        SourceB636ParityActualGroupFields434 L hS data →
      ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ cfg.tmax →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (Q : ℕ) (hA hB xi : ℝ), 0 < hA → hA ≤ 1 → 0 < hB → hB ≤ 1 →
      ∀ (r : ParityPrimitiveRankIndex434 Q),
        r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi
          (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) →
      ∀ (zeta Z : ℝ) (k : ℤ), k ≠ 0 → ∀ (s theta : ℝ),
        (theta : AddCircle (1 : ℝ)) ∉ sourceCircleRationalArcs434
          ((2*k).natAbs*Nat.ceil (L^(D+1)))
          (L^cfg.Carc/(Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB))) →
      ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
          (theta : AddCircle (1 : ℝ))‖^2 ≤
        (sourceOriginalTwoCellCoefficient434
          (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hA)
          (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1)^2 *
          (2000*L^(-Bsave)) := by
  have hSource := eventually_source_original_true_five_index_unit_cell_minor434
    cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hSource,eventually_source_B636_parity_root_group_gates434] with L hMinor hg
  refine ⟨hg.1,?_⟩
  intro hS x Y Hp data hFields J m hmJ hm nu hnu Q hA hB xi hhA hA1 hhB hB1
    r hr zeta Z k hk s theta hOutside
  have hG := hg.2 hS cfg x Y Hp data hFields
  rcases hG with ⟨hsep,_,_,_,_,_,_,_,hLower,hMass,hDisj,_,_⟩
  rcases hFields with ⟨_,_,hTb,_,_,hV⟩
  have hLower' : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p : ℝ) := by
    simpa only [hcexp] using hLower
  have hMin := hMinor x Y Hp data hsep hMass
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    hDisj m Q hm hLower' (fun _ => hA) (fun _ => hB)
    (fun _ _ => ⟨hhA,hA1⟩) (fun _ _ => ⟨hhB,hB1⟩) xi
  rw [hTb,hV] at hMin
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let SA : nu.1 → Finset ℕ := fun z => P z.val.1
  let SB : nu.2 → Finset ℕ := fun z => P z.val.1
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let baseA := fun a : SourceOriginalGramPrimeTuple434 SA =>
    star (r.1.2.2 (pa a : ZMod (r.1.2.1.val+1))) *
      sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pa a)
  let baseB := fun b : SourceOriginalGramPrimeTuple434 SB =>
    star (r.2.2.2 (pb b : ZMod (r.2.2.1.val+1))) *
      sourceOriginalPureMellinPhase434 (zeta-2*Real.pi*s) (pb b)
  have hba (a : SourceOriginalGramPrimeTuple434 SA) : ‖baseA a‖ ≤ 1 := by
    simpa only [baseA,norm_mul,norm_star,source_original_pure_mellin_phase_norm_one434,mul_one]
      using r.1.2.2.norm_le_one (pa a : ZMod (r.1.2.1.val+1))
  have hbb (b : SourceOriginalGramPrimeTuple434 SB) : ‖baseB b‖ ≤ 1 := by
    simpa only [baseB,norm_mul,norm_star,source_original_pure_mellin_phase_norm_one434,mul_one]
      using r.2.2.2.norm_le_one (pb b : ZMod (r.2.2.1.val+1))
  have hz : (⟨nu,r⟩ : Σ ν : SourceOriginalProbePattern434
        (sourceNativeOriginalBigType434 20 L) m,ParityPrimitiveRankIndex434 Q) ∈
      sourceOriginalProbeExpandedFamily434 (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) m Q P V (fun _ => hA) (fun _ => hB) xi := by
    exact Finset.mem_sigma.mpr ⟨hnu,hr⟩
  have hTwo : (2*k : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hk
  have hh := hMin ⟨nu,r⟩ hz baseA baseB hba hbb theta (2*k) hTwo hOutside
  rw [parity_actual_cell_coupled_kernel_bilinear_norm_sq434 L J m hmJ nu hnu]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 28000

/-- The literal fixed source03 moment exponent for actual Parity endpoint
free multiplicity at most 1+mmax. It is chosen before L, any pattern,
active cell, character, Mellin frequency or endpoint data. -/
def parityCellKernelMomentExponent434 (mmax : ℕ) : ℕ :=
  ⌈4*Real.log (((1+mmax).factorial : ℝ)*
    (max (1 : ℝ) (Real.log (6/5 : ℝ)/2)⁻¹)^(1+mmax))⌉₊

/-- The full actual coupled-kernel minor estimate with no data-record or
auxiliary-existence hypothesis. Both actual cell inverse masses are still
explicitly present in the coefficient. The internal zero-cutoff group
record certifies only true r20 groups and masses; the original kernel,
Z, signed 2*k and all frequencies are left unchanged. -/
theorem parity_eventually_actual_cell_coupled_minor_sq434
    (mmax : ℕ) (D Bsave Carc : ℝ) (hD : 0 ≤ D)
    (hSaving : Bsave+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D)
    (hArc : D+2 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (Q : ℕ) (hA hB xi : ℝ), 0 < hA → hA ≤ 1 → 0 < hB → hB ≤ 1 → 0 < xi →
      ∀ (r : ParityPrimitiveRankIndex434 Q),
        r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi
          (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) →
      ∀ (zeta Z : ℝ) (k : ℤ), k ≠ 0 → ∀ (s theta : ℝ),
        (theta : AddCircle (1 : ℝ)) ∉ sourceCircleRationalArcs434
          ((2*k).natAbs*Nat.ceil (L^(D+1)))
          (L^Carc/(Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB))) →
      ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
          (theta : AddCircle (1 : ℝ))‖^2 ≤
        (sourceOriginalTwoCellCoefficient434
          (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hA)
          (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1)^2 *
          (2000*L^(-Bsave)) := by
  have hCarc : 1 ≤ Carc := by linarith
  let cfg := parityCellKernelGroupFixed434 mmax Carc hCarc
  let C := parityCellKernelMomentExponent434 mmax
  have hExponent : cfg.C0*Real.log
      (((cfg.tmax.factorial : ℕ) : ℝ)*(max (1 : ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C : ℝ) := by
    change 4*Real.log (((1+mmax).factorial : ℝ)*
      (max (1 : ℝ) (Real.log (6/5 : ℝ)/2)⁻¹)^(1+mmax)) ≤
        (⌈4*Real.log (((1+mmax).factorial : ℝ)*
          (max (1 : ℝ) (Real.log (6/5 : ℝ)/2)⁻¹)^(1+mmax))⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hMinor := parity_eventually_actual_cell_coupled_minor434 cfg rfl D Bsave hD C
    hExponent hSaving 1 (by norm_num) (by change 1+(D+1) ≤ Carc; linarith)
  have hData := parity_eventually_actual_cell_group_data434 mmax Carc hCarc
  filter_upwards [hMinor,hData] with L hm hd
  intro J m hmJ hmm nu hnu Q hA hB xi hhA hA1 hhB hB1 hxi r hr zeta Z k hk s theta hOutside
  have hmem := Finset.mem_product.mp hr
  have hja := (Finset.mem_product.mp hmem.1).1
  have hjb := (Finset.mem_product.mp hmem.2).1
  obtain ⟨data,hFields⟩ := hd.2 hd.1 J m hmJ hmm nu hnu hA hB xi hhA hhB hxi hA1 hB1
    r.1.1 r.2.1 hja hjb
  have hmt : m ≤ cfg.tmax := by change m ≤ 1+mmax; omega
  exact hm.2 hd.1 _ _ _ data hFields J m hmJ hmt nu hnu Q hA hB xi hhA hA1 hhB hB1
    r hr zeta Z k hk s theta hOutside

/-- Requested genuine minor saving for the actual coupled kernel,
uniform at ALL real Mellin frequencies, all Z and signed nonzero k.
Both original inverse cell masses are explicit. The loss 2*A+2+2*Cmoment
is paid before L; the harmless numerical 2000 is absorbed at large L.
No source-data, supplied auxiliary draw, minor-bound or small-Main
hypothesis is present. -/
theorem parity_eventually_actual_cell_coupled_minor_saving434
    (mmax : ℕ) (A D Carc : ℝ) (hD : 0 ≤ D)
    (hSaving : 2*A+2+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D)
    (hArc : D+2 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (Q : ℕ) (hA hB xi : ℝ), 0 < hA → hA ≤ 1 → 0 < hB → hB ≤ 1 → 0 < xi →
      ∀ (r : ParityPrimitiveRankIndex434 Q),
        r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi
          (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) →
      ∀ (zeta Z : ℝ) (k : ℤ), k ≠ 0 → ∀ (s theta : ℝ),
        (theta : AddCircle (1 : ℝ)) ∉ sourceCircleRationalArcs434
          ((2*k).natAbs*Nat.ceil (L^(D+1)))
          (L^Carc/(Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB))) →
      ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
          (theta : AddCircle (1 : ℝ))‖ ≤
        sourceOriginalTwoCellCoefficient434
          (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hA)
          (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
            (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1 * L^(-A) := by
  have hSq := parity_eventually_actual_cell_coupled_minor_sq434 mmax D (2*A+2) Carc hD hSaving hArc
  filter_upwards [hSq,eventually_ge_atTop (2000 : ℝ)] with L hsq hL
  intro J m hmJ hmm nu hnu Q hA hB xi hhA hA1 hhB hB1 hxi r hr zeta Z k hk s theta hOutside
  have hLp : 0 < L := by linarith
  have hb := hsq J m hmJ hmm nu hnu Q hA hB xi hhA hA1 hhB hB1 hxi r hr
    zeta Z k hk s theta hOutside
  let coeff := sourceOriginalTwoCellCoefficient434
    (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA)
    (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1
  have hmem := Finset.mem_product.mp hr
  have hja := (Finset.mem_product.mp hmem.1).1
  have hjb := (Finset.mem_product.mp hmem.2).1
  have hco : 0 ≤ coeff :=
    (source_original_two_cell_coefficient_bound434
      (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hA)
      (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1 xi hxi
      ((source_original_probe_active_cell_A_mem_iff434 m _ _ nu hA xi hhA hxi _).mp hja)
      ((source_original_probe_active_cell_B_mem_iff434 m _ _ nu hB xi hhB hxi _).mp hjb)).1
  have hLSq : 2000 ≤ L^2 := by
    have h1 : 1 ≤ L := by linarith
    calc
      _ ≤ L := hL
      _ = L*1 := by ring
      _ ≤ L*L := mul_le_mul_of_nonneg_left h1 hLp.le
      _ = L^2 := by ring
  have hPower : L^(-(2*A+2)) = (L^(-A))^2/L^2 := by
    have he : -(2*A+2) = (-A)+(-A)-(2 : ℝ) := by ring
    rw [he,Real.rpow_sub hLp,Real.rpow_add hLp,Real.rpow_two]
    ring
  have hCompare : 2000*L^(-(2*A+2)) ≤ (L^(-A))^2 := by
    rw [hPower]
    calc
      _ = (2000*(L^(-A))^2)/L^2 := by ring
      _ ≤ (L^(-A))^2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hLSq (sq_nonneg (L^(-A)))]
  have hBound : ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s
      (theta : AddCircle (1 : ℝ))‖^2 ≤ (coeff*L^(-A))^2 := by
    calc
      _ ≤ coeff^2*(2000*L^(-(2*A+2))) := hb
      _ ≤ coeff^2*(L^(-A))^2 := mul_le_mul_of_nonneg_left hCompare (sq_nonneg coeff)
      _ = (coeff*L^(-A))^2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hco (Real.rpow_nonneg hLp.le _))).mp hBound
end Green64Analytic.Parity

end

end

/-! ## GlobalRankEnergy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000

/-- Full-circle energy of both genuine actual rank endpoints on the
original positive carrier, with completely unrestricted Mellin and core
frequencies. The same eta is universally quantified by support/norm only;
there is no second existential cutoff to identify with the arc cutoff. -/
def ParityB633ActualGlobalRankCellEnergy434
    (cfg : SourceComparisonFixed434) (A L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma Kglobal Eglobal : ℝ) : Prop :=
  ∀ (eta : ℝ → ℂ),
    (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) → (∀ u : ℝ,‖eta u‖≤1) →
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s : ℝ),
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw sourceSide : Bool),
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let core:=if sourceSide then
    b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
    else b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let v:=if sourceSide then -(rho+xi3)-2*Real.pi*s else -rho
  let psi : ℝ → ℂ:=if sourceSide then (fun u=>eta u/(u : ℂ)) else eta
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let endpoint:=fun n : ℕ=>psi ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 core v tw sourceSide n
  (∫ theta : AddCircle (1 : ℝ),‖sourceNatFourierPoly N endpoint theta‖^2
    ∂AddCircle.haarAddCircle)≤Kglobal*Y*L^Eglobal

/-- Genuine full global actual endpoint budget, uniform over every real
Mellin frequency and every admissible common cutoff eta. The constants
are explicit functions of fixed source weights and A, before the fine
precision S, L and the whole operator tuple. Actual zero-frequency data
is used only to certify the original arithmetic/group/mark fields; the
primary full global theorem is applied to the true arbitrary frequencies.
No energy estimate for a zero endpoint is transferred. -/
theorem parity_eventually_B633_actual_global_rank_energy434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma A : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) (hA : 64≤A) :
    let cfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
      hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
    let Kg:=source_data_weight_constant434 cfg
    let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
    let Eglobal:=2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log Kg)+16
    0<Kglobal ∧ 0≤Eglobal ∧
    ∀ S : ℝ,0<S → ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ParityB633ActualGlobalRankCellEnergy434 cfg A L jQ mmax CZ Ck S beta gamma Kglobal Eglobal := by
  dsimp only
  let cfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
  let Kg:=source_data_weight_constant434 cfg
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  let Eglobal:=2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log Kg)+16
  have hKg : 1≤Kg:=source_data_weight_constant_ge434 cfg
  have hKgp : 0<Kg:=by linarith
  have hAs : 1≤A:=by linarith
  have hAp : 0<A:=by linarith
  have hlogA : 0≤Real.log (A+1):=Real.log_nonneg (by linarith)
  have hlogK : 0≤Real.log Kg:=Real.log_nonneg hKg
  have hC0 : 0≤ cfg.C0:=cfg.hC0
  refine ⟨by positivity,by positivity,?_⟩
  intro S hS
  have hData:=parity_eventually_actual_comparison_data434 jQ mmax cm 0 0 0 CZ Carc Cchi Ck
    0 S beta gamma hCZ hCk hcm hCarc hCchi hCchiPos (by norm_num) hS hbeta hgamma
    (fun _=>0) (by intro j;norm_num)
  have hScales:=Filter.eventually_all.mpr
    (fun m : Fin (mmax+1)=>parity_eventually_enlarged_comparison_cell_scales434
      A CZ Carc m.val hA hCZ ((Nat.cast_nonneg cm).trans hCarc))
  filter_upwards [hData,hScales,eventually_ge_atTop (3 : ℝ)] with L hd hscale hL
  refine ⟨hd.1,hd.2.1,?_⟩
  unfold ParityB633ActualGlobalRankCellEnergy434
  intro eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    prime lFine uFine a b hFineLow hl hu hub Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  have hLp : 0<L:=by linarith
  have hZeroBudget : sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun _ : ℝ=>(0 : ℂ)):=by
    intro j u
    simpa using (mul_nonneg (cfg.hKpsi j)
      (Real.rpow_nonneg hLp.le (cfg.Cpsi*((j : ℝ)+1))))
  have hz0 : |(0 : ℝ)|≤L^cfg.s0:=by
    simpa only [abs_zero] using (pow_nonneg hLp.le cfg.s0)
  have hz1 : |(0 : ℝ)|≤L^cfg.s1base:=by
    simpa only [abs_zero] using (pow_nonneg hLp.le cfg.s1base)
  have hzv : |(0 : ℝ)|≤L^cfg.vexp:=by
    simpa only [abs_zero] using (pow_nonneg hLp.le cfg.vexp)
  obtain ⟨data,hfields⟩:=hd.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu
    hAcell hB xi hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
    chi 0 0 0 hz0 hz1 hzv (fun _=>0) contDiff_const
    (by intro u hu;exact False.elim (hu rfl)) hZeroBudget
    prime lFine uFine a b hFineLow Qcomp aux hAux hAuxA hAuxB (fun _ _=>0) tw true
  obtain ⟨hz,hcap,hG,hTw,hSdata,hTs,hTb,hVs,hVm,hVb,hts,htb,hcoef,hk0,hAlpha,
    hlo,hhi,hcut,hF1,hF2,hp1,hp2,hU1,hU2,hQ,hc,hC,hq,hchi,hs0,hs1,hv,hpsi⟩:=hfields
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let core:=if sourceSide then
    b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
    else b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let v:=if sourceSide then -(rho+xi3)-2*Real.pi*s else -rho
  let psi : ℝ → ℂ:=if sourceSide then (fun u=>eta u/(u : ℂ)) else eta
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let row:=if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hAcell ja ca
  have hRank : ∀ marks,‖row marks‖≤1:=by
    intro marks
    have hh:=parity_actual_rank_mark_norm434 J 1 m hmJ nu hAcell hB ja jb ca cb marks
    cases sourceSide
    · exact hh.2
    · exact hh.1
  let ranked : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L Y Hp:=
    {data with
      tb:=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
      coef:=row
      htb:=fun g=>(source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans
        (by change 1+m≤1+mmax;omega)
      hcoef:=hRank}
  have hY : 0<Y:=by linarith [ranked.hY]
  have hInv:=parity_common_cutoff_inverse_bound434 A hAs eta hSupp hNorm
  have hPsiSupport : ∀ u : ℝ,psi u≠0 → 1/A≤u ∧ u≤A:=by
    cases sourceSide
    · exact hSupp
    · exact hInv.2
  have hPsiNorm : ∀ u : ℝ,‖psi u‖≤A:=by
    cases sourceSide
    · exact fun u=>(hNorm u).trans hAs
    · exact hInv.1
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let M:=Finset.Icc 1 ⌈A*Y⌉₊
  let U:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    core v tw sourceSide n
  have hgeo:=(hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hAcell hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  have hCap : (⌈A*Y⌉₊ : ℝ)≤Real.exp (2*L):=by
    calc
      _≤(Real.exp L)^2:=hgeo.2.1
      _=Real.exp (2*L):=by rw [pow_two,←Real.exp_add];congr 1;ring
  have hCarrier : sourceNatFourierPoly N (fun n : ℕ=>psi ((n : ℝ)/Y)*U n)=
      sourceNatFourierPoly M (fun n : ℕ=>psi ((n : ℝ)/Y)*U n):=
    parity_actual_cell_fourier_carrier434 J Ck L hLp A Y hAs hY psi hPsiSupport hCap U
  have hFull : sourceOriginalFullEndpointCoefficients434 ranked.qBase ranked.S ranked.Ts ranked.Tb cfg.q0
      ranked.Vs ranked.Vsmall ranked.Vbig ranked.ts ranked.tb ranked.coef ranked.k ranked.primeSlot
      ranked.alphaCut ranked.c ranked.chi0
      (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma) (fun n=>psi ((n : ℝ)/Y)*sourcePhase n v)=
    sourceOriginalFullEndpointCoefficients434 (2*k.natAbs)
      (sourceNativeOriginalS434 20 L hFamily) (sourceNativeOriginalTs434 20 L hFamily)
      (sourceNativeOriginalTb434 20 L) cfg.q0 (sourceNativeOriginalVs434 20 L hFamily)
      (sourceNativeOriginalVsmall434 20 L hFamily) (sourceNativeOriginalVbig434 20 L)
      (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) row 0
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band)
      F.alpha (fun n=>star (F.residual n)) (chi.ringHomComp (starRingEnd ℂ))
      (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma) (fun n=>psi ((n : ℝ)/Y)*sourcePhase n v):=by
    dsimp only [ranked]
    congr 1
  have hpoly : sourceCircleFourierPoly (M.image (fun n : ℕ=>(n : ℤ)))
      (sourceSignedCoefficients434 (if tw then sourceNativeOriginalG434 20 L else ∅) true
        (sourceOriginalFullEndpointCoefficients434 ranked.qBase ranked.S ranked.Ts ranked.Tb cfg.q0
          ranked.Vs ranked.Vsmall ranked.Vbig ranked.ts ranked.tb ranked.coef ranked.k ranked.primeSlot
          ranked.alphaCut ranked.c ranked.chi0 (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma)
          (fun n=>psi ((n : ℝ)/Y)*sourcePhase n v)))=
      sourceNatFourierPoly M (fun n : ℕ=>psi ((n : ℝ)/Y)*U n):=by
    rw [hFull]
    unfold sourceNatFourierPoly sourceCircleFourierPoly
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hz
    have he:=parity_actual_B633_rank_cutoff_original434 L (by linarith) hFamily J m hmJ nu
      hAcell hB rank cfg.q0 band slot delta freq k chi prime S gamma lFine uFine a b
      xi1 xi2 xi3 rho sigma s Y eta tw sourceSide n
      (by have hh:=(Finset.mem_Icc.mp hn).1;omega)
    rw [←he]
    rfl
  have hg:=parity_source_data_free_frequency_global434 cfg (Real.exp L) L Y Hp hL ranked
    A A hAs hAp.le psi hPsiSupport hPsiNorm ⌈A*Y⌉₊
    (if tw then sourceNativeOriginalG434 20 L else ∅)
    (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma) v
  rw [hpoly] at hg
  rw [←hCarrier] at hg
  exact hg
end Green64Analytic.Parity

end

end

/-! ## HarmonicHaarEnergy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Balanced Cauchy on the actual Haar circle. All integrability follows
from continuity on this compact space. The first energy B/Y and second
energy B*Y give the product bound B with no residual scale factor. -/
theorem parity_harmonic_haar_cauchy434
    (Y B : ℝ) (hY : 0<Y) (f g : C(AddCircle (1 : ℝ),ℂ))
    (hFirst : (∫ theta : AddCircle (1 : ℝ),‖f theta‖^2
      ∂AddCircle.haarAddCircle)≤B/Y)
    (hSecond : (∫ theta : AddCircle (1 : ℝ),‖g theta‖^2
      ∂AddCircle.haarAddCircle)≤B*Y) :
    (∫ theta : AddCircle (1 : ℝ),‖star (f theta)*g theta‖
      ∂AddCircle.haarAddCircle)≤B := by
  have hfi : Integrable (fun theta=>‖f theta‖^2) AddCircle.haarAddCircle := by
    have hc : Continuous (fun theta=>‖f theta‖^2) := by fun_prop
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hgi : Integrable (fun theta=>‖g theta‖^2) AddCircle.haarAddCircle := by
    have hc : Continuous (fun theta=>‖g theta‖^2) := by fun_prop
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hprod : Integrable (fun theta=>‖f theta‖*‖g theta‖) AddCircle.haarAddCircle := by
    have hc : Continuous (fun theta=>‖f theta‖*‖g theta‖) := by fun_prop
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hpoint (theta : AddCircle (1 : ℝ)) :
      (2*Y)*(‖f theta‖*‖g theta‖)≤Y^2*‖f theta‖^2+‖g theta‖^2 := by
    nlinarith [sq_nonneg (Y*‖f theta‖-‖g theta‖)]
  have hi:=integral_mono (hprod.const_mul (2*Y)) ((hfi.const_mul (Y^2)).add hgi) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hfi.const_mul (Y^2)) hgi,integral_const_mul] at hi
  have hbudget : Y^2*(B/Y)+B*Y=(2*Y)*B := by
    field_simp [hY.ne']
    <;> ring
  have hupper :
      Y^2*(∫ theta : AddCircle (1 : ℝ),‖f theta‖^2 ∂AddCircle.haarAddCircle)+
        (∫ theta : AddCircle (1 : ℝ),‖g theta‖^2 ∂AddCircle.haarAddCircle)≤(2*Y)*B := by
    calc
      _≤Y^2*(B/Y)+B*Y := add_le_add (mul_le_mul_of_nonneg_left hFirst (sq_nonneg Y)) hSecond
      _=(2*Y)*B := hbudget
  simp only [norm_mul,norm_star]
  exact (mul_le_mul_iff_right₀ (by positivity : 0<2*Y)).mp (hi.trans hupper)

/-- The genuine full typed-auxiliary kernel, with both inverse cell
masses and its c-dependent Mellin/additive phase still present, contracts
the full circle product integral. The actual conditional-cell theorem
proves the norm bound, including zero masses; no kernel-smallness input
or unjustified auxiliary independence is used. -/
theorem parity_actual_coupled_circle_domination434
    (L : ℝ) (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu∈sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) (f g : C(AddCircle (1 : ℝ),ℂ)) :
    ‖∫ theta : AddCircle (1 : ℝ),star (f theta)*g theta*
      parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta
      ∂AddCircle.haarAddCircle‖≤
    ∫ theta : AddCircle (1 : ℝ),‖star (f theta)*g theta‖ ∂AddCircle.haarAddCircle := by
  have hKernel : Continuous (fun theta : AddCircle (1 : ℝ)=>
      parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta) := by
    unfold parityActualCellCoupledKernel434
    fun_prop
  have hInt : Integrable (fun theta : AddCircle (1 : ℝ)=>star (f theta)*g theta*
      parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta)
      AddCircle.haarAddCircle := by
    have hc : Continuous (fun theta : AddCircle (1 : ℝ)=>star (f theta)*g theta*
        parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta) := by fun_prop
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hProd : Integrable (fun theta : AddCircle (1 : ℝ)=>‖star (f theta)*g theta‖)
      AddCircle.haarAddCircle := by
    have hc : Continuous (fun theta : AddCircle (1 : ℝ)=>‖star (f theta)*g theta‖) := by fun_prop
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  calc
    _≤∫ theta : AddCircle (1 : ℝ),‖star (f theta)*g theta*
        parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta‖
        ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _≤_ := integral_mono hInt.norm hProd (fun theta=>by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (parity_actual_cell_coupled_kernel_norm434 L J m hmJ nu hnu hA hB r zeta Z k s theta))
end Green64Analytic.Parity

end

end

/-! ## HarmonicGlobal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 28000

/-- Genuine full-circle harmonic first/second energies and actual coupled
rank-mode amplitude, for arbitrary real Mellin and core frequencies.
The original positive carrier and complete endpoint marks remain literal.
Both active cells are inputs, but no auxiliary witness is supplied: its
existence is derived from the two original positive cell probabilities.
The common eta is universal and can be exactly the constructed arc eta. -/
def ParityB633ActualHarmonicGlobalCellEnergy434
    (cfg : SourceComparisonFixed434) (A L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma Kglobal Eglobal : ℝ) : Prop :=
  ∀ (eta : ℝ → ℂ),
    (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) → (∀ u : ℝ,‖eta u‖≤1) →
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s zeta : ℝ),
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw : Bool),
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 G (-rho) tw false n)
  (∫ theta : AddCircle (1 : ℝ),‖first theta‖^2 ∂AddCircle.haarAddCircle)≤
    (Kglobal/Y)*L^Eglobal ∧
  (∫ theta : AddCircle (1 : ℝ),‖second theta‖^2 ∂AddCircle.haarAddCircle)≤
    Kglobal*Y*L^Eglobal ∧
  (∫ theta : AddCircle (1 : ℝ),‖star (first theta)*second theta‖
    ∂AddCircle.haarAddCircle)≤Kglobal*L^Eglobal ∧
  ‖∫ theta : AddCircle (1 : ℝ),star (first theta)*second theta*
    parityActualCellCoupledKernel434 L J m hmJ nu hA hB rank zeta Z k s theta
    ∂AddCircle.haarAddCircle‖≤Kglobal*L^Eglobal

/-- Construct all actual endpoint certificates and derive harmonic Y
cancellation on the complete Haar circle. Kglobal and Eglobal are fixed
before S,L,eta and every operator tuple. The original conditional-cell
kernel, with both inverse cell masses and its coupled shift/phase, remains
inside the integral; its contraction is proved. There is no frequency
cutoff, endpoint norm, kernel-smallness, supplied-auxiliary or Main-saving
hypothesis. This polynomial bound is an input for later minor/tail saving. -/
theorem parity_eventually_B633_actual_harmonic_global434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma A : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) (hA : 64≤A) :
    let cfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
      hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
    let Kg:=source_data_weight_constant434 cfg
    let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
    let Eglobal:=2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log Kg)+16
    0<Kglobal ∧ 0≤Eglobal ∧
    ∀ S : ℝ,0<S → ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ParityB633ActualHarmonicGlobalCellEnergy434 cfg A L jQ mmax CZ Ck S beta gamma Kglobal Eglobal := by
  dsimp only
  let cfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
  let Kg:=source_data_weight_constant434 cfg
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  let Eglobal:=2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log Kg)+16
  have hGlobal:=parity_eventually_B633_actual_global_rank_energy434
    jQ mmax cm CZ Carc Cchi Ck beta gamma A hCZ hCk hcm hCarc hCchi hCchiPos hbeta hgamma hA
  refine ⟨hGlobal.1,hGlobal.2.1,?_⟩
  intro S hS
  filter_upwards [hGlobal.2.2 S hS,eventually_ge_atTop (3 : ℝ)] with L hGlobalL hL
  refine ⟨hGlobalL.1,hGlobalL.2.1,?_⟩
  unfold ParityB633ActualHarmonicGlobalCellEnergy434
  intro eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s zeta
    prime lFine uFine a b hFineLow hl hu hub Qcomp ca cb tw
  obtain ⟨aux,hAux,hAuxA,hAuxB⟩:=parity_active_cells_joint_aux434 m nu
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    hAcell hB xi hhA hhB hxi ja jb ha hb
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let U:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    E (-(rho+xi3)) tw true n
  let V:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    G (-rho) tw false n
  let Ub:=fun n : ℕ=>(eta ((n : ℝ)/Y)/(((n : ℝ)/Y : ℝ) : ℂ))*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
      E (-(rho+xi3)-2*Real.pi*s) tw true n
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*V n)
  let firstBase:=sourceNatFourierPoly N Ub
  have hLp : 0<L:=by linarith
  have hZ : 0<Z:=(mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hY : 0<Y:=by dsimp [Y,Hp];positivity
  have hEach (side : Bool):=
    hGlobalL.2.2 eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi
      hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
      chi rho xi1 xi2 xi3 sigma s prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw side
  have hFirstBase : (∫ theta : AddCircle (1 : ℝ),‖firstBase theta‖^2
      ∂AddCircle.haarAddCircle)≤Kglobal*Y*L^Eglobal:=hEach true
  have hSecond : (∫ theta : AddCircle (1 : ℝ),‖second theta‖^2
      ∂AddCircle.haarAddCircle)≤Kglobal*Y*L^Eglobal:=hEach false
  have hFirstScale : first=(Y : ℂ)⁻¹ • firstBase:=by
    unfold first
    have heq : parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n)=
        (fun n : ℕ=>(Y : ℂ)⁻¹*Ub n):=by
      funext n
      exact parity_actual_cell_mellin_first_endpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
        E (-(rho+xi3)) s Y hY tw true eta n
    rw [heq]
    exact parity_nat_fourier_const_mul434 N ((Y : ℂ)⁻¹) Ub
  have hFirstValue (theta : AddCircle (1 : ℝ)) : first theta=(Y : ℂ)⁻¹*firstBase theta:=by
    rw [hFirstScale]
    rfl
  have hScalar : ‖(Y : ℂ)⁻¹‖^2=(Y⁻¹)^2:=by simp [norm_inv,abs_of_pos hY]
  have hFirst : (∫ theta : AddCircle (1 : ℝ),‖first theta‖^2
      ∂AddCircle.haarAddCircle)≤(Kglobal/Y)*L^Eglobal:=by
    calc
      _=(Y⁻¹)^2*(∫ theta : AddCircle (1 : ℝ),‖firstBase theta‖^2
          ∂AddCircle.haarAddCircle):=by
        simp_rw [hFirstValue,norm_mul,mul_pow,hScalar]
        rw [integral_const_mul]
      _≤(Y⁻¹)^2*(Kglobal*Y*L^Eglobal):=
        mul_le_mul_of_nonneg_left hFirstBase (sq_nonneg _)
      _=(Kglobal/Y)*L^Eglobal:=by field_simp [hY.ne']
  have hProduct : (∫ theta : AddCircle (1 : ℝ),‖star (first theta)*second theta‖
      ∂AddCircle.haarAddCircle)≤Kglobal*L^Eglobal:=by
    apply parity_harmonic_haar_cauchy434 Y (Kglobal*L^Eglobal) hY first second
    · convert hFirst using 1 <;> ring
    · convert hSecond using 1 <;> ring
  exact ⟨hFirst,hSecond,hProduct,
    (parity_actual_coupled_circle_domination434 L J m hmJ nu hnu hAcell hB rank zeta Z k s
      first second).trans hProduct⟩
end Green64Analytic.Parity

end

end

/-! ## CoupledCircleSplit -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

/-- The actual finite coupled auxiliary kernel is continuous on the
circle for every real Mellin frequency, with every true mass and gate
unchanged. No source probability estimate is needed for continuity. -/
theorem parity_actual_cell_coupled_kernel_continuous434
    (L : ℝ) (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) :
    Continuous (fun theta : AddCircle (1:ℝ) =>
      parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta) := by
  unfold parityActualCellCoupledKernel434
  dsimp only
  fun_prop

/-- Split the genuine continuous coupled circle integral using a small
MAJOR product integral and an unrestricted-frequency GLOBAL product
integral. The minor coefficient is retained linearly, so both original
inverse cell masses can be paid by the later exact family cost. -/
theorem parity_circle_product_major_minor434
    (F G M : C(AddCircle (1:ℝ),ℂ))
    (major : Set (AddCircle (1:ℝ))) (hMajorMeas : MeasurableSet major)
    (delta Bmajor Bglobal : ℝ) (hdelta : 0≤delta)
    (hBound : ∀ theta,‖M theta‖≤1)
    (hMinor : ∀ theta,theta∉major → ‖M theta‖≤delta)
    (hMajor : (∫ theta in major,‖star (F theta)*G theta‖
      ∂AddCircle.haarAddCircle)≤Bmajor)
    (hGlobal : (∫ theta,‖star (F theta)*G theta‖
      ∂AddCircle.haarAddCircle)≤Bglobal) :
    ‖∫ theta,M theta*star (F theta)*G theta ∂AddCircle.haarAddCircle‖≤
      Bmajor+delta*Bglobal := by
  let W := fun theta : AddCircle (1:ℝ)=>M theta*star (F theta)*G theta
  let b := fun theta : AddCircle (1:ℝ)=>‖star (F theta)*G theta‖
  have hWc : Continuous W := (M.continuous.mul F.continuous.star).mul G.continuous
  have hbc : Continuous b := (F.continuous.star.mul G.continuous).norm
  have hWi : Integrable W AddCircle.haarAddCircle := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hWc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hbi : Integrable b AddCircle.haarAddCircle := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hbc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hNorm (theta : AddCircle (1:ℝ)) : ‖W theta‖=‖M theta‖*b theta := by
    dsimp only [W,b]
    rw [mul_assoc,norm_mul]
  have hb0 (theta : AddCircle (1:ℝ)) : 0≤b theta:=norm_nonneg _
  have hMpoint (theta : AddCircle (1:ℝ)) : ‖W theta‖≤b theta := by
    rw [hNorm]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hBound theta) (hb0 theta)
  have hMI : ‖∫ theta in major,W theta ∂AddCircle.haarAddCircle‖≤Bmajor := by
    calc
      _≤∫ theta in major,‖W theta‖ ∂AddCircle.haarAddCircle :=
        norm_integral_le_integral_norm _
      _≤∫ theta in major,b theta ∂AddCircle.haarAddCircle :=
        integral_mono hWi.norm.integrableOn hbi.integrableOn hMpoint
      _≤Bmajor := hMajor
  have hminorNorm :
      (∫ theta in majorᶜ,‖W theta‖ ∂AddCircle.haarAddCircle)≤
      ∫ theta in majorᶜ,delta*b theta ∂AddCircle.haarAddCircle := by
    apply integral_mono_ae hWi.norm.integrableOn (hbi.const_mul delta).integrableOn
    exact (ae_restrict_mem hMajorMeas.compl).mono (fun theta htheta=>by
      change ‖W theta‖≤delta*b theta
      rw [hNorm]
      exact mul_le_mul_of_nonneg_right (hMinor theta htheta) (hb0 theta))
  rw [integral_const_mul] at hminorNorm
  have hcomp :
      (∫ theta in majorᶜ,b theta ∂AddCircle.haarAddCircle)≤
      ∫ theta,b theta ∂AddCircle.haarAddCircle :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hb0) hbi
  have hminorI : ‖∫ theta in majorᶜ,W theta ∂AddCircle.haarAddCircle‖≤delta*Bglobal := by
    calc
      _≤∫ theta in majorᶜ,‖W theta‖ ∂AddCircle.haarAddCircle :=
        norm_integral_le_integral_norm _
      _≤delta*(∫ theta in majorᶜ,b theta ∂AddCircle.haarAddCircle) := hminorNorm
      _≤delta*Bglobal := mul_le_mul_of_nonneg_left (hcomp.trans hGlobal) hdelta
  change ‖∫ theta,W theta ∂AddCircle.haarAddCircle‖≤_
  rw [←integral_add_compl hMajorMeas hWi]
  exact (norm_add_le _ _).trans (add_le_add hMI hminorI)

/-- The source minor denominator uses the ACTUAL signed shift2*k.
The factor2 from that shift and the ceiling loss fit in two additional
powers for L>=2. All exponent choices precede L and the mask tuple. -/
theorem parity_actual_minor_denominator_budget434
    (L Ck D : ℝ) (cm : ℕ) (hL : 2≤L) (hD : 0≤D)
    (hcm : Ck+D+3≤(cm : ℝ)) (k : ℤ)
    (hk : (k.natAbs : ℝ)≤L^Ck) :
    (((2*k).natAbs*Nat.ceil (L^(D+1)) : ℕ) : ℝ)≤L^cm := by
  have hLp : 0<L:=by linarith
  have hL1 : 1≤L:=by linarith
  have hPow : 1≤L^(D+1):=Real.one_le_rpow hL1 (by linarith)
  have hCeil : (Nat.ceil (L^(D+1)) : ℝ)≤2*L^(D+1) := by
    have h:= (Nat.ceil_lt_add_one (by positivity : 0≤L^(D+1))).le
    linarith
  have hFour : (4:ℝ)≤L^2:=by nlinarith
  have hAbs : ((2*k).natAbs : ℝ)=2*(k.natAbs : ℝ):=by
    norm_num [Int.natAbs_mul]
  calc
    _=2*(k.natAbs : ℝ)*(Nat.ceil (L^(D+1)) : ℝ):=by
      rw [Nat.cast_mul,hAbs]
    _≤2*L^Ck*(2*L^(D+1)):=by gcongr
    _=4*L^(Ck+D+1):=by
      have he : L^Ck*L^(D+1)=L^(Ck+D+1):=by
        rw [←Real.rpow_add hLp]
        congr 1
        ring
      calc
        _=4*(L^Ck*L^(D+1)):=by ring
        _=4*L^(Ck+D+1):=by rw [he]
    _≤L^2*L^(Ck+D+1):=
      mul_le_mul_of_nonneg_right hFour (Real.rpow_nonneg hLp.le _)
    _=L^(Ck+D+3):=by
      rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
      congr 1
      norm_num
      ring
    _≤L^(cm : ℝ):=Real.rpow_le_rpow_of_exponent_le hL1 hcm
    _=L^cm:=Real.rpow_natCast L cm
end Green64Analytic.Parity

end

end

/-! ## GlobalBudgetFixed -/

section

open Filter Real
open scoped Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- The original full-marked global constant depends only on the fixed
maximum number of free marks. These three scalar inputs are the actual
Parity source q0, harmonic lower mass and free-mark cap. The actual r20
Q-band geometry is not replaced by the old r6 geometry. -/
def parityGlobalMarkConstant434 (mmax : ℕ) : ℝ :=
  Classical.choose (source_original_full_global_log_budget434
    (1/2) (Real.log (6/5 : ℝ)/2) (1+mmax)
    (by norm_num) (by norm_num)
    (by exact div_pos (Real.log_pos (by norm_num)) (by norm_num)))

/-- A global energy exponent fixed before every arc/minor exponent,
scale, cutoff, character modulus and operator tuple. -/
def parityGlobalMarkExponent434 (mmax : ℕ) : ℝ :=
  16*Real.log (parityGlobalMarkConstant434 mmax)+16

theorem parity_global_mark_constant_ge434 (mmax : ℕ) :
    1≤parityGlobalMarkConstant434 mmax :=
  (Classical.choose_spec (source_original_full_global_log_budget434
    (1/2) (Real.log (6/5 : ℝ)/2) (1+mmax)
    (by norm_num) (by norm_num)
    (by exact div_pos (Real.log_pos (by norm_num)) (by norm_num)))).1

/-- Exact constant identity for the full Parity fixed record, even when all
arc, character, derivative and frequency parameters vary. The source
choice theorem uses only q0,vmin,tmax; its proof arguments are irrelevant. -/
theorem parity_global_mark_constant_fixed434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi : ℝ)
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (Cpsi : ℝ) (hCpsi : 0≤Cpsi) (Kpsi : ℕ → ℝ) (hKpsi : ∀ j,0≤Kpsi j) :
    let cfg:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    source_data_weight_constant434 cfg=parityGlobalMarkConstant434 mmax := by
  rfl

/-- Exact unrestricted-frequency global exponent used by the new actual
B633 bounds. It is independent of cm,Carc,Cchi,CZ,jQ,all frequencies and
A/eta, so a minor saving exponent may be selected BEFORE those parameters.
This is the displayed exponent of the norm-only cutoff theorem; it does
not identify arbitrary positive-Cpsi source derivative budgets with zero. -/
theorem parity_global_mark_exponent_fixed434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi : ℝ)
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (Cpsi : ℝ) (hCpsi : 0≤Cpsi) (Kpsi : ℕ → ℝ) (hKpsi : ∀ j,0≤Kpsi j) :
    let cfg:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log (source_data_weight_constant434 cfg))+16=
      parityGlobalMarkExponent434 mmax := by
  dsimp only
  rw [parity_global_mark_constant_fixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi]
  simp only [parityComparisonFixed434,sourceNativeOriginalR6Fixed434,
    parityGlobalMarkExponent434,Nat.cast_zero]
  ring

/-- Explicit K(A,mmax) and E(mmax) actual global corollary. It permits
choosing the minor precision from the fixed free-mark exponent before
cm/Carc, while the later cutoff width A affects only a multiplicative
constant. The same universal eta and complete genuine actual property
are retained, without a supplied auxiliary witness. -/
theorem parity_eventually_B633_actual_harmonic_global_fixed434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma A : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) (hA : 64≤A) :
    let cfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
      hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
    let Kg:=parityGlobalMarkConstant434 mmax
    let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
    let Eglobal:=parityGlobalMarkExponent434 mmax
    0<Kglobal ∧ 0≤Eglobal ∧
    ∀ S : ℝ,0<S → ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ParityB633ActualHarmonicGlobalCellEnergy434 cfg A L jQ mmax CZ Ck S beta gamma Kglobal Eglobal := by
  have h:=parity_eventually_B633_actual_harmonic_global434
    jQ mmax cm CZ Carc Cchi Ck beta gamma A hCZ hCk hcm hCarc hCchi hCchiPos hbeta hgamma hA
  dsimp only at h ⊢
  rw [parity_global_mark_exponent_fixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)] at h
  rw [parity_global_mark_constant_fixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)] at h
  exact h
end Green64Analytic.Parity

end

end

/-! ## CoupledCircleBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 30000

/-- The genuine fixed-rank coupled circle integral of the actual B633
endpoints. The minor coefficient contains BOTH original inverse cell
masses; it is retained linearly beside the complete major-union bound.
No auxiliary witness, endpoint energy or kernel-smallness input occurs. -/
def ParityB633ActualCoupledRankCircleBound434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma majorSaving Karc Cfreq Ftail minorSaving Kglobal : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s : ℝ),
    |rho|≤L^Cfreq → |xi1|≤L^Cfreq → |xi2|≤L^Cfreq → |xi3|≤L^Cfreq →
    |sigma|≤L^Cfreq → |s|≤L^Ftail →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)),
    ca∈sourceOriginalActualPrimitiveCharacters434 Qcomp →
    cb∈sourceOriginalActualPrimitiveCharacters434 Qcomp →
  ∀ tw : Bool,
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 G (-rho) tw false n)
  let coeff:=sourceOriginalTwoCellCoefficient434
    (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA)
    (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB) ja jb
  ‖∫ theta : AddCircle (1:ℝ),
    parityActualCellCoupledKernel434 L J m hmJ nu hA hB rank (-xi3) Z k s theta*
      star (first theta)*second theta ∂AddCircle.haarAddCircle‖≤
    2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving)+
      coeff*Kglobal*L^(parityGlobalMarkExponent434 mmax-minorSaving)

/-- Construct a complete actual major/minor circle bound and its
unrestricted-frequency global companion before the operator tuple.
All precision choices D,cm,Carc and requested major/minor powers precede
the common cutoff and L. The exact global exponent depends only on mmax.
The full actual auxiliary law remains inside the integral throughout. -/
theorem parity_eventually_B633_actual_coupled_circle_bound434
    (jQ mmax cm : ℕ)
    (CZ Carc Cchi Ck beta gamma majorSaving Cfreq Ftail minorSaving D : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hD : 0≤D)
    (hMinorSaving : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ)≤D)
    (hcm : Ck+D+3≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hMinorArc : D+2≤Carc) (hbeta : 0<beta) (hgamma : 0<gamma) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    let gcfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
      hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        let Kg:=parityGlobalMarkConstant434 mmax
        let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
        0<Kglobal ∧ 0≤parityGlobalMarkExponent434 mmax ∧
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicGlobalCellEnergy434 gcfg A L jQ mmax CZ Ck S beta gamma
              Kglobal (parityGlobalMarkExponent434 mmax) ∧
            ParityB633ActualCoupledRankCircleBound434 cfg eta L jQ mmax CZ Ck S beta gamma
              majorSaving Karc Cfreq Ftail minorSaving Kglobal := by
  dsimp only
  have hcm0 : Ck+1≤(cm : ℝ):=by linarith
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_harmonic_circle_major434 jQ mmax cm CZ Carc Cchi Ck beta gamma
      majorSaving Cfreq Ftail hCZ hCk hcm0 hCarc hCchi hCchiPos hbeta hgamma
  have hGlobal:=parity_eventually_B633_actual_harmonic_global_fixed434
    jQ mmax cm CZ Carc Cchi Ck beta gamma A hCZ hCk hcm0 hCarc hCchi hCchiPos hbeta hgamma hA
  have hMinor:=parity_eventually_actual_cell_coupled_minor_saving434
    mmax minorSaving D Carc hD hMinorSaving hMinorArc
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hGlobal.1,hGlobal.2.1,
    Karc,hKarc,B,S,hSB,?_⟩
  have hSpos : 0<S:=by nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  let cfg0:=parityComparisonFixed434 jQ mmax cm ⌈Cfreq+1⌉₊ ⌈Cfreq⌉₊
    ⌈max Cfreq Ftail+1⌉₊ CZ Carc Cchi hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  let Kg:=parityGlobalMarkConstant434 mmax
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  filter_upwards [hArc,hGlobal.2.2 S hSpos,hMinor,eventually_ge_atTop (2 : ℝ)]
    with L hArcL hGlobalL hMinorL hL
  refine ⟨hArcL.1,hArcL.2.1,hGlobalL.2.2,?_⟩
  unfold ParityB633ActualCoupledRankCircleBound434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp ca cb hca hcb tw
  obtain ⟨aux,hAux,hAuxA,hAuxB⟩:=parity_active_cells_joint_aux434 m nu
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    hAcell hB xi hhA hhB hxi ja jb ha hb
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 G (-rho) tw false n)
  let coeff:=sourceOriginalTwoCellCoefficient434
    (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hAcell)
    (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB) ja jb
  let Qmajor:=(2*k).natAbs*Nat.ceil (L^(D+1))
  let major:=sourceCircleRationalArcs434 Qmajor (L^cfg.Carc/Hp)
  let M : C(AddCircle (1:ℝ),ℂ):=
    ⟨fun theta=>parityActualCellCoupledKernel434 L J m hmJ nu hAcell hB rank (-xi3) Z k s theta,
      parity_actual_cell_coupled_kernel_continuous434 L J m hmJ nu hAcell hB rank (-xi3) Z k s⟩
  have hRank : rank∈parityCanonicalRankIndices434 m nu Qcomp hAcell hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L):=
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha,hca⟩,
      Finset.mem_product.mpr ⟨hb,hcb⟩⟩
  have hDen : (Qmajor : ℝ)≤L^cfg.cm:=
    parity_actual_minor_denominator_budget434 L Ck D cm hL hD hcm k hKcap
  have hMajorBound:=
    (hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw Qmajor hDen).2.2
  have hGlobalBound:=
    (hGlobalL.2.2 eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi
      hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
      chi rho xi1 xi2 xi3 sigma s (-xi3) prime lFine uFine a b hFineLow hl hu hub
      Qcomp ca cb tw).2.2.1
  have hLp : 0<L:=by linarith
  have hco : 0≤ coeff:=
    (source_original_two_cell_coefficient_bound434
      (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hAcell)
      (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hB) ja jb xi hxi
      ((source_original_probe_active_cell_A_mem_iff434 m _ _ nu hAcell xi hhA hxi ja).mp ha)
      ((source_original_probe_active_cell_B_mem_iff434 m _ _ nu hB xi hhB hxi jb).mp hb)).1
  have hMin : ∀ theta,theta∉major → ‖M theta‖≤ coeff*L^(-minorSaving):=by
    intro theta hOutside
    obtain ⟨t,ht⟩:=Quotient.exists_rep theta
    subst theta
    exact hMinorL J m hmJ hmm nu hnu Qcomp hAcell hB xi hhA hA1 hhB hB1 hxi
      rank hRank (-xi3) Z k hk s t hOutside
  have hBound:=parity_circle_product_major_minor434 first second M major
    (source_circle_rational_arcs_measurable434 Qmajor (L^cfg.Carc/Hp))
    (coeff*L^(-minorSaving)) (2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving))
    (Kglobal*L^(parityGlobalMarkExponent434 mmax))
    (mul_nonneg hco (Real.rpow_nonneg hLp.le _))
    (fun theta=>parity_actual_cell_coupled_kernel_norm434
      L J m hmJ nu hnu hAcell hB rank (-xi3) Z k s theta)
    hMin hMajorBound hGlobalBound
  have hPower : L^(-minorSaving)*L^(parityGlobalMarkExponent434 mmax)=
      L^(parityGlobalMarkExponent434 mmax-minorSaving):=by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hFactor : (coeff*L^(-minorSaving))*(Kglobal*L^(parityGlobalMarkExponent434 mmax))=
      coeff*Kglobal*L^(parityGlobalMarkExponent434 mmax-minorSaving):=by
    calc
      _=(coeff*Kglobal)*(L^(-minorSaving)*L^(parityGlobalMarkExponent434 mmax)):=by ring
      _=_:=by rw [hPower]
  exact hBound.trans_eq (congrArg
    (fun t : ℝ=>2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving)+t) hFactor)
end Green64Analytic.Parity

end

end

/-! ## CoupledFamilyBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Quantitative bounds for the already independently defined localized
actual coupled-circle FAMILY. The global estimate is uniform over all
real frequencies. The low-frequency estimate retains a separate major
count and minor coefficient cost: BOTH inverse true cell masses appear
in the latter. No pointwise equality with the unlocalized Mellin family
is asserted, and no original Main is redefined by this proposition. -/
def ParityB633ActualCoupledCircleFamilyBounds434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma CQ Cxi majorSaving Karc Cfreq Ftail minorSaving Kglobal : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ)  ≤  Z → Z  ≤  Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (h xi : ℝ), 0<h → h ≤ 1 → 0<xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs : ℝ) ≤ L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
  ∀ Q : ℕ,(Q : ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi → ∀ tw : Bool,
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let EF:=(m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let amplitude:=parityActualCellCoupledCircleFamily434 L hFamily J m hmJ Q h xi rho xi3 Ck Z k E G tw eta
  (∀ s : ℝ,‖amplitude s‖ ≤ Kglobal*L^(parityGlobalMarkExponent434 mmax+EF+4*CQ+2*Cxi)) ∧
  (|rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq → |xi3| ≤ L^Cfreq →
    |sigma| ≤ L^Cfreq → ∀ s : ℝ,|s| ≤ L^Ftail →
    ‖amplitude s‖ ≤ 2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving+EF+4*CQ+2*Cxi)+
      Kglobal*L^(parityGlobalMarkExponent434 mmax-minorSaving+EF+4*CQ+4*Cxi))

/-- Genuine full-family assembly from actual fixed-rank major/minor and
global theorems. The complete original pattern/rank carriers are summed,
with exact Q^4 xi^-2 count and Q^4 xi^-4 coefficient budgets. All powers,
precision controls and cutoff choices precede L and the operator tuple.
The same eta is returned for the later original-cutoff Mellin identity. -/
theorem parity_eventually_B633_actual_coupled_family_bound434
    (jQ mmax cm : ℕ)
    (CZ Carc Cchi Ck beta gamma majorSaving Cfreq Ftail minorSaving D CQ Cxi : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hD : 0 ≤ D)
    (hMinorSaving : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D)
    (hcm : Ck+D+3 ≤ (cm : ℝ))
    (hCarc : (cm : ℝ) ≤ Carc) (hCchi : (cm : ℝ) ≤ Cchi) (hCchiPos : 0<Cchi)
    (hMinorArc : D+2 ≤ Carc) (hbeta : 0<beta) (hgamma : 0<gamma) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64 ≤ A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A ≤ u ∧ u ≤ A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖ ≤ 1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0 ≤ K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        let Kg:=parityGlobalMarkConstant434 mmax
        let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
        0<Kglobal ∧ 0 ≤ parityGlobalMarkExponent434 mmax ∧
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ  ≤  sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualCoupledCircleFamilyBounds434 cfg eta L jQ mmax CZ Ck S beta gamma
              CQ Cxi majorSaving Karc Cfreq Ftail minorSaving Kglobal := by
  dsimp only
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hKglobal,hEglobal,
      Karc,hKarc,B,S,hSB,hCircle⟩:=
    parity_eventually_B633_actual_coupled_circle_bound434 jQ mmax cm
      CZ Carc Cchi Ck beta gamma majorSaving Cfreq Ftail minorSaving D
      hCZ hCk hD hMinorSaving hcm hCarc hCchi hCchiPos hMinorArc hbeta hgamma
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hKglobal,hEglobal,
    Karc,hKarc,B,S,hSB,?_⟩
  let cfg0:=parityComparisonFixed434 jQ mmax cm ⌈Cfreq+1⌉₊ ⌈Cfreq⌉₊
    ⌈max Cfreq Ftail+1⌉₊ CZ Carc Cchi hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  let Kg:=parityGlobalMarkConstant434 mmax
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  let EG:=parityGlobalMarkExponent434 mmax
  filter_upwards [hCircle,parity_eventually_actual_rank_family_power434 CQ Cxi,
    eventually_ge_atTop (1 : ℝ)] with L hCircleL hFamilyPower hL
  refine ⟨hCircleL.1,hCircleL.2.1,?_⟩
  unfold ParityB633ActualCoupledCircleFamilyBounds434
  intro hFamily Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband slot delta freq k hk hKcap
    chi rho xi1 xi2 xi3 sigma prime lFine uFine a b hFineLow hl hu hub Q hQ hXi tw
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let EF:=(m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let P:=sourceNativeOriginalTb434 20 L
  let V:=sourceNativeOriginalVbig434 20 L
  let Fam:=sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m
  let R:=fun nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m=>
    parityCanonicalRankIndices434 m nu Q h h xi P V
  let C:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q)=>
    sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu h)
      (sourceOriginalProbeCellB434 m P V nu h) r.1.1 r.2.1
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let Hp:=fun r : ParityPrimitiveRankIndex434 Q=>
    Real.exp ((r.1.1 : ℝ)*h)*Real.exp ((r.2.1 : ℝ)*h)
  let first:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q) (s : ℝ)=>
    sourceNatFourierPoly N (parityMellinFourierFirst434 s
      (fun n=>eta ((n : ℝ)/(Z*Hp r))*
        parityActualRankEndpoint434 L hFamily J m hmJ nu h h r (1/2) E (-(rho+xi3)) tw true n))
  let second:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q)=>
    sourceNatFourierPoly N (fun n=>eta ((n : ℝ)/(Z*Hp r))*
      parityActualRankEndpoint434 L hFamily J m hmJ nu h h r (1/2) G (-rho) tw false n)
  let I:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q) (s : ℝ)=>
    ∫ theta : AddCircle (1 : ℝ),
      parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta*
        star (first nu r s theta)*second nu r theta ∂AddCircle.haarAddCircle
  let amplitude:=parityActualCellCoupledCircleFamily434 L hFamily J m hmJ Q h xi rho xi3 Ck Z k E G tw eta
  have h2 : (2*k)≠0:=mul_ne_zero (by norm_num) hk
  have hAmp (s : ℝ) : amplitude s=∑ nu∈Fam,∑ r∈R nu,I nu r s:=by
    simp only [amplitude,parityActualCellCoupledCircleFamily434,h2,ite_false]
    change (∑ nu : ↥Fam,∑ r∈R nu.val,I nu.val r s)=_
    exact Finset.sum_coe_sort Fam (fun nu=>∑ r∈R nu,I nu r s)
  have hTriangle (s : ℝ) : ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,‖I nu r s‖:=by
    rw [hAmp]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun nu hnu=>norm_sum_le _ _))
  have hBudgets:=hFamilyPower m Q (fun _=>h) (fun _=>h)
    (fun nu hnu=>hh) (fun nu hnu=>hh) xi hxi hQ hXi
  have hLp : 0<L:=by linarith
  have hCount : (∑ nu∈Fam,((R nu).card : ℝ)) ≤ L^(EF+4*CQ+2*Cxi):=hBudgets.1
  have hCost : (∑ nu∈Fam,∑ r∈R nu,C nu r) ≤ L^(EF+4*CQ+4*Cxi):=hBudgets.2
  have hGlobalEach (nu) (hnu : nu∈Fam) (r) (hr : r∈R nu) (s : ℝ) :
      ‖I nu r s‖ ≤ Kglobal*L^EG:=by
    obtain ⟨hra,hrb⟩:=Finset.mem_product.mp hr
    obtain ⟨ha,hca⟩:=Finset.mem_product.mp hra
    obtain ⟨hb,hcb⟩:=Finset.mem_product.mp hrb
    have hi:=(hCircleL.2.2.1 eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu h h xi
      hh hh hxi h1 h1 r.1.1 r.2.1 ha hb band hband slot delta freq k hk hKcap
      chi rho xi1 xi2 xi3 sigma s (-xi3) prime lFine uFine a b hFineLow hl hu hub
      Q r.1.2 r.2.2 tw).2.2.2
    change ‖∫ theta : AddCircle (1 : ℝ),
      star (first nu r s theta)*second nu r theta*
        parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
          ∂AddCircle.haarAddCircle‖ ≤ Kglobal*L^EG at hi
    calc
      ‖I nu r s‖ = ‖∫ theta : AddCircle (1 : ℝ),
          star (first nu r s theta)*second nu r theta*
            parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
              ∂AddCircle.haarAddCircle‖ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun theta=>by
          change parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta*
            star (first nu r s theta)*second nu r theta =
            star (first nu r s theta)*second nu r theta*
            parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
          ring)
      _ ≤ Kglobal*L^EG := hi
  constructor
  · intro s
    calc
      ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,Kglobal*L^EG:=
        (hTriangle s).trans (Finset.sum_le_sum (fun nu hnu=>
          Finset.sum_le_sum (fun r hr=>hGlobalEach nu hnu r hr s)))
      _=(∑ nu∈Fam,((R nu).card : ℝ))*(Kglobal*L^EG):=by
        simp only [Finset.sum_const,nsmul_eq_mul,←Finset.sum_mul]
      _ ≤ L^(EF+4*CQ+2*Cxi)*(Kglobal*L^EG):=
        mul_le_mul_of_nonneg_right hCount (mul_nonneg hKglobal.le (Real.rpow_nonneg hLp.le _))
      _=Kglobal*L^(EG+EF+4*CQ+2*Cxi):=by
        calc
          _=Kglobal*(L^(EF+4*CQ+2*Cxi)*L^EG):=by ring
          _=_:=by rw [←Real.rpow_add hLp];congr 1;ring
  · intro hrho hxi1 hxi2 hxi3 hsigma s hsTail
    let BM:=2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving)
    let BN:=Kglobal*L^(EG-minorSaving)
    have hBM : 0 ≤ BM:=by dsimp [BM];positivity
    have hBN : 0 ≤ BN:=mul_nonneg hKglobal.le (Real.rpow_nonneg hLp.le _)
    have hLowEach (nu) (hnu : nu∈Fam) (r) (hr : r∈R nu) :
        ‖I nu r s‖ ≤ BM+C nu r*BN:=by
      obtain ⟨hra,hrb⟩:=Finset.mem_product.mp hr
      obtain ⟨ha,hca⟩:=Finset.mem_product.mp hra
      obtain ⟨hb,hcb⟩:=Finset.mem_product.mp hrb
      have hi:=hCircleL.2.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu h h xi
        hh hh hxi h1 h1 r.1.1 r.2.1 ha hb band hband slot delta freq k hk hKcap
        chi rho xi1 xi2 xi3 sigma s hrho hxi1 hxi2 hxi3 hsigma hsTail
        prime lFine uFine a b hFineLow hl hu hub Q r.1.2 r.2.2 hca hcb tw
      change ‖I nu r s‖ ≤ BM+(C nu r*Kglobal)*L^(EG-minorSaving) at hi
      simpa only [BN,mul_assoc] using hi
    calc
      ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,(BM+C nu r*BN):=
        (hTriangle s).trans (Finset.sum_le_sum (fun nu hnu=>
          Finset.sum_le_sum (fun r hr=>hLowEach nu hnu r hr)))
      _=(∑ nu∈Fam,((R nu).card : ℝ))*BM+(∑ nu∈Fam,∑ r∈R nu,C nu r)*BN:=by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.sum_mul]
      _ ≤ L^(EF+4*CQ+2*Cxi)*BM+L^(EF+4*CQ+4*Cxi)*BN:=
        add_le_add (mul_le_mul_of_nonneg_right hCount hBM) (mul_le_mul_of_nonneg_right hCost hBN)
      _=2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving+EF+4*CQ+2*Cxi)+
          Kglobal*L^(EG-minorSaving+EF+4*CQ+4*Cxi):=by
        dsimp only [BM,BN]
        have hM : L^(EF+4*CQ+2*Cxi)*L^(2*(cfg.cm : ℝ)-majorSaving)=
            L^(2*(cfg.cm : ℝ)-majorSaving+EF+4*CQ+2*Cxi):=by
          rw [←Real.rpow_add hLp];congr 1;ring
        have hN : L^(EF+4*CQ+4*Cxi)*L^(EG-minorSaving)=
            L^(EG-minorSaving+EF+4*CQ+4*Cxi):=by
          rw [←Real.rpow_add hLp];congr 1;ring
        calc
          _=(2*Karc)*(L^(EF+4*CQ+2*Cxi)*L^(2*(cfg.cm : ℝ)-majorSaving))+
              Kglobal*(L^(EF+4*CQ+4*Cxi)*L^(EG-minorSaving)):=by ring
          _=_:=by rw [hM,hN]
end Green64Analytic.Parity

end

end

/-! ## MainSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Genuine saving for the UNCHANGED existing actual r20 rank-Main
family on the original positive B654 carrier, with the ORIGINAL physical
cutoff psi. The full actual B633 core, modulus 2*natAbs(k), signed shift,
parity, operator tuple and cutoff derivative budget are displayed. The
same external Z appears once. This proposition defines only the claimed
bound, not a replacement Main functional. -/
def ParityB633ActualRankMainSaving434
    (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Cfreq CQ Cxi Cpsi : ℝ) (Kpsi : ℕ → ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (h xi : ℝ), 0 < h → h ≤ 1 → 0 < xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
  ∀ (Q : ℕ), (Q : ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi → ∀ (tw : Bool),
    |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq → |xi3| ≤ L^Cfreq →
    |sigma| ≤ L^Cfreq →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  ‖parityActualWeightedRankMainFamily434 L hFamily J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw psi‖ ≤
      L^(-targetSaving) ∧
  ‖(Z : ℂ)*parityActualWeightedRankMainFamily434 L hFamily J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw psi‖ ≤
      Z*L^(-targetSaving)

/-- Unconditional actual r20 B633 rank-Main saving at the ORIGINAL cutoff.
The low-frequency target is E+ceil(3*Cpsi)+3. Both cell losses and the
complete fixed-m family cost are paid before choosing D, cm, Carc and the
actual B629 operator precision. The genuine global exponent depends only
on mmax, so these choices are not circular. A common constructed eta is
used for both endpoint estimates and the exact original-Main Mellin
identity, then disappears from the conclusion. No assumed Main, kernel,
endpoint-energy, data-record, auxiliary-witness or amplitude bound is an
input. This is a rank-Main theorem, not a claim of E4.1 or exact Green64. -/
theorem parity_eventually_B633_actual_rank_main_saving434
    (jQ mmax : ℕ)
    (targetSaving Cpsi Ftail Cfreq CZ Ck CQ Cxi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j,0 ≤ Kpsi j) (hCF : Cpsi < Ftail)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityB633ActualRankMainSaving434 L jQ mmax CZ Ck S beta gamma
          targetSaving Cfreq CQ Cxi Cpsi Kpsi := by
  let lowSaving := b662CutoffSavingExponent434 targetSaving Cpsi
  let EFmax := (mmax : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let Eglobal := parityGlobalMarkExponent434 mmax
  let minorSaving := max 0 (Eglobal+EFmax+4*CQ+4*Cxi+lowSaving+2)
  let D := 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ)
  let cm := Nat.ceil (Ck+D+3)
  let Carc := (cm : ℝ)+D+2
  let Cchi := (cm : ℝ)+1
  let majorSaving := 2*(cm : ℝ)+EFmax+4*CQ+2*Cxi+lowSaving+2
  let Cglobal := Eglobal+EFmax+4*CQ+2*Cxi+1
  have hMinor0 : 0 ≤ minorSaving := le_max_left _ _
  have hMoment0 : 0 ≤ (parityCellKernelMomentExponent434 mmax : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have hCm0 : 0 ≤ (cm : ℝ) := Nat.cast_nonneg _
  have hcm : Ck+D+3 ≤ (cm : ℝ) := Nat.le_ceil _
  have hCarc : (cm : ℝ) ≤ Carc := by dsimp only [Carc]; linarith
  have hCchi : (cm : ℝ) ≤ Cchi := by dsimp only [Cchi]; linarith
  have hCchiPos : 0 < Cchi := by dsimp only [Cchi]; linarith
  have hMinorArc : D+2 ≤ Carc := by dsimp only [Carc]; linarith
  have hMinorPrec : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D := le_rfl
  have hFamily := parity_eventually_B633_actual_coupled_family_bound434
    jQ mmax cm CZ Carc Cchi Ck beta gamma majorSaving Cfreq Ftail minorSaving D CQ Cxi
    hCZ hCk hD hMinorPrec hcm hCarc hCchi hCchiPos hMinorArc hbeta hgamma
  dsimp only at hFamily
  obtain ⟨A,hA,eta,hEtaSmooth,hEtaSupport,hEtaOne,hEtaNorm,Keta,hKeta,hEtaBudget,
    hKglobal,hEglobal,Karc,hKarc,B,S,hSB,hFull⟩ := hFamily
  let Kg := parityGlobalMarkConstant434 mmax
  let Kglobal := (A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  have hKglobal' : 0 < Kglobal := hKglobal
  have hMajorAllocation : 2*(cm : ℝ)+EFmax+4*CQ+2*Cxi+lowSaving+2 ≤ majorSaving := le_rfl
  have hMinorAllocation : Eglobal+EFmax+4*CQ+4*Cxi+lowSaving+2 ≤ minorSaving := le_max_right _ _
  have hMellin := parity_eventually_actual_main_mellin_transfer434 targetSaving Cpsi Ftail Cglobal
    CZ Ck Kpsi hCpsi hKpsi hCF hCZ hCk
  refine ⟨B,S,hSB,?_⟩
  filter_upwards [hFull,hMellin,eventually_ge_atTop (max 2 (2*Karc+Kglobal))]
    with L hFullL hTransfer hLarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLarge
  have hKL : 2*Karc+Kglobal ≤ L := (le_max_right _ _).trans hLarge
  refine ⟨hFullL.1,hFullL.2.1,?_⟩
  unfold ParityB633ActualRankMainSaving434
  intro hS Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband slot delta freq k hk hK
    chi rho xi1 xi2 xi3 sigma prime lFine uFine a b hFine hl hu hub Q hQ hX tw
    hrho hxi1 hxi2 hxi3 hsigma psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let EF := (m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  have hEF : EF ≤ EFmax := parity_rank_family_exponent_mono434 m mmax hmm
  have hAbsorb := parity_coupled_family_power_absorb434 L lowSaving Eglobal EF EFmax CQ Cxi
    (cm : ℝ) majorSaving minorSaving Karc Kglobal hL2 hEF hKarc.le hKglobal'.le hKL
    hMajorAllocation hMinorAllocation
  have hPair := hFullL.2.2 hS Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband
    slot delta freq k hk hK chi rho xi1 xi2 xi3 sigma prime lFine uFine a b
    hFine hl hu hub Q hQ hX tw
  dsimp only at hPair
  have hLow (s : ℝ) (hs : |s| ≤ L^Ftail) :
      ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw eta s‖ ≤
        L^(-b662CutoffSavingExponent434 targetSaving Cpsi) := by
    exact (hPair.2 hrho hxi1 hxi2 hxi3 hsigma s hs).trans hAbsorb.1
  have hAll (s : ℝ) :
      ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw eta s‖ ≤
        L^Cglobal := by
    exact (hPair.1 s).trans hAbsorb.2
  exact hTransfer hS J m hmJ Q h xi rho xi3 Z k h1 hZlo hK Ecore Gcore tw psi eta
    hSmooth hSupport hReg hEtaOne hLow hAll
end Green64Analytic.Parity

end

end

/-! ## ActualRawHarmonicSaving -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Genuine literal physical RAW saving obtained by subtracting the actual
comparison Main from the small original harmonic residual. The comparison
bound, restoration and collision errors are all derived, not assumptions.
The original cutoff is literally t*psi(t); the certified normalized log
adapter preserves Cpsi. The independent full physical RAW construction,
all shared/free products, original P-dependent ordinary-part/core gates,
parity, signed shift2*k and
both endpoint readouts remain unchanged. This is literal uncapped RAW
with endpoint weight1, without an added physical Ppart cap.
Exactly one exterior Z remains.

The harmonic construction chooses m/cell parameters/J before the fine
precision. The actual comparison theorem is then requested at target+2
with those fixed family costs, before B/S,L and the operator tuple.
The final statement hides the auxiliary comparison parameters altogether,
because their exact RAW reindex is independently proved. This does not
assert a complete historical B521-channel correspondence or TypeII. -/
theorem parity_eventually_B633_actual_literal_raw_harmonic_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        ‖(Z : ℂ)*parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
          1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (fun _ _ => 1)‖ ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hH⟩ :=
    parity_eventually_actual_harmonic_physical_saving434
      (target+2) Cfreq Ck Cpsi Kpsi (by linarith) hCk hCpsi hKpsi
  obtain ⟨B,S,hSB,hMain⟩ :=
    parity_eventually_B633_actual_rank_main_saving434 jQ m
      (target+2) Cpsi (Cpsi+1) Cfreq CZ Ck (Cq : ℝ) (Cxi : ℝ) beta gamma KH
      hCpsi hKH (by linarith) hCZ hCk hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hRest := parity_eventually_actual_harmonic_outer_Z_rank_error434
    J S beta gamma CZ Ck (Cq : ℝ) (Cxi : ℝ) Cpsi (KH 0) (target+2)
    hSpos hbeta hgamma hCZ (hKH 0)
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hH S beta gamma CZ hSpos hbeta hgamma hCZ,hMain,hRest,
    eventually_ge_atTop (3 : ℝ)] with L hHL hML hRL hL3
  dsimp only at hHL
  obtain ⟨hL1,hQp,hQc,hh,hh2,hxi,hxic,hFamily0,hHsave⟩ := hHL
  refine ⟨hFamily0,hML.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH) : ℕ) : ℝ)
  let xi : ℝ := L^(-(Cxi : ℝ))
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let H := parityHarmonicPhysical434 L hFamily J m hmJ Q h xi (-xi3) Z Ck k
    (parityDyadicDepth434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0 psiH
  let R := parityActualHarmonicRawPositiveFibreSum434 L hFamily J m hmJ Q h xi (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0 psiH
  let Main := parityActualWeightedRankMainFamily434 L hFamily J m hmJ Q h xi
    rho xi3 Ck Z k Ecore Gcore tw psiH
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hh1 : h ≤ 1 := by change h+h ≤ 1 at hh2;change 0 < h at hh;nlinarith
  have hQbound : (Q : ℝ) ≤ L^(Cq : ℝ) := by
    simpa only [Real.rpow_natCast] using hQc
  have hXibound : xi⁻¹ ≤ L^(Cxi : ℝ) := by
    simpa only [Real.rpow_natCast] using hxic
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hSmoothH : ContDiff ℝ ∞ psiH := Complex.ofRealCLM.contDiff.mul hSmooth
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hPsiH : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0*L^Cpsi := by
    intro t
    by_cases ht : psiH t = 0
    · rw [ht,norm_zero]
      exact mul_nonneg (hKH 0) (Real.rpow_nonneg hLp.le _)
    · have htp : 0 < t := by linarith [(hSupportH t ht).1]
      simpa only [iteratedDeriv_zero,Nat.cast_zero,zero_add,mul_one,Real.exp_log htp]
        using hRegH 0 (Real.log t)
  have hHsmall : ‖(Z : ℂ)*H‖ ≤ Z*L^(-(target+2)) :=
    hHsave hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound
      prime lFine uFine hFineLow 20 (sourceOriginalLiteralDepth 20 L) (by norm_num)
      band slot delta freq (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma tw Z hZlo hZhi
  have hMsmall : ‖(Z : ℂ)*Main‖ ≤ Z*L^(-(target+2)) :=
    (hML.2.2 hFamily Z hZlo hZhi J m hmJ (le_refl m) h xi hh hh1 hxi
      band hband slot delta freq k hk hkBound chi rho xi1 xi2 xi3 sigma
      prime lFine uFine a b hFineLow hl hu hub Q hQbound hXibound tw
      hrho hxi1 hxi2 hxi3 hsigma psiH hSmoothH hSupportH hRegH).2
  have hError : ‖(Z : ℂ)*(H-R-Main)‖ ≤ Z*L^(-(target+2)) :=
    hRL.2.2 prime lFine uFine hFineLow 20 (sourceOriginalLiteralDepth 20 L)
      (by norm_num) band slot delta freq (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi
      hkReal hQbound hXibound tw psiH hSupportH hPsiH
  have hRawSmall : ‖(Z : ℂ)*R‖ ≤ Z*L^(-target) := by
    have hPower : L^2*L^(-(target+2)) = L^(-target) := by
      calc
        _ = L^((2 : ℕ) : ℝ)*L^(-(target+2)) := by rw [Real.rpow_natCast]
        _ = L^(((2 : ℕ) : ℝ)+(-(target+2))) := (Real.rpow_add hLp _ _).symm
        _ = L^(-target) := by congr 1 <;> norm_num <;> ring
    calc
      _ = ‖(Z : ℂ)*H-(Z : ℂ)*Main-(Z : ℂ)*(H-R-Main)‖ := by congr 1;ring
      _ ≤ ‖(Z : ℂ)*H-(Z : ℂ)*Main‖+‖(Z : ℂ)*(H-R-Main)‖ := norm_sub_le _ _
      _ ≤ (‖(Z : ℂ)*H‖+‖(Z : ℂ)*Main‖)+‖(Z : ℂ)*(H-R-Main)‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ ≤ (Z*L^(-(target+2))+Z*L^(-(target+2)))+Z*L^(-(target+2)) :=
        add_le_add (add_le_add hHsmall hMsmall) hError
      _ = Z*(3*L^(-(target+2))) := by ring
      _ ≤ Z*(L^2*L^(-(target+2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by nlinarith : (3 : ℝ) ≤ L^2)
            (Real.rpow_nonneg hLp.le _)) hZ.le
      _ = Z*L^(-target) := by rw [hPower]
  have hRawEq : R =
      parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
        positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
        psiH (fun _ _ => 1) := by
    simpa only [R,parityActualEndpointWeightedRawPositiveFibreSum434,
      parityActualHarmonicRawPositiveFibreSum434,one_mul] using
      parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily J m hmJ Q h xi (-xi3) Z k
        positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
        psiH (fun _ _ => 1)
  rw [hRawEq] at hRawSmall
  exact hRawSmall
end Green64Analytic.Parity

end

end

/-! ## PhysicalComparisonSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 30000

/-- A genuine original-cutoff physical comparison bound, obtained by subtracting
ONLY the literal RAW branch of the pre-existing harmonic functional. The
original full harmonic and RAW are independently defined; in particular the
conclusion is not the definition of a new desired residual. Exactly one outer
Z, the original B633 E/G input, all marks, cutoff, and both character and
fine-alpha gates are retained. -/
def ParityB633ActualPhysicalComparisonSaving434
    (L : ℝ) (J jQ mmax : ℕ)
    (CZ Ck S beta gamma A Cfreq CQ Cxi Cpsi : ℝ)
    (Kpsi : ℕ → ℝ) : Prop :=
  ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (h xi : ℝ), 0 < h → h ≤ 1 → 0 < xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
  ∀ (Q : ℕ), (Q : ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi → ∀ (tw : Bool),
    |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq → |xi3| ≤ L^Cfreq →
    |sigma| ≤ L^Cfreq →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  ‖(Z : ℂ)*(parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
      (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
    parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi)‖ ≤ Z*L^(-A)

/-- The original log-derivative budget already contains the uniform
value bound needed for literal Restored/Stripped/collision estimates.
Outside positive input support the cutoff vanishes; on positive input
use j=0 at log(t). This adds NO new smoothness or size assumption. -/
theorem parity_original_log_budget_sup434
    (L C : ℝ) (K : ℕ → ℝ) (psi : ℝ → ℂ)
    (hL : 0 < L) (hK : 0 ≤ K 0)
    (hSupport : ∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hBudget : sourceLogDerivativeBudget C K L (fun u => psi (Real.exp u))) :
    ∀ t : ℝ, ‖psi t‖ ≤ K 0 * L^C := by
  intro t
  by_cases ht : 0 < t
  · have h0 := hBudget 0 (Real.log t)
    simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_add, mul_one,
      Real.exp_log ht] using h0
  · have hz : psi t = 0 := by
      by_contra hne
      have hh := (hSupport t hne).1
      linarith
    simpa only [hz, norm_zero] using
      (mul_nonneg hK (Real.rpow_nonneg hL.le C))

/-- The genuine B633 comparison contribution H−RAW has arbitrary inverse-log
saving, with exactly one exterior Z. The proof combines independently
constructed Main saving and the literal H−RAW−Main restoration/collision
estimate at local precision A+1. Original support and the derivative
budget imply the only required psi supremum bound. All fixed precisions,
cutoff exponents and mmax precede L and the operator data. -/
theorem parity_eventually_B633_actual_physical_comparison_saving434
    (J jQ mmax : ℕ)
    (A Cpsi Ftail Cfreq CZ Ck CQ Cxi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) (hCF : Cpsi < Ftail)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityB633ActualPhysicalComparisonSaving434 L J jQ mmax CZ Ck S beta gamma
          A Cfreq CQ Cxi Cpsi Kpsi := by
  obtain ⟨B,S,hSB,hMain⟩ := parity_eventually_B633_actual_rank_main_saving434
    jQ mmax (A+1) Cpsi Ftail Cfreq CZ Ck CQ Cxi beta gamma Kpsi
    hCpsi hKpsi hCF hCZ hCk hbeta hgamma
  refine ⟨B,S,hSB,?_⟩
  filter_upwards [hMain,
    parity_eventually_actual_harmonic_outer_Z_rank_error434 J S beta gamma CZ Ck CQ Cxi
      Cpsi (Kpsi 0) (A+1) (by linarith [hSB]) hbeta hgamma hCZ (hKpsi 0),
    eventually_ge_atTop (2 : ℝ)] with L hMainL hRankL hL2
  refine ⟨hMainL.1,hMainL.2.1,?_⟩
  unfold ParityB633ActualPhysicalComparisonSaving434
  intro hS Z hZlo hZhi m hmJ hmm h xi hh hh1 hxi band hband slot delta freq
    k hk hK chi rho xi1 xi2 xi3 sigma prime lFine uFine a b hFine hl hu hub
    Q hQ hX tw hrho hxi1 hxi2 hxi3 hsigma psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let H := parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
    (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi
  let R := parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
    1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi
  let M := parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k E G tw psi
  have hLp : 0 < L := by linarith
  have hZp : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hSup : ∀ t, ‖psi t‖ ≤ (Kpsi 0)*L^Cpsi :=
    parity_original_log_budget_sup434 L Cpsi Kpsi psi hLp (hKpsi 0) hSupport hReg
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hK
  have hError : ‖(Z : ℂ)*(H-R-M)‖ ≤ Z*L^(-(A+1)) := by
    exact hRankL.2.2 prime lFine uFine hFine 20 (sourceOriginalLiteralDepth 20 L)
      (by norm_num) band slot delta freq (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hkReal hQ hX
      tw psi hSupport hSup
  have hMainBound := hMainL.2.2 hS Z hZlo hZhi J m hmJ hmm h xi hh hh1 hxi
    band hband slot delta freq k hk hK chi rho xi1 xi2 xi3 sigma
    prime lFine uFine a b hFine hl hu hub Q hQ hX tw
    hrho hxi1 hxi2 hxi3 hsigma psi hSmooth hSupport hReg
  have hMain : ‖(Z : ℂ)*M‖ ≤ Z*L^(-(A+1)) := hMainBound.2
  have hp : L*L^(-(A+1)) = L^(-A) := by
    calc
      _ = L^(1+(-(A+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(A+1))).symm
      _ = L^(-A) := by congr 1; ring
  change ‖(Z : ℂ)*(H-R)‖ ≤ Z*L^(-A)
  calc
    _ = ‖(Z : ℂ)*(H-R-M)+(Z : ℂ)*M‖ := by congr 1; ring
    _ ≤ ‖(Z : ℂ)*(H-R-M)‖+‖(Z : ℂ)*M‖ := norm_add_le _ _
    _ ≤ Z*L^(-(A+1))+Z*L^(-(A+1)) := add_le_add hError hMain
    _ = Z*(2*L^(-(A+1))) := by ring
    _ ≤ Z*(L*L^(-(A+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZp.le
    _ = Z*L^(-A) := by rw [hp]
end Green64Analytic.Parity

end

end

