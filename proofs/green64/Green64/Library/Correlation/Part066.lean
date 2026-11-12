module

public import Green64.Library.Correlation.Part065
public import Green64.Library.Weights.Part086
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Correlation / Part066

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralFockSourceCoreEqualsTPrimeCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- EXACT original divisor geometry, for positive ordinary endpoint n:
T's p∣(n/m) iff Fock sourceCore's p∣n and m*p∣n, retaining all prime
powers. No squarefree proxy or truncation. -/
theorem source_native_B523_actual_quotient_divisor_support434
    (n m p : ℕ) (hn : 0 < n) (hm : m ∈ n.divisors) :
    p ∈ (n/m).divisors ↔ p ∈ n.divisors ∧ m*p ∣ n := by
  have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hn
  have hmp : m ≤ n := Nat.le_of_dvd hn hmdvd
  have hquotpos : 0 < n/m := Nat.div_pos hmp hmpos
  constructor
  · intro hp
    have hpdvd : p ∣ n/m := (Nat.mem_divisors.mp hp).1
    have hmul : m*p ∣ n := (Nat.dvd_div_iff_mul_dvd hmdvd).mp hpdvd
    exact ⟨Nat.mem_divisors.mpr
      ⟨(dvd_mul_left p m).trans hmul, Nat.ne_of_gt hn⟩,hmul⟩
  · rintro ⟨hp,hmul⟩
    have hpdvd : p ∣ n/m := (Nat.dvd_div_iff_mul_dvd hmdvd).mpr hmul
    exact Nat.mem_divisors.mpr ⟨hpdvd, Nat.ne_of_gt hquotpos⟩

/-- Original ordinary-P part is positive even for zero n, since it is
a product of TRUE positive prime powers; no zero divisor corner is hidden. -/
theorem source_native_B523_original_ordinary_part_pos434
    (P : Finset ℕ) (n : ℕ) :
    0 < sourceOriginalOrdinaryPart P n := by
  unfold sourceOriginalOrdinaryPart
  apply Finset.prod_pos
  intro p hp
  have hpr : p.Prime :=
    (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1
  exact pow_pos hpr.pos _

/-- The FULL original native T Q/P `primeSlotCoreValue` equals the actual
physical/Fock `sourceCore` at its unmodified outside-P endpoint. The two
kernels share the EXACT same ordinary prime powers, full divisor m,p
geometry, prime Q band, original alpha/character, residual including every
QSkip factorial/Fourier phase, and both Mellin twists. No model endpoint,
source support restriction removal, or numerical approximation. -/
theorem source_native_B523_literal_fock_sourceCore_eq_T_primeSlotCore434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (z : ℕ) :
    sourceCore (sourceOutsidePart (Finset.univ.biUnion P) z)
        ((Finset.Icc F.lo F.hi).filter Nat.Prime)
        F.alpha F.residual F.q F.character F.sigma₀ F.sigma₁ =
    primeSlotCoreValue P F z := by
  rw [source_native_B521_fock_outside_eq_T_original_ordinary434]
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  have hns : 0 < ns := source_native_B523_original_ordinary_part_pos434 _ _
  unfold sourceCore primeSlotCoreValue
  apply Finset.sum_congr rfl
  intro m hm
  have hmdvd : m ∣ ns := (Nat.mem_divisors.mp hm).1
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hns
  have hSubset : (ns/m).divisors ⊆ ns.divisors := by
    intro p hp
    exact (source_native_B523_actual_quotient_divisor_support434 ns m p hns hm).mp hp |>.1
  let f : ℕ → ℂ := fun p =>
    if p ∈ (Finset.Icc F.lo F.hi).filter Nat.Prime ∧ p.Prime ∧ m*p ∣ ns then
      F.alpha m * F.character m * sourceUnitTwist m F.sigma₀ *
        sourceUnitTwist p F.sigma₁ * F.residual (ns/(m*p)) else 0
  have hZero (p : ℕ) (hp : p ∈ ns.divisors)
      (hnp : p ∉ (ns/m).divisors) : f p = 0 := by
    have hno : ¬ (p ∈ (Finset.Icc F.lo F.hi).filter Nat.Prime ∧
        p.Prime ∧ m*p ∣ ns) := by
      intro hh
      exact hnp ((source_native_B523_actual_quotient_divisor_support434
        ns m p hns hm).mpr ⟨hp,hh.2.2⟩)
    dsimp only [f]
    rw [if_neg hno]
  have hSum : (∑ p ∈ ns.divisors, f p) =
      (∑ p ∈ (ns/m).divisors, f p) :=
    (Finset.sum_subset hSubset hZero).symm
  change (∑ p ∈ ns.divisors, f p) = _
  rw [hSum]
  apply Finset.sum_congr rfl
  intro p hp
  have hmul : m*p ∣ ns :=
    (source_native_B523_actual_quotient_divisor_support434
      ns m p hns hm).mp hp |>.2
  by_cases hPB : p.Prime ∧ p ∈ Finset.Icc F.lo F.hi
  · have hSrc : p ∈ (Finset.Icc F.lo F.hi).filter Nat.Prime ∧
        p.Prime ∧ m*p ∣ ns :=
      ⟨Finset.mem_filter.mpr ⟨hPB.2,hPB.1⟩,hPB.1,hmul⟩
    simp only [f,if_pos hSrc,if_pos hPB]
    rw [source_native_B522_fock_sourceUnitTwist_eq_T_imaginaryPower434
          m hmpos F.sigma₀,
        source_native_B522_fock_sourceUnitTwist_eq_T_imaginaryPower434
          p hPB.1.pos F.sigma₁]
    rw [Nat.div_div_eq_div_mul]
  · have hSrc : ¬ (p ∈ (Finset.Icc F.lo F.hi).filter Nat.Prime ∧
        p.Prime ∧ m*p ∣ ns) := by
      intro hh
      exact hPB ⟨hh.2.1,(Finset.mem_filter.mp hh.1).1⟩
    simp only [f,if_neg hSrc,if_neg hPB]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualSortedQSkipFockToNativeCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- ACTUAL original sorted-Q/QSkip sourceCore with genuine original
finite K-supported alpha, full factorial (r!)^-(d+1), every labelled
skipped-Q Fourier phase and the true closed designated Q band equals
the literal T PrimeSlotCoreValue at the SAME physical ordinary endpoint.
No independent residual, branch or analogue is substituted. -/
theorem source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (z : ℕ) :
    let F := sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁
    sourceCore (sourceOutsidePart (Finset.univ.biUnion P) z)
      (sourceOriginalQActualBands r d L b)
      (restrictSequence K alpha)
      (sourceEndpointFibre
        (Finset.univ : Finset (OrderedQSkip
          (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
          (sourceActualSortedQ r d L b slot) δ))
        orderedSkipProduct
        (fun a => sourceActualSortedFactorial r d *
          orderedSkipPhase (sourceActualSortedFrequencyScales r d L b slot) ξ a))
      q χ σ₀ σ₁ = primeSlotCoreValue P F z := by
  dsimp only
  let F := sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁
  change sourceCore (sourceOutsidePart (Finset.univ.biUnion P) z)
      ((Finset.Icc F.lo F.hi).filter Nat.Prime)
      F.alpha F.residual F.q F.character F.sigma₀ F.sigma₁ =
      primeSlotCoreValue P F z
  exact source_native_B523_literal_fock_sourceCore_eq_T_primeSlotCore434 P F z
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualFockProjectedEqualsT -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Literal original physical/Fock ordinary endpoint `sourceCore` with
actual finite K-restricted alpha and all source QSkip factorial/ξ phases.
It uses the original outside-P factorization, not a native surrogate. -/
noncomputable def sourceNativeB525ActualFockEndpointCore434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (z : ℕ) : ℂ :=
  sourceCore (sourceOutsidePart (Finset.univ.biUnion P) z)
    (sourceOriginalQActualBands r d L b)
    (restrictSequence K alpha)
    (sourceEndpointFibre
      (Finset.univ : Finset (OrderedQSkip
        (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
        (sourceActualSortedQ r d L b slot) δ))
      orderedSkipProduct
      (fun a => sourceActualSortedFactorial r d *
        orderedSkipPhase (sourceActualSortedFrequencyScales r d L b slot) ξ a))
    q χ σ₀ σ₁

/-- The complete ORIGINAL finite physical four-sign projected correlation
constructed from Fock sourceCore at BOTH physical endpoints z,z+2k,
using original ordinary-part extraction and full sorted-QSkip residuals.
All outer Mellin, source BIG marked weights and actual physical parity
factors remain untouched. The source and target δ,ξ,K are independent. -/
noncomputable def sourceNativeB525PhysicalFockProjected434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
    if 0 < (z:ℤ)+2*k then
      let zR := ((z:ℤ)+2*k).toNat
      psi ((z:ℝ)/Z)/(z:ℂ) *
      imaginaryPower z a1 * imaginaryPower zR a2 *
      star (sourceNativeB525ActualFockEndpointCore434 P
        r d L b slot δF ξF KF alphaF q χ σF0 σF1 z) *
      sourceNativeB525ActualFockEndpointCore434 P
        r d L b slot δG ξG KG alphaG q χ σG0 σG1 zR *
      (sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P zR : ℝ) *
      ((((1-groupSign P true z)/2)*
        ((1-groupSign P true zR)/2)) : ℝ)
    else 0

/-- EXACT original physical/Fock two-end projected scalar correlation
at true integer shift 2k equals the T `sourceCorrelationProjected` of
the original sorted-Q/QSkip `sourceNativePrimeCore` constructors. Neither
original K mask is overwritten. Two independent δ, ξ, source/target
QSkip residuals, divisor multiplicities, all Fourier/Mellin phases,
marked weights, and four parity signs are kept literally. This is the
missing SCALAR ordinary-core Fock↔T bridge; it does NOT identify the
full memory/OLD/terminal-vacuum functional or the D61 Fourier integrals. -/
theorem source_native_B525_original_Fock_projected_eq_T_native434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ) :
    sourceNativeB525PhysicalFockProjected434 c g P
      r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ
      σF0 σF1 σG0 σG1 Z a1 a2 bPsi k psi =
    sourceCorrelationProjected c g P
      (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1)
      Z a1 a2 bPsi (2*k) psi := by
  unfold sourceNativeB525PhysicalFockProjected434 sourceCorrelationProjected
  apply Finset.sum_congr rfl
  intro z hz
  unfold sourceCorrelationBaseKernel
  by_cases hp : 0 < (z:ℤ)+2*k
  · simp only [if_pos hp]
    unfold sourceNativeB525ActualFockEndpointCore434
    rw [source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
          P r d L b slot δF ξF KF alphaF q χ σF0 σF1 z,
        source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
          P r d L b slot δG ξG KG alphaG q χ σG0 σG1
          (((z:ℤ)+2*k).toNat)]
  · simp only [if_neg hp]
    simp
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## TrueNativePGatedOriginalCore -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve
/-- LITERAL original P-prime-part definition from SourceShiftTwoOriginalWeights;
no surrogate indicator or lost prime powers. -/
noncomputable def sourceOriginalPPrimePart (Pall : Finset ℕ) (u : ℕ) : ℕ :=
  ∏ p ∈ u.primeFactors ∩ Pall, p ^ u.factorization p
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Literal SOURCE T original physical GATED kernel (not the ungated B490
Schwartz interval proxy). The two independent original P-part-support
conditions at z and z+2k, both Mellin phases, original ψ(z), source marked
weights and the genuine Q/P `PrimeSlotCore` are kept in every summand.
Copied from SourceNativeFourChannelContract.lean, no analytic changes. -/
noncomputable def sourceNativeGatedGramKernel
    {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (R : Finset ℕ) (F G : PrimeSlotCore)
    (k : ℤ) (a₁ a₂ : ℝ) (psi : ℕ → ℂ) (z : ℕ) : ℂ :=
  let zp := ((z:ℤ)+2*k).toNat
  if 0 < (z:ℤ)+2*k ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) zp ∈ R then
    psi z * imaginaryPower z a₁ * imaginaryPower zp a₂ *
      star (primeSlotCoreValue P F z) * primeSlotCoreValue P G zp *
      ((sourceMarkedWeight (1/2:ℝ) 1 P z * sourceMarkedWeight (1/2:ℝ) 1 P zp:ℝ):ℂ)
  else 0

/-- Literal T original TWO independent endpoint-twist GATED channel,
with the actual provided physical position support S (original S.image e),
not a replacement dyadic interval. No C191 Fourier approximation. -/
noncomputable def sourceNativeGatedChannel
    (S : Finset ℕ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (R : Finset ℕ)
    (F G : PrimeSlotCore) (k : ℤ) (a₁ a₂ : ℝ) (psi : ℕ → ℂ)
    (tw₁ tw₂ : Bool) : ℂ :=
  ∑ z ∈ S, sourceNativeGatedGramKernel P R F G k a₁ a₂ psi z *
    ((groupSign P tw₁ z * groupSign P tw₂ (((z:ℤ)+2*k).toNat):ℝ):ℂ)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## TrueNativeGatedFourSignProjected -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Genuinely P-PART-GATED original physical Q/P correlation, with
its original arbitrary finite tagged z-support S, literal marked weights,
full two-sided sourceNativePrimeCore and (+,-,-,+)/4 projector BEFORE norm. -/
noncomputable def sourceNativeB522GatedPhysicalProjected434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ) (F G : PrimeSlotCore)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) : ℂ :=
  ∑ z ∈ S, sourceNativeGatedGramKernel P R F G k a1 a2 psi z *
    (((1-groupSign P true z)/2)*
     ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2) : ℝ)

/-- Exact original T GATED FOUR-channel identity. The same true
sourceNativeGatedGramKernel, P-part pair gate, original finite tagged
position support and independent two endpoint signs are used in every
channel. No C191 Fourier-parameter substitution, smoothing or loss. -/
theorem source_native_B522_literal_gated_four_sign_projector434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ) (F G : PrimeSlotCore)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) :
    sourceNativeB522GatedPhysicalProjected434 S P R F G k a1 a2 psi =
    ∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw *
        sourceNativeGatedChannel S P R F G k a1 a2 psi tw.1 tw.2 := by
  let hKernel : ℕ → ℂ := sourceNativeGatedGramKernel P R F G k a1 a2 psi
  let zp : ℕ → ℕ := fun z => ((z:ℤ)+2*k).toNat
  have hPoint (z : ℕ) :
      hKernel z * (((1-groupSign P true z)/2)*
        ((1-groupSign P true (zp z))/2):ℝ) =
      ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
        (hKernel z * ((groupSign P tw.1 z *
           groupSign P tw.2 (zp z)):ℝ)) := by
    calc
      _ = ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
        (hKernel z * (((if tw.1 then groupSign P true z else 1) *
          (if tw.2 then groupSign P true (zp z) else 1)):ℝ)) :=
        source_native_B494_complex_four_sign_projector434
          (hKernel z) (groupSign P true z) (groupSign P true (zp z))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro tw htw
        rcases tw with ⟨a,b⟩
        cases a <;> cases b <;> rfl
  change (∑ z ∈ S, hKernel z * (((1-groupSign P true z)/2)*
      ((1-groupSign P true (zp z))/2):ℝ)) =
    ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ z ∈ S, hKernel z *
        ((groupSign P tw.1 z*groupSign P tw.2 (zp z)):ℝ))
  calc
    _ = ∑ z ∈ S, ∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw *
        (hKernel z *
          ((groupSign P tw.1 z*groupSign P tw.2 (zp z)):ℝ)) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hPoint z
    _ = ∑ tw : Bool × Bool, ∑ z ∈ S,
      sourceOriginalB430ParityCoefficient tw *
        (hKernel z *
          ((groupSign P tw.1 z*groupSign P tw.2 (zp z)):ℝ)) := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro tw htw
        rw [Finset.mul_sum]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalFockPGatedPhysicalBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Full original P-gated physical kernel with LITERAL source Fock ordinary
sourceCore at two endpoints, original QSkip factorial residual and Mellin
phases, and physical integer shift 2k. P-pair gates remain unchanged. -/
noncomputable def sourceNativeB538FockPGatedKernel434
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z : ℕ) : ℂ :=
  let zp := ((z:ℤ)+2*k).toNat
  if 0 < (z:ℤ)+2*k ∧
     sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
     sourceOriginalPPrimePart (Finset.univ.biUnion P) zp ∈ R then
    psi z * imaginaryPower z a1 * imaginaryPower zp a2 *
    star (sourceNativeB525ActualFockEndpointCore434 P r d L b slot
      δF ξF KF alphaF q χ σF0 σF1 z) *
    sourceNativeB525ActualFockEndpointCore434 P r d L b slot
      δG ξG KG alphaG q χ σG0 σG1 zp *
    ((sourceMarkedWeight (1/2:ℝ) 1 P z *
      sourceMarkedWeight (1/2:ℝ) 1 P zp:ℝ):ℂ)
  else 0


/-- The literal original Fock/QSkip kernel equals the genuine T P-gated
kernel at the same physical z and z+2k, with both original P-part gates,
independent finite cofactor masks, factorial residuals, Mellin phases and
physical marked weights unchanged. No roughness or analytic estimate is
assumed or inferred. -/
theorem source_native_B538_original_Fock_P_gated_kernel_eq_T434
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z : ℕ) :
    sourceNativeB538FockPGatedKernel434 g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi z =
    sourceNativeGatedGramKernel P R
      (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1) k a1 a2 psi z := by
  unfold sourceNativeB538FockPGatedKernel434 sourceNativeGatedGramKernel
  dsimp only
  split_ifs with hgate
  · unfold sourceNativeB525ActualFockEndpointCore434
    rw [source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
          P r d L b slot δF ξF KF alphaF q χ σF0 σF1 z,
        source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
          P r d L b slot δG ξG KG alphaG q χ σG0 σG1
          (((z:ℤ)+2*k).toNat)]
  · rfl

/-- Original Fock P-gated channel on the literal supplied finite tagged
position support; there is no replacement of S by an interval. -/
noncomputable def sourceNativeB538FockPGatedChannel434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (twF twG : Bool) : ℂ :=
  ∑ z ∈ Spos, sourceNativeB538FockPGatedKernel434
    g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi z *
    ((groupSign P twF z * groupSign P twG (((z:ℤ)+2*k).toNat):ℝ):ℂ)

/-- Both independent physical endpoint signs and all actual tagged
positions survive the literal Fock/native P-gated kernel bridge. -/
theorem source_native_B538_original_Fock_P_gated_channel_eq_T434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (twF twG : Bool) :
    sourceNativeB538FockPGatedChannel434 Spos
      g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi twF twG =
    sourceNativeGatedChannel Spos P R
      (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1) k a1 a2 psi twF twG := by
  unfold sourceNativeB538FockPGatedChannel434 sourceNativeGatedChannel
  apply Finset.sum_congr rfl
  intro z hz
  rw [source_native_B538_original_Fock_P_gated_kernel_eq_T434]

/-- True four-sign projector applied to the coherent original Fock
kernel before any norm or square, on the same tagged-position support. -/
noncomputable def sourceNativeB538FockPGatedProjected434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) : ℂ :=
  ∑ z ∈ Spos, sourceNativeB538FockPGatedKernel434
    g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi z *
    (((1-groupSign P true z)/2)*
      ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2):ℝ)

/-- Exact coherent projected Fock/native equality. The four-sign
projector precedes the square; no scalar-to-character RMS transfer or
loss of either P gate is used. -/
theorem source_native_B538_original_Fock_P_gated_projected_eq_T434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) :
    sourceNativeB538FockPGatedProjected434 Spos
      g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi =
    sourceNativeB522GatedPhysicalProjected434 Spos P R
      (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1) k a1 a2 psi := by
  unfold sourceNativeB538FockPGatedProjected434 sourceNativeB522GatedPhysicalProjected434
  apply Finset.sum_congr rfl
  intro z hz
  rw [source_native_B538_original_Fock_P_gated_kernel_eq_T434]

/-- Exact four-channel expansion of the original Fock P-gated
correlation, obtained by transporting the already checked native
projector identity, with the (+,-,-,+)/4 coefficients inside the norm. -/
theorem source_native_B538_original_Fock_P_gated_four_sign_eq_T434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) :
    sourceNativeB538FockPGatedProjected434 Spos
      g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi =
    ∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw *
        sourceNativeGatedChannel Spos P R
          (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
          (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1) k a1 a2 psi tw.1 tw.2 := by
  rw [source_native_B538_original_Fock_P_gated_projected_eq_T434]
  exact source_native_B522_literal_gated_four_sign_projector434
    Spos P R _ _ k a1 a2 psi

/-- Exact normalized post-square character RMS transport for the
complete P-gated original Fock correlation. This is substitution of
pointwise equal character-dependent kernels, NOT a scalar-discrepancy
RMS estimate. It asserts no inverse-log cancellation. -/
theorem source_native_B538_original_Fock_P_gated_character_RMS_eq_T434
    (Spos : Finset ℕ)
    (g : ℕ) (P : Fin g → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ)
    (q : ℕ) (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖((q.totient:ℂ)⁻¹)‖ *
      ‖sourceNativeB538FockPGatedProjected434 Spos
        g P R r d L b slot δF δG ξF ξG KF KG alphaF alphaG q χ σF0 σF1 σG0 σG1 k a1 a2 psi‖^2) =
    ∑ χ : DirichletCharacter ℂ q, ‖((q.totient:ℂ)⁻¹)‖ *
      ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativePrimeCore r d L b slot δF ξF KF alphaF q χ σF0 σF1)
        (sourceNativePrimeCore r d L b slot δG ξG KG alphaG q χ σG0 σG1) k a1 a2 psi‖^2 := by
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [source_native_B538_original_Fock_P_gated_projected_eq_T434]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## PhysicalMellinNearDiagonal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Logarithm is 1/Z-Lipschitz on the positive half-line [Z,infinity).
This estimate keeps the true additive distance of the physical endpoints. -/
theorem source_native_B540_log_difference_le434
    (x y Z : ℝ) (hZ : 0 < Z) (hx : Z ≤ x) (hy : Z ≤ y) :
    |Real.log y - Real.log x| ≤ |y-x|/Z := by
  have hx0 : 0 < x := hZ.trans_le hx
  have hy0 : 0 < y := hZ.trans_le hy
  have hForward (u v : ℝ) (hu : Z ≤ u) (hv : Z ≤ v) (huv : u ≤ v) :
      Real.log v - Real.log u ≤ (v-u)/Z := by
    have hu0 : 0 < u := hZ.trans_le hu
    have hv0 : 0 < v := hZ.trans_le hv
    have hlog := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    rw [Real.log_div (ne_of_gt hv0) (ne_of_gt hu0)] at hlog
    calc
      Real.log v - Real.log u ≤ v/u - 1 := hlog
      _ = (v-u)/u := by field_simp
      _ ≤ (v-u)/Z := div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hZ hu
  by_cases hxy : x ≤ y
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hForward x y hx hy hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [abs_sub_comm (Real.log y) (Real.log x),abs_sub_comm y x,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hForward y x hy hx hyx

/-- Literal native imaginaryPower, not a substituted Fourier phase. -/
theorem source_native_B540_imaginaryPower_exp434
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    imaginaryPower n a = Complex.exp (Complex.I * ((a*Real.log (n:ℝ):ℝ):ℂ)) := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [imaginaryPower,Complex.cpow_def_of_ne_zero hnC]
  rw [←Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem source_native_B540_imaginaryPower_norm_one434
    (n : ℕ) (hn : 0 < n) (a : ℝ) : ‖imaginaryPower n a‖ = 1 := by
  rw [source_native_B540_imaginaryPower_exp434 n hn a,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Real.exp_zero]

/-- The two true physical Mellin parameters split into one common
Mellin parameter a1+a2 and an additive-shift shear of size log(z'/z). -/
theorem source_native_B540_physical_phase_exact434
    (z zp : ℕ) (hz : 0 < z) (hzp : 0 < zp) (a1 a2 : ℝ) :
    imaginaryPower z a1 * imaginaryPower zp a2 =
      imaginaryPower z (a1+a2) *
        Complex.exp (Complex.I *
          ((a2*(Real.log (zp:ℝ)-Real.log (z:ℝ)):ℝ):ℂ)) := by
  rw [source_native_B540_imaginaryPower_exp434 z hz a1,
    source_native_B540_imaginaryPower_exp434 zp hzp a2,
    source_native_B540_imaginaryPower_exp434 z hz (a1+a2),
    ←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At the ACTUAL integer shift 2*k the extra physical Mellin phase is
uniformly small: its error is at most |a2|*|2k|/Z whenever both endpoints
are at least Z. No statement about the QSkip/cofactor phases is made. -/
theorem source_native_B540_physical_shift_two_phase_bound434
    (z : ℕ) (k : ℤ) (a1 a2 Z : ℝ) (hZ : 0 < Z)
    (hz : Z ≤ (z:ℝ))
    (hzp : Z ≤ ((((z:ℤ)+2*k).toNat:ℕ):ℝ)) :
    ‖imaginaryPower z a1 * imaginaryPower (((z:ℤ)+2*k).toNat) a2 -
      imaginaryPower z (a1+a2)‖ ≤ |a2| * |((2*k:ℤ):ℝ)| / Z := by
  let zp : ℕ := ((z:ℤ)+2*k).toNat
  have hz0 : 0 < z := by exact_mod_cast hZ.trans_le hz
  have hzp0 : 0 < zp := by exact_mod_cast hZ.trans_le hzp
  have hpos : 0 < (z:ℤ)+2*k := by omega
  have heq : (zp:ℝ)-(z:ℝ) = ((2*k:ℤ):ℝ) := by
    have hh : (zp:ℤ) = (z:ℤ)+2*k := Int.toNat_of_nonneg hpos.le
    have hr : (zp:ℝ) = (z:ℝ)+((2*k:ℤ):ℝ) := by exact_mod_cast hh
    linarith
  have hLog := source_native_B540_log_difference_le434
    (z:ℝ) (zp:ℝ) Z hZ hz hzp
  rw [heq] at hLog
  have hExp := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := a2*(Real.log (zp:ℝ)-Real.log (z:ℝ)))
  rw [Real.norm_eq_abs,abs_mul] at hExp
  have hExact := source_native_B540_physical_phase_exact434 z zp hz0 hzp0 a1 a2
  change ‖imaginaryPower z a1 * imaginaryPower zp a2 -
      imaginaryPower z (a1+a2)‖ ≤ _
  rw [hExact,←mul_sub_one,norm_mul,
    source_native_B540_imaginaryPower_norm_one434 z hz0 (a1+a2),one_mul]
  calc
    _ ≤ |a2| * |Real.log (zp:ℝ)-Real.log (z:ℝ)| := hExp
    _ ≤ |a2| * (|((2*k:ℤ):ℝ)| / Z) :=
      mul_le_mul_of_nonneg_left hLog (abs_nonneg a2)
    _ = |a2| * |((2*k:ℤ):ℝ)| / Z := by push_cast; ring

/-- Specialization to the LITERAL original D61 outer Fourier arguments
A1=2*pi*(rho+zeta2), A2=-2*pi*rho. The common phase is exactly
z^(2*pi*i*zeta2); increasing rho contributes only the tiny shift shear.
The inner cofactor/QSkip frequencies are deliberately unchanged. -/
theorem source_native_B540_D61_outer_Fourier_shear434
    (z : ℕ) (k : ℤ) (rho zeta2 Z : ℝ) (hZ : 0 < Z)
    (hz : Z ≤ (z:ℝ))
    (hzp : Z ≤ ((((z:ℤ)+2*k).toNat:ℕ):ℝ)) :
    ‖imaginaryPower z (2*Real.pi*(rho+zeta2)) *
        imaginaryPower (((z:ℤ)+2*k).toNat) (-2*Real.pi*rho) -
      imaginaryPower z (2*Real.pi*zeta2)‖ ≤
        (2*Real.pi*|rho|) * |((2*k:ℤ):ℝ)| / Z := by
  have hsum : 2*Real.pi*(rho+zeta2)+(-2*Real.pi*rho) =
      2*Real.pi*zeta2 := by ring
  have habs : |-2*Real.pi*rho| = 2*Real.pi*|rho| := by
    rw [abs_mul,abs_mul,abs_of_pos Real.pi_pos]
    norm_num
  have hh := source_native_B540_physical_shift_two_phase_bound434
    z k (2*Real.pi*(rho+zeta2)) (-2*Real.pi*rho) Z hZ hz hzp
  rw [hsum,habs] at hh
  exact hh

/-- The original P-gated arithmetic kernel factors its actual physical
outer Mellin phase exactly, retaining both endpoint cores, P-part gates,
psi and every marked weight in the zero-outer-frequency kernel. -/
theorem source_native_B540_original_kernel_outer_phase_factor434
    {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (R : Finset ℕ)
    (F G : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z : ℕ) :
    sourceNativeGatedGramKernel P R F G k a1 a2 psi z =
      (imaginaryPower z a1 * imaginaryPower (((z:ℤ)+2*k).toNat) a2) *
        sourceNativeGatedGramKernel P R F G k 0 0 psi z := by
  dsimp only [sourceNativeGatedGramKernel]
  split_ifs <;> simp only [imaginaryPower,Complex.ofReal_zero,mul_zero,Complex.cpow_zero] <;> ring

/-- Quantified near-diagonal transport for the COMPLETE ORIGINAL tagged
P-gated projected kernel, with the physical four signs still before norm.
The perturbation cost is the explicit actual zero-outer-phase total
variation, not a presumed polynomial cap. This is no inverse-log RMS
saving: it proves exactly how little independent outer phase the two
nearby physical positions can supply. -/
theorem source_native_B540_full_P_gated_projected_phase_transport434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ) (F G : PrimeSlotCore)
    (k : ℤ) (a1 a2 Z : ℝ) (psi : ℕ → ℂ) (hZ : 0 < Z)
    (hlo : ∀ z ∈ S, Z ≤ (z:ℝ))
    (hhi : ∀ z ∈ S, Z ≤ ((((z:ℤ)+2*k).toNat:ℕ):ℝ)) :
    ‖sourceNativeB522GatedPhysicalProjected434 S P R F G k a1 a2 psi -
      sourceNativeB522GatedPhysicalProjected434 S P R F G k (a1+a2) 0 psi‖ ≤
    (|a2| * |((2*k:ℤ):ℝ)| / Z) *
      ∑ z ∈ S, ‖sourceNativeGatedGramKernel P R F G k 0 0 psi z *
        (((1-groupSign P true z)/2) *
         ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2) : ℝ)‖ := by
  let eps : ℝ := |a2| * |((2*k:ℤ):ℝ)| / Z
  let proj : ℕ → ℂ := fun z =>
    ((((1-groupSign P true z)/2) *
      ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2) : ℝ):ℂ)
  let A : ℕ → ℂ := fun z =>
    sourceNativeGatedGramKernel P R F G k 0 0 psi z * proj z
  have hPoint (z : ℕ) :
      sourceNativeGatedGramKernel P R F G k a1 a2 psi z * proj z -
      sourceNativeGatedGramKernel P R F G k (a1+a2) 0 psi z * proj z =
      (imaginaryPower z a1 * imaginaryPower (((z:ℤ)+2*k).toNat) a2 -
        imaginaryPower z (a1+a2)) * A z := by
    rw [source_native_B540_original_kernel_outer_phase_factor434
      P R F G k a1 a2 psi z,
      source_native_B540_original_kernel_outer_phase_factor434
      P R F G k (a1+a2) 0 psi z]
    have hzero : imaginaryPower (((z:ℤ)+2*k).toNat) 0 = 1 := by
      simp only [imaginaryPower,Complex.ofReal_zero,mul_zero,Complex.cpow_zero]
    rw [hzero]
    dsimp only [A]
    ring
  have hEstimate (z : ℕ) (hz : z ∈ S) :
      ‖sourceNativeGatedGramKernel P R F G k a1 a2 psi z * proj z -
        sourceNativeGatedGramKernel P R F G k (a1+a2) 0 psi z * proj z‖ ≤
      eps * ‖A z‖ := by
    rw [hPoint,norm_mul]
    exact mul_le_mul_of_nonneg_right
      (source_native_B540_physical_shift_two_phase_bound434
        z k a1 a2 Z hZ (hlo z hz) (hhi z hz)) (norm_nonneg _)
  change ‖(∑ z ∈ S,
      sourceNativeGatedGramKernel P R F G k a1 a2 psi z * proj z) -
    (∑ z ∈ S,
      sourceNativeGatedGramKernel P R F G k (a1+a2) 0 psi z * proj z)‖ ≤
    eps * ∑ z ∈ S, ‖A z‖
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z ∈ S,
      ‖sourceNativeGatedGramKernel P R F G k a1 a2 psi z * proj z -
        sourceNativeGatedGramKernel P R F G k (a1+a2) 0 psi z * proj z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ z ∈ S, eps*‖A z‖ := Finset.sum_le_sum hEstimate
    _ = eps * ∑ z ∈ S, ‖A z‖ := (Finset.mul_sum _ _ _).symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKGatedCofactorExpansion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Literal T gated native physical cofactor term retaining BOTH original
P-prime-part divisibility gates, true physical shift 2k, ψ(z), original
source marked weights, Mellin exponents, complete Q/P m,p residuals.
The coprimality selector is exact under the original source rough floor. -/
noncomputable def sourceNativeB523GatedCoprimeTerm434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z m t : ℕ) : ℂ :=
  let zR := ((z:ℤ)+2*k).toNat
  if 0 < (z:ℤ)+2*k ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) zR ∈ R then
    if Nat.Coprime m t then
      psi z * imaginaryPower z a1 * imaginaryPower zR a2 *
        star (sourceNativePrimeCoreCofactor434 P F z m) *
        sourceNativePrimeCoreCofactor434 P H zR t *
        ((sourceMarkedWeight (1/2:ℝ) 1 P z *
          sourceMarkedWeight (1/2:ℝ) 1 P zR : ℝ):ℂ)
    else 0
  else 0

/-- Exact ORIGINAL T P-PART GATED Q/P source kernel, with literal original
sorted-QSkip/factorial K-restricted D20 alpha, equals the true coprime
cofactor double sum at each physical z and z+2k. Every inherited gate
and ψ(z)/Mellin/marked weight is identical. No ungated substitution. -/
theorem source_native_B523_K_original_P_gated_cofactor_exact434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (H : PrimeSlotCore)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ) (z : ℕ) (hz : z ≠ 0) :
    let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    sourceNativeGatedGramKernel P R Fcore H k a1 a2 psi z =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      sourceNativeB523GatedCoprimeTerm434 P R Fcore H k a1 a2 psi z m t := by
  dsimp only
  let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  let gate : Prop := 0 < (z:ℤ)+2*k ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) zR ∈ R
  by_cases hg : gate
  · dsimp only [gate,zR] at hg
    have hp : 0 < (z:ℤ)+2*k := hg.1
    have hCore := source_native_B514_original_K_D20_shifted_QP_coprime_exact434
      P r d L b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ H z k hz hk hp hsmall
    change star (primeSlotCoreValue P Fcore z) * primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P Fcore z m) *
            sourceNativePrimeCoreCofactor434 P H zR t else 0 at hCore
    let pref : ℂ := psi z * imaginaryPower z a1 * imaginaryPower zR a2
    let w : ℂ := ((sourceMarkedWeight (1/2:ℝ) 1 P z *
       sourceMarkedWeight (1/2:ℝ) 1 P zR : ℝ):ℂ)
    have hPhysical : sourceNativeGatedGramKernel P R Fcore H k a1 a2 psi z =
      pref * (star (primeSlotCoreValue P Fcore z) *
              primeSlotCoreValue P H zR) * w := by
      unfold sourceNativeGatedGramKernel
      simp only [show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring]
      simp only [if_pos hg]
      dsimp only [pref,w,zR]
      ring
    rw [hPhysical,hCore]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [sourceNativeB523GatedCoprimeTerm434,zR]
    simp only [if_pos hg]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      dsimp only [pref,w]
      ring
    · simp only [if_neg hc]
      ring
  · dsimp only [gate,zR] at hg
    simp only [sourceNativeB523GatedCoprimeTerm434,
      sourceNativeGatedGramKernel,
      show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring,
      if_neg hg,Finset.sum_const_zero]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKGatedProjectedPhysicalCorrelation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Literal original P-PART-GATED, physically FOUR-SIGN-PROJECTED source
cofactor amplitude at z and z+2k, with exact source-native Q/P m,p core.
Every gate, tag and physical mark remains in this cofactor term. -/
noncomputable def sourceNativeB524GatedProjectedCofactorTerm434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z m t : ℕ) : ℂ :=
  sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t *
    (((1-groupSign P true z)/2) *
     ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2) : ℝ)

/-- Full finite physically tagged position set S, original TWO P-part
gates at z and z+2k, true signed D20 alpha restricted to K inside the
ORIGINAL sorted-QSkip/factorial T sourceNativePrimeCore, and both endpoint
odd projectors. The entire original gated physical projected correlation
is an EXACT position-dependent COPRIME Q/P cofactor sum. No replacement
by the ungated Schwartz interval, no new estimates or counting loss. -/
theorem source_native_B524_K_original_FULL_gated_projected_coprime_exact434
    {ι : Type} [Fintype ι]
    (S : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (H : PrimeSlotCore)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ S, z ≠ 0) :
    let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
    sourceNativeB522GatedPhysicalProjected434 S P R Fcore H k a1 a2 psi =
    ∑ z ∈ S,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
        sourceNativeB524GatedProjectedCofactorTerm434
          P R Fcore H k a1 a2 psi z m t := by
  dsimp only
  let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
  unfold sourceNativeB522GatedPhysicalProjected434
  apply Finset.sum_congr rfl
  intro z hz
  have hh := source_native_B523_K_original_P_gated_cofactor_exact434
    P R r d L b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ H
    k hk hsmall a1 a2 psi z (hS z hz)
  change sourceNativeGatedGramKernel P R Fcore H k a1 a2 psi z =
    ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
    ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors,
      sourceNativeB523GatedCoprimeTerm434 P R Fcore H k a1 a2 psi z m t at hh
  rw [hh,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  rfl
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## GatedOriginalKActiveTriples -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- True T P-gated physically tagged finite (z,m,t) divisors: S is the
ORIGINAL tagged z-support, not a rectangular or artificial dyadic set.
All cofactor divisors depend on z and the original physical shift 2k. -/
noncomputable def sourceNativeB525FullGatedTriples434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (k : ℤ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  S.sigma (fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors)

/-- Exactly the original two independent K-restricted centered D20
cofactor supports on the true T tagged position-dependent triples.
The original P-part endpoint gates stay INSIDE each physical amplitude
and are not replaced by a surrogate support. -/
noncomputable def sourceNativeB525OriginalKActiveGatedTriples434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (k : ℤ)
    (KF KG : Finset ℕ) (Δ W y : ℝ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (sourceNativeB525FullGatedTriples434 S P k).filter (fun s =>
    (s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
    (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0))

/-- Literal source Q/P P-GATED cofactor term vanishes for zero source alpha,
regardless of P-gates, marked factors, Mellin phases or endpoint twists. -/
theorem source_native_B525_P_gated_cofactor_zero_left434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z m t : ℕ) (ha : F.alpha m = 0) :
    sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t = 0 := by
  have hc := source_native_B491_QP_cofactor_alpha_zero434 P F z m ha
  unfold sourceNativeB523GatedCoprimeTerm434
  split_ifs <;> simp [hc]

/-- Same exact zero for zero TARGET cofactor alpha at physical z+2k. -/
theorem source_native_B525_P_gated_cofactor_zero_right434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z m t : ℕ) (ha : H.alpha t = 0) :
    sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t = 0 := by
  have hc := source_native_B491_QP_cofactor_alpha_zero434 P H
    (((z:ℤ)+2*k).toNat) t ha
  unfold sourceNativeB523GatedCoprimeTerm434
  split_ifs <;> simp [hc]

/-- Original source+target K-restricted sorted-QSkip/factorial Q/P
cofactor term is ZERO outside its genuine original active K×Delta support,
even with both P-prime-part gates, both physical marks and all phases.
No active term is discarded based on size or frequency. -/
theorem source_native_B525_P_gated_actual_K_zero_outside434
    {ι : Type} [Fintype ι]
    (S : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (s : Σ _ : ℕ, ℕ × ℕ)
    (hs : s ∈ sourceNativeB525FullGatedTriples434 S P k)
    (hn : s ∉ sourceNativeB525OriginalKActiveGatedTriples434
      S P k KF KG Δ W y) :
    sourceNativeB523GatedCoprimeTerm434 P R
      (sourceNativePrimeCore r d L b slot δF ξF KF
        (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG
        (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1)
      k a1 a2 psi s.1 s.2.1 s.2.2 = 0 := by
  let Fcore := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
  let Gcore := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
  have hbad : ¬ ((s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
      (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0)) := by
    intro h
    exact hn (Finset.mem_filter.mpr ⟨hs,h⟩)
  by_cases hF : s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0
  · have hG : Gcore.alpha s.2.2 = 0 := by
      by_contra hne
      exact hbad ⟨hF,(source_native_B510_original_K_D20_nonzero_support434
        r d L b slot δG ξG KG Δ W y q χ σG0 σG1 s.2.2 hne)⟩
    exact source_native_B525_P_gated_cofactor_zero_right434
      P R Fcore Gcore k a1 a2 psi s.1 s.2.1 s.2.2 hG
  · have hFzero : Fcore.alpha s.2.1 = 0 := by
      by_contra hne
      exact hF (source_native_B510_original_K_D20_nonzero_support434
        r d L b slot δF ξF KF Δ W y q χ σF0 σF1 s.2.1 hne)
    exact source_native_B525_P_gated_cofactor_zero_left434
      P R Fcore Gcore k a1 a2 psi s.1 s.2.1 s.2.2 hFzero
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullGatedNativeKPhysicalTripleSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The complete original P-part GATED physical four-sign projected Q/P
correlation, with BOTH literal source+target sorted-QSkip/factorial cores
and their separate original cofactor supports KF,KG, equals an EXACT
coherent sum over the true tagged position-dependent active (z,m,t)
triples. The original P-pair gates are retained INSIDE each amplitude.
Zero terms are removed only by the literal K-restricted D20 coefficients.
There is no dyadic-interval substitution or early norm/character average. -/
theorem source_native_B526_K_original_FULL_P_gated_active_triples_exact434
    {ι : Type} [Fintype ι]
    (S : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ S, z ≠ 0) :
    let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
    let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
    let T := sourceNativeB525OriginalKActiveGatedTriples434
      S P k KF KG Δ W y
    sourceNativeB522GatedPhysicalProjected434 S P R Fχ Gχ k a1 a2 psi =
    ∑ s ∈ T, sourceNativeB524GatedProjectedCofactorTerm434 P R Fχ Gχ
      k a1 a2 psi s.1 s.2.1 s.2.2 := by
  dsimp only
  let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
  let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
  let D : ℕ → Finset (ℕ×ℕ) := fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors
  let Tfull : Finset (Σ _ : ℕ, ℕ×ℕ) := S.sigma D
  let T : Finset (Σ _ : ℕ, ℕ×ℕ) := Tfull.filter (fun s =>
    (s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
    (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0))
  let B : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB524GatedProjectedCofactorTerm434 P R Fχ Gχ
      k a1 a2 psi s.1 s.2.1 s.2.2
  have hBase := source_native_B524_K_original_FULL_gated_projected_coprime_exact434
    S P R r d L b slot δF ξF KF Δ W y hWy
    q χ σF0 σF1 Gχ k hk hsmall a1 a2 psi hS
  have hSigma : (∑ z ∈ S, ∑ v ∈ D z, B ⟨z,v⟩) =
      ∑ s ∈ Tfull, B s :=
    (Finset.sum_sigma S D B).symm
  have hZero (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ Tfull)
      (hsnot : s ∉ T) : B s = 0 := by
    have hh := source_native_B525_P_gated_actual_K_zero_outside434
      S P R r d L b slot δF δG ξF ξG KF KG Δ W y
      q χ σF0 σF1 σG0 σG1 k a1 a2 psi s hs hsnot
    change sourceNativeB523GatedCoprimeTerm434 P R Fχ Gχ
      k a1 a2 psi s.1 s.2.1 s.2.2 = 0 at hh
    change sourceNativeB524GatedProjectedCofactorTerm434 P R Fχ Gχ
      k a1 a2 psi s.1 s.2.1 s.2.2 = 0
    unfold sourceNativeB524GatedProjectedCofactorTerm434
    rw [hh]
    simp
  have hFilter : (∑ s ∈ T, B s) = ∑ s ∈ Tfull, B s :=
    Finset.sum_subset (Finset.filter_subset _ _) hZero
  change sourceNativeB522GatedPhysicalProjected434 S P R Fχ Gχ k a1 a2 psi =
    ∑ s ∈ T, B s
  calc
    _ = ∑ z ∈ S,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors, B ⟨z,(m,t)⟩ := hBase
    _ = ∑ z ∈ S, ∑ v ∈ D z, B ⟨z,v⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Finset.sum_product
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors
        (fun v : ℕ×ℕ => B ⟨z,v⟩)).symm
    _ = ∑ s ∈ Tfull, B s := hSigma
    _ = ∑ s ∈ T, B s := hFilter.symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## GatedOriginalKCharacterFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- ORIGINAL T P-GATED physical cofactor m,t amplitude, with original
independent sorted-QSkip/factorial Fourier residuals and BOTH source/target
K-restricted D20 coefficients, factors EXACTLY as χ̄(m)χ(t) times the
same genuine gated, character-free Q/P cofactor amplitude. Original P-part
pair gates and full source marked/ψ(z)/Mellin factors remain untouched.
The character factorization precedes parity projection and RMS squaring. -/
theorem source_native_B527_original_K_P_gated_character_factor434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z m t : ℕ) :
    let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
    let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
    let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
    let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
    sourceNativeB523GatedCoprimeTerm434 P R Fχ Gχ k a1 a2 psi z m t =
      sourceNativeB496PhysicalPairCharacter434 q m t χ *
        sourceNativeB523GatedCoprimeTerm434 P R F0 G0 k a1 a2 psi z m t := by
  dsimp only
  let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
  let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
  change sourceNativeB523GatedCoprimeTerm434 P R
    (sourceNativeWithCharacter434 F0 q χ)
    (sourceNativeWithCharacter434 G0 q χ) k a1 a2 psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB523GatedCoprimeTerm434 P R F0 G0 k a1 a2 psi z m t
  let gate : Prop := 0 < (z:ℤ)+2*k ∧
    sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
    sourceOriginalPPrimePart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat) ∈ R
  by_cases hg : gate
  · dsimp only [gate] at hg
    unfold sourceNativeB523GatedCoprimeTerm434
    simp only [if_pos hg]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      rw [source_native_B495_QP_cofactor_character_factor434 P F0 q χ z m,
        source_native_B495_QP_cofactor_character_factor434 P G0 q χ
          (((z:ℤ)+2*k).toNat) t,star_mul]
      have hF0 : sourceNativeWithoutCharacter434 F0 = F0 := rfl
      have hG0 : sourceNativeWithoutCharacter434 G0 = G0 := rfl
      rw [hF0,hG0]
      unfold sourceNativeB496PhysicalPairCharacter434
      ring
    · simp [hc]
  · dsimp only [gate] at hg
    simp [sourceNativeB523GatedCoprimeTerm434,hg]

/-- Exact same original K-restricted character factor AFTER full original
(+,-,-,+)/4 endpoint projection. The P-gates, true tagged position z,
source QSkip and marked weights stay inside the true physical amplitude. -/
theorem source_native_B527_original_K_P_gated_PROJECTED_character_factor434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z m t : ℕ) :
    let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
    let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
    let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
    let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
    sourceNativeB524GatedProjectedCofactorTerm434 P R Fχ Gχ
      k a1 a2 psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB524GatedProjectedCofactorTerm434 P R F0 G0
        k a1 a2 psi z m t := by
  dsimp only
  let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
  let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
  let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
  let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
  have hh := source_native_B527_original_K_P_gated_character_factor434
    P R r d L b slot δF δG ξF ξG KF KG Δ W y
      q χ σF0 σF1 σG0 σG1 k a1 a2 psi z m t
  change sourceNativeB523GatedCoprimeTerm434 P R Fχ Gχ k a1 a2 psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
    sourceNativeB523GatedCoprimeTerm434 P R F0 G0 k a1 a2 psi z m t at hh
  unfold sourceNativeB524GatedProjectedCofactorTerm434
  rw [hh]
  ring
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalTRoughCofactorGeometry -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The actual ORIGINAL T proof contract is `rough W m` for each nonzero
cofactor, not necessarily `alpha(m)=sourceD20FullDelta(m)`. For any such
source rough cofactor dividing physical z, and any target cofactor dividing
z+2k, the TRUE integer shift |2k|≤W forces coprimality. No D20 proxy. -/
theorem source_native_B529_original_rough_shifted_coprime434
    (W : ℝ) (m t z : ℕ) (k : ℤ)
    (hm : rough W m) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hpos : 0 < (z:ℤ)+2*k)
    (hmz : m ∣ z) (htz : t ∣ ((z:ℤ)+2*k).toNat) :
    Nat.Coprime m t := by
  change Nat.gcd m t = 1
  by_contra hne
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_left m t)
  have hpt : p ∣ t := hpg.trans (Nat.gcd_dvd_right m t)
  have hpz : (p:ℤ) ∣ (z:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpm.trans hmz)
  have hpzp : (p:ℤ) ∣ (((z:ℤ)+2*k).toNat:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpt.trans htz)
  rw [Int.toNat_of_nonneg hpos.le] at hpzp
  have hpShift : (p:ℤ) ∣ 2*k := by simpa using dvd_sub hpzp hpz
  have hshiftNZ : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have hpAbs : p ≤ (2*k).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpShift hshiftNZ
  have hpW : (p:ℝ) ≤ W :=
    (by exact_mod_cast hpAbs : (p:ℝ) ≤ ((2*k).natAbs:ℝ)).trans hsmall
  exact (not_le_of_gt (hm.2 p hp hpm)) hpW

/-- The original T rough cofactor premise also makes the cofactor a unit
modulo ANY composite outer Dirichlet modulus q with 0<q≤W. -/
theorem source_native_B529_original_rough_cofactor_unit_mod434
    (W : ℝ) (n q : ℕ) (hn : rough W n)
    (hq : 0 < q) (hqW : (q:ℝ) ≤ W) :
    IsUnit (n : ZMod q) := by
  rw [ZMod.isUnit_iff_coprime]
  change Nat.gcd n q = 1
  by_contra hne
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n q)
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right n q)
  have hpW : (p:ℝ) ≤ W :=
    (by exact_mod_cast Nat.le_of_dvd hq hpq : (p:ℝ) ≤ q).trans hqW
  exact (not_le_of_gt (hn.2 p hp hpn)) hpW

/-- For composite modulus q, original rough-supported source/target
cofactor residues are genuine units and so is their cross-product. -/
theorem source_native_B529_original_rough_cross_unit_mod434
    (W : ℝ) (m t q : ℕ) (hm : rough W m) (ht : rough W t)
    (hq : 0 < q) (hqW : (q:ℝ) ≤ W) :
    IsUnit (((m*t:ℕ):ZMod q)) := by
  have hu1 := source_native_B529_original_rough_cofactor_unit_mod434 W m q hm hq hqW
  have hu2 := source_native_B529_original_rough_cofactor_unit_mod434 W t q ht hq hqW
  rw [Nat.cast_mul]
  exact hu1.mul hu2
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughGeneralGatedCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Original T rough W support on source alpha suffices for exact coprime
cofactor expansion of full Q/P core at physical shift 2k. No D20 proxy,
no cofactor K restriction and no bounds on residuals, slots or characters. -/
theorem source_native_B530_rough_alpha_full_QP_coprime434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (F H : PrimeSlotCore)
    (W : ℝ) (hrough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (z : ℕ) (hz : z ≠ 0) (k : ℤ) (hk : k ≠ 0)
    (hp : 0 < (z:ℤ)+2*k) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    star (primeSlotCoreValue P F z) * primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P F z m) *
            sourceNativePrimeCoreCofactor434 P H zR t
        else 0 := by
  dsimp only
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  have hzR : zR ≠ 0 := by
    dsimp [zR]
    omega
  have hL := source_native_B491_full_QP_core_cofactor_expansion434 P F z
  have hR := source_native_B491_full_QP_core_cofactor_expansion434 P H zR
  change primeSlotCoreValue P F z =
    ∑ m ∈ nsL.divisors, sourceNativePrimeCoreCofactor434 P F z m at hL
  change primeSlotCoreValue P H zR =
    ∑ t ∈ nsR.divisors, sourceNativePrimeCoreCofactor434 P H zR t at hR
  rw [hL,hR,star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases ha : F.alpha m = 0
  · rw [source_native_B491_QP_cofactor_alpha_zero434 P F z m ha]
    simp
  · have hmz : m ∣ z :=
      (Nat.mem_divisors.mp hm).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) z hz)
    have htz : t ∣ zR :=
      (Nat.mem_divisors.mp ht).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) zR hzR)
    have hc : Nat.Coprime m t :=
      source_native_B529_original_rough_shifted_coprime434
        W m t z k (hrough m ha) hk hsmall hp hmz htz
    rw [if_pos hc]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughNativeShiftedCoprime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Stronger than B514: arbitrary original T `PrimeSlotCore.alpha`, with
its EXACT original rough-support hypothesis, yields lossless coprime
source/target m,t at true physical shift 2k. No assumption that the
original alpha equals centered D20 coefficients, no K-mask overwrite.
All Q/P p-divisor ranges, residuals and Mellin/characters are literal. -/
theorem source_native_B530_rough_original_QP_shifted_coprime_exact434
    {ι : Type} [Fintype ι] (P : ι → Finset ℕ)
    (F H : PrimeSlotCore) (W : ℝ)
    (hRough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (z : ℕ) (k : ℤ) (hz : z ≠ 0)
    (hk : k ≠ 0) (hpos : 0 < (z:ℤ)+2*k)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    star (primeSlotCoreValue P F z) * primeSlotCoreValue P H zR =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      if Nat.Coprime m t then
        star (sourceNativePrimeCoreCofactor434 P F z m) *
          sourceNativePrimeCoreCofactor434 P H zR t
      else 0 := by
  dsimp only
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  have hzR : zR ≠ 0 := by dsimp [zR]; omega
  rw [source_native_B491_full_QP_core_cofactor_expansion434 P F z,
      source_native_B491_full_QP_core_cofactor_expansion434 P H zR,
      star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases ha : F.alpha m = 0
  · rw [source_native_B491_QP_cofactor_alpha_zero434 P F z m ha]
    simp
  · have hmz : m ∣ z :=
      (Nat.mem_divisors.mp hm).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) z hz)
    have htz : t ∣ zR :=
      (Nat.mem_divisors.mp ht).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) zR hzR)
    have hc : Nat.Coprime m t :=
      source_native_B529_original_rough_shifted_coprime434
        W m t z k (hRough m ha) hk hsmall hpos hmz htz
    rw [if_pos hc]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughPGatedCoprime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The LITERAL original T P-PART-GATED physical cofactor kernel, at
integer shift 2k, with arbitrary original source alpha supported on
`rough W`. Unlike B523 this theorem imposes NO D20 alpha proxy, no
finite cofactor support K, and no original sorted-QSkip shortcut.
P-prime-part gates on BOTH shifted positions, full Q/P prime slot,
residual, Dirichlet character, Mellin phases and marked source weights
are kept intact before any RMS or Fourier mean. -/
theorem source_native_B531_rough_alpha_original_P_gated_QP_coprime434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ) (F H : PrimeSlotCore)
    (W : ℝ) (hrough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (z : ℕ) (hz : z ≠ 0)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ) :
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    sourceNativeGatedGramKernel P R F H k a1 a2 psi z =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t := by
  dsimp only
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  let gate : Prop := 0 < (z:ℤ)+2*k ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) zR ∈ R
  by_cases hg : gate
  · dsimp only [gate,zR] at hg
    have hp : 0 < (z:ℤ)+2*k := hg.1
    have hCore := source_native_B530_rough_alpha_full_QP_coprime434
      P F H W hrough z hz k hk hp hsmall
    change star (primeSlotCoreValue P F z)*primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P F z m)*
          sourceNativePrimeCoreCofactor434 P H zR t else 0 at hCore
    let pref : ℂ := psi z*imaginaryPower z a1*imaginaryPower zR a2
    let w : ℂ := ((sourceMarkedWeight (1/2:ℝ) 1 P z *
       sourceMarkedWeight (1/2:ℝ) 1 P zR : ℝ):ℂ)
    have hPhysical : sourceNativeGatedGramKernel P R F H k a1 a2 psi z =
      pref * (star (primeSlotCoreValue P F z)*primeSlotCoreValue P H zR)*w := by
      unfold sourceNativeGatedGramKernel
      simp only [show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring]
      simp only [if_pos hg]
      dsimp only [pref,w,zR]
      ring
    rw [hPhysical,hCore]
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [sourceNativeB523GatedCoprimeTerm434,zR]
    simp only [if_pos hg]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      dsimp only [pref,w]
      ring
    · simp only [if_neg hc]
      ring
  · dsimp only [gate,zR] at hg
    simp only [sourceNativeB523GatedCoprimeTerm434,
      sourceNativeGatedGramKernel,
      show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring,
      if_neg hg,Finset.sum_const_zero]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## RoughOriginalPGatedCofactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- GENERIC actual original T physical P-gated kernel at true z+2k,
with arbitrary original Q/P PrimeSlotCore.alpha and its actual rough
support hypothesis, equals COPRIME cofactor double sum with every P-part,
marked, Mellin, Fourier and Q/P residual factor unchanged. This removes
the restrictive D20-alpha premise in the earlier B523 proof. -/
theorem source_native_B531_rough_original_P_gated_cofactor_exact434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (W : ℝ)
    (hRough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ) (z : ℕ) (hz : z ≠ 0) :
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    sourceNativeGatedGramKernel P R F H k a1 a2 psi z =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t := by
  dsimp only
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  let gate : Prop := 0 < (z:ℤ)+2*k ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
      sourceOriginalPPrimePart (Finset.univ.biUnion P) zR ∈ R
  by_cases hg : gate
  · dsimp only [gate,zR] at hg
    have hp : 0 < (z:ℤ)+2*k := hg.1
    have hCore := source_native_B530_rough_original_QP_shifted_coprime_exact434
      P F H W hRough z k hz hk hp hsmall
    change star (primeSlotCoreValue P F z) * primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P F z m) *
            sourceNativePrimeCoreCofactor434 P H zR t else 0 at hCore
    let pref : ℂ := psi z * imaginaryPower z a1 * imaginaryPower zR a2
    let w : ℂ := ((sourceMarkedWeight (1/2:ℝ) 1 P z *
       sourceMarkedWeight (1/2:ℝ) 1 P zR : ℝ):ℂ)
    have hPhysical : sourceNativeGatedGramKernel P R F H k a1 a2 psi z =
      pref * (star (primeSlotCoreValue P F z) *
              primeSlotCoreValue P H zR) * w := by
      unfold sourceNativeGatedGramKernel
      simp only [show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring]
      simp only [if_pos hg]
      dsimp only [pref,w,zR]
      ring
    rw [hPhysical,hCore]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [sourceNativeB523GatedCoprimeTerm434,zR]
    simp only [if_pos hg]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      dsimp only [pref,w]
      ring
    · simp only [if_neg hc]
      ring
  · dsimp only [gate,zR] at hg
    simp only [sourceNativeB523GatedCoprimeTerm434,
      sourceNativeGatedGramKernel,
      show (z:ℤ)+k*2 = (z:ℤ)+2*k from by ring,
      if_neg hg,Finset.sum_const_zero]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## RoughGatedActivePhysicalTriples -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- TRUE original arbitrary rough-supported alpha on BOTH T endpoint
PrimeSlotCore records, with their actual finite tagged z-support and
z-dependent Q/P cofactor divisors. Original P-gates stay inside amplitudes.
No D20 or cofactor centering assumption on alpha. -/
noncomputable def sourceNativeB532RoughActiveGatedTriples434
    (S : Finset ℕ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (k : ℤ)
    (F G : PrimeSlotCore) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (sourceNativeB525FullGatedTriples434 S P k).filter
    (fun s => F.alpha s.2.1 ≠ 0 ∧ G.alpha s.2.2 ≠ 0)

/-- FULL ORIGINAL T P-gated FOUR-SIGN physically tagged Q/P correlation,
with ARBITRARY true rough-supported source F.alpha (not a centered D20
proxy) and arbitrary target G.alpha, equals EXACTLY its finite active
position-dependent coprime cofactor sum. Only zero coefficients are
removed. Preserves both P-part gates, original ψ(z), full Q/P residual,
Mellin phases and physical shift 2k. -/
theorem source_native_B532_original_rough_FULL_P_gated_triples_exact434
    {ι : Type} [Fintype ι]
    (S : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F G : PrimeSlotCore) (W : ℝ)
    (hRoughF : ∀ m, F.alpha m ≠ 0 → rough W m)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ S, z ≠ 0) :
    let T := sourceNativeB532RoughActiveGatedTriples434 S P k F G
    sourceNativeB522GatedPhysicalProjected434 S P R F G k a1 a2 psi =
    ∑ s ∈ T, sourceNativeB524GatedProjectedCofactorTerm434 P R F G
      k a1 a2 psi s.1 s.2.1 s.2.2 := by
  dsimp only
  let D : ℕ → Finset (ℕ×ℕ) := fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors
  let Tfull : Finset (Σ _ : ℕ, ℕ×ℕ) := S.sigma D
  let T : Finset (Σ _ : ℕ, ℕ×ℕ) := Tfull.filter (fun s =>
    F.alpha s.2.1 ≠ 0 ∧ G.alpha s.2.2 ≠ 0)
  let B : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB524GatedProjectedCofactorTerm434 P R F G
      k a1 a2 psi s.1 s.2.1 s.2.2
  have hAt (z : ℕ) (hz : z ∈ S) :
      sourceNativeGatedGramKernel P R F G k a1 a2 psi z =
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
        sourceNativeB523GatedCoprimeTerm434 P R F G
          k a1 a2 psi z m t :=
    source_native_B531_rough_original_P_gated_cofactor_exact434
      P R F G W hRoughF k hk hsmall a1 a2 psi z (hS z hz)
  have hSigma : (∑ z ∈ S, ∑ v ∈ D z, B ⟨z,v⟩) =
      ∑ s ∈ Tfull, B s :=
    (Finset.sum_sigma S D B).symm
  have hZero (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ Tfull)
      (hsnot : s ∉ T) : B s = 0 := by
    have hNo : ¬ (F.alpha s.2.1 ≠ 0 ∧ G.alpha s.2.2 ≠ 0) := by
      intro h
      exact hsnot (Finset.mem_filter.mpr ⟨hs,h⟩)
    by_cases ha : F.alpha s.2.1 = 0
    · change sourceNativeB524GatedProjectedCofactorTerm434 P R F G
        k a1 a2 psi s.1 s.2.1 s.2.2 = 0
      unfold sourceNativeB524GatedProjectedCofactorTerm434
      rw [source_native_B525_P_gated_cofactor_zero_left434
        P R F G k a1 a2 psi s.1 s.2.1 s.2.2 ha]
      simp
    · have hb : G.alpha s.2.2 = 0 := by
        by_contra hnb
        exact hNo ⟨ha,hnb⟩
      change sourceNativeB524GatedProjectedCofactorTerm434 P R F G
        k a1 a2 psi s.1 s.2.1 s.2.2 = 0
      unfold sourceNativeB524GatedProjectedCofactorTerm434
      rw [source_native_B525_P_gated_cofactor_zero_right434
        P R F G k a1 a2 psi s.1 s.2.1 s.2.2 hb]
      simp
  have hFilter : (∑ s ∈ T, B s) = ∑ s ∈ Tfull, B s :=
    Finset.sum_subset (Finset.filter_subset _ _) hZero
  unfold sourceNativeB522GatedPhysicalProjected434
  calc
    _ = ∑ z ∈ S,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors, B ⟨z,(m,t)⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hAt z hz,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
      rfl
    _ = ∑ z ∈ S, ∑ v ∈ D z, B ⟨z,v⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Finset.sum_product
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors
        (fun v : ℕ×ℕ => B ⟨z,v⟩)).symm
    _ = ∑ s ∈ Tfull, B s := hSigma
    _ = ∑ s ∈ T, B s := hFilter.symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughFullPGatedProjected -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The COMPLETE ORIGINAL T P-PART-GATED, physical FOUR-SIGN-projected
correlation at integer shift 2k, over the actual supplied tagged position
set S, with any rough-supported source cofactor sequence alpha. Exactly
expands into the original physical (z,m,t) cofactor terms, coprime by the
true rough-shift geometry. Unlike B524 there is no D20 alpha proxy,
no QSkip restriction and no fictitious Schwartz-interval substitution.
The literal P gates, both Q/P prime-slot/factorial residuals, Mellin
phases, original marked weights and both endpoint signs are retained. -/
theorem source_native_B532_rough_alpha_FULL_P_gated_projected_coprime434
    {ι : Type} [Fintype ι]
    (S : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (W : ℝ) (hrough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ S, z ≠ 0) :
    sourceNativeB522GatedPhysicalProjected434 S P R F H k a1 a2 psi =
    ∑ z ∈ S,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
        sourceNativeB524GatedProjectedCofactorTerm434
          P R F H k a1 a2 psi z m t := by
  unfold sourceNativeB522GatedPhysicalProjected434
  apply Finset.sum_congr rfl
  intro z hz
  have hh := source_native_B531_rough_alpha_original_P_gated_QP_coprime434
    P R F H W hrough z (hS z hz) k hk hsmall a1 a2 psi
  change sourceNativeGatedGramKernel P R F H k a1 a2 psi z =
    ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
          sourceNativeB523GatedCoprimeTerm434 P R F H k a1 a2 psi z m t at hh
  rw [hh,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  rfl
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughGatedCharacterFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- UNIVERSAL ORIGINAL T physical P-PART-GATED cofactor kernel, with any
original PrimeSlotCore alpha/residual/Q/P/Fourier parameters, has exact
character factor conj(χ(m))*χ(t) BEFORE any four-sign projection or RMS.
There is no D20 proxy, finite K restriction, or dropped source marked gate. -/
theorem source_native_B533_original_rough_P_gated_character_factor434
    {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z m t : ℕ) :
    sourceNativeB523GatedCoprimeTerm434 P R
      (sourceNativeWithCharacter434 F q χ)
      (sourceNativeWithCharacter434 H q χ)
      k a1 a2 psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB523GatedCoprimeTerm434 P R
        (sourceNativeWithoutCharacter434 F)
        (sourceNativeWithoutCharacter434 H)
        k a1 a2 psi z m t := by
  let F0 := sourceNativeWithoutCharacter434 F
  let H0 := sourceNativeWithoutCharacter434 H
  have hf0 : sourceNativeWithCharacter434 F q χ =
      sourceNativeWithCharacter434 F0 q χ := rfl
  have hh0 : sourceNativeWithCharacter434 H q χ =
      sourceNativeWithCharacter434 H0 q χ := rfl
  rw [hf0,hh0]
  let gate : Prop := 0 < (z:ℤ)+2*k ∧
    sourceOriginalPPrimePart (Finset.univ.biUnion P) z ∈ R ∧
    sourceOriginalPPrimePart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat) ∈ R
  by_cases hg : gate
  · dsimp only [gate] at hg
    unfold sourceNativeB523GatedCoprimeTerm434
    simp only [if_pos hg]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      rw [source_native_B495_QP_cofactor_character_factor434 P F0 q χ z m,
        source_native_B495_QP_cofactor_character_factor434 P H0 q χ
          (((z:ℤ)+2*k).toNat) t,star_mul]
      have hF0 : sourceNativeWithoutCharacter434 F0 = F0 := rfl
      have hH0 : sourceNativeWithoutCharacter434 H0 = H0 := rfl
      rw [hF0,hH0]
      unfold sourceNativeB496PhysicalPairCharacter434
      ring
    · simp [hc]
  · dsimp only [gate] at hg
    simp [sourceNativeB523GatedCoprimeTerm434,hg]

/-- Exact original (+,-,-,+)/4 two-endpoint projector of the universal
rough-alpha P-gated cofactor retains the SAME physical character factor,
all P-prime-part gates and actual integer shift 2k. -/
theorem source_native_B533_original_rough_P_gated_PROJECTED_factor434
    {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ) (z m t : ℕ) :
    sourceNativeB524GatedProjectedCofactorTerm434 P R
      (sourceNativeWithCharacter434 F q χ)
      (sourceNativeWithCharacter434 H q χ)
      k a1 a2 psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB524GatedProjectedCofactorTerm434 P R
        (sourceNativeWithoutCharacter434 F)
        (sourceNativeWithoutCharacter434 H)
        k a1 a2 psi z m t := by
  unfold sourceNativeB524GatedProjectedCofactorTerm434
  rw [source_native_B533_original_rough_P_gated_character_factor434]
  ring
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullOriginalRoughGatedRatioRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- GENUINE original T source PrimeSlotCore with completely arbitrary
physical alpha and residual on both endpoints, satisfying exactly the
original nonzero-ALPHA ROUGH W-support contract. For the original P-pair
gates and arbitrary positive tagged z-support Spos, full Q/P, 2k shift,
marked weights, Mellin and both parity projectors, the normalized
post-square character RMS equals the sum of squared COHERENT original
physical cofactor ratio-fiber amplitudes t/m mod |k|. Composite moduli are
supported. All offdiagonal signs within each fiber survive, and no
nontrivial TypeII saving is claimed. Crucially NO D20-delta assumption. -/
theorem source_native_B534_full_original_rough_gated_ratio_RMS434
    (g : ℕ) (P : Fin g → Finset ℕ) (Spos R : Finset ℕ)
    (F G : PrimeSlotCore) (W : ℝ)
    (hRoughF : ∀ m, F.alpha m ≠ 0 → rough W m)
    (hRoughG : ∀ t, G.alpha t ≠ 0 → rough W t)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ Spos, z ≠ 0) :
    let F0 := sourceNativeWithoutCharacter434 F
    let G0 := sourceNativeWithoutCharacter434 G
    let T := sourceNativeB532RoughActiveGatedTriples434 Spos P k F0 G0
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB524GatedProjectedCofactorTerm434 P R F0 G0
        k a1 a2 psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
          (sourceNativeWithCharacter434 F0 k.natAbs χ)
          (sourceNativeWithCharacter434 G0 k.natAbs χ)
          k a1 a2 psi‖^2) =
      ∑ v ∈ T.image ratio,
        ‖∑ s ∈ T.filter (fun s => ratio s = v), base s‖^2 := by
  dsimp only
  let F0 := sourceNativeWithoutCharacter434 F
  let G0 := sourceNativeWithoutCharacter434 G
  let T := sourceNativeB532RoughActiveGatedTriples434 Spos P k F0 G0
  let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB524GatedProjectedCofactorTerm434 P R F0 G0
      k a1 a2 psi s.1 s.2.1 s.2.2
  let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
    (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
  have hRF : ∀ m, F0.alpha m ≠ 0 → rough W m := hRoughF
  have hRG : ∀ m, G0.alpha m ≠ 0 → rough W m := hRoughG
  have hnk : k.natAbs ≤ (2*k).natAbs := by
    rw [Int.natAbs_mul]
    change k.natAbs ≤ 2*k.natAbs
    omega
  have hqW : ((k.natAbs:ℕ):ℝ) ≤ W :=
    (by exact_mod_cast hnk : ((k.natAbs:ℕ):ℝ) ≤ ((2*k).natAbs:ℝ)).trans hsmall
  have hUnit (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ T) :
      IsUnit (s.2.1 : ZMod k.natAbs) := by
    have hn := (Finset.mem_filter.mp hs).2.1
    exact source_native_B529_original_rough_cofactor_unit_mod434
      W s.2.1 k.natAbs (hRF s.2.1 hn) (Int.natAbs_pos.mpr hk) hqW
  have hCross : ∀ s ∈ T, ∀ v ∈ T,
      IsUnit (((v.2.1*s.2.2:ℕ):ZMod k.natAbs)) := by
    intro s hs v hv
    have hmp := (Finset.mem_filter.mp hv).2.1
    have ht := (Finset.mem_filter.mp hs).2.2
    exact source_native_B529_original_rough_cross_unit_mod434
      W v.2.1 s.2.2 k.natAbs (hRF v.2.1 hmp) (hRG s.2.2 ht)
      (Int.natAbs_pos.mpr hk) hqW
  have hFactor (χ : DirichletCharacter ℂ k.natAbs)
      (s : Σ _ : ℕ, ℕ×ℕ) :
      sourceNativeB524GatedProjectedCofactorTerm434 P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 G0 k.natAbs χ)
        k a1 a2 psi s.1 s.2.1 s.2.2 =
      base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hh := source_native_B533_original_rough_P_gated_PROJECTED_factor434
      P R F0 G0 k.natAbs χ k a1 a2 psi s.1 s.2.1 s.2.2
    change _ = sourceNativeB496PhysicalPairCharacter434
      k.natAbs s.2.1 s.2.2 χ * base s at hh
    rw [hh]
    ring
  have hWhole (χ : DirichletCharacter ℂ k.natAbs) :
      sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 G0 k.natAbs χ)
        k a1 a2 psi =
      ∑ s ∈ T, base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hRFχ : ∀ m, (sourceNativeWithCharacter434 F0 k.natAbs χ).alpha m ≠ 0 →
        rough W m := hRF
    have hh := source_native_B532_original_rough_FULL_P_gated_triples_exact434
      Spos P R (sourceNativeWithCharacter434 F0 k.natAbs χ)
      (sourceNativeWithCharacter434 G0 k.natAbs χ) W
      hRFχ k hk hsmall a1 a2 psi hS
    change sourceNativeB522GatedPhysicalProjected434 Spos P R
      (sourceNativeWithCharacter434 F0 k.natAbs χ)
      (sourceNativeWithCharacter434 G0 k.natAbs χ)
      k a1 a2 psi =
      ∑ s ∈ T, sourceNativeB524GatedProjectedCofactorTerm434 P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 G0 k.natAbs χ)
        k a1 a2 psi s.1 s.2.1 s.2.2 at hh
    calc
      _ = ∑ s ∈ T, sourceNativeB524GatedProjectedCofactorTerm434 P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 G0 k.natAbs χ)
        k a1 a2 psi s.1 s.2.1 s.2.2 := hh
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hFactor χ s
  have hGram := source_native_B501_finite_physical_character_RMS_residue_only434
    T k.natAbs (Int.natAbs_pos.mpr hk)
    (fun s => s.2.1) (fun s => s.2.2) base hCross
  have hFibers := source_native_B506_finite_ratio_fiber_square_identity434
    T ratio base
  have hCong (s v : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ T) (hv : v ∈ T) :
      (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
       ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) ↔ ratio s = ratio v :=
    source_native_B505_original_QP_cross_residue_iff_ratio434
      k.natAbs s.2.1 s.2.2 v.2.1 v.2.2 (hUnit s hs) (hUnit v hv)
  calc
    _ = ∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖∑ s ∈ T,
          base s * sourceNativeB496PhysicalPairCharacter434
            k.natAbs s.2.1 s.2.2 χ‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hWhole χ]
    _ = ∑ s ∈ T, ∑ v ∈ T,
      if (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) then
        (star (base s)*base v).re else 0 := hGram
    _ = ∑ s ∈ T, ∑ v ∈ T,
      if ratio s = ratio v then (star (base s)*base v).re else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      by_cases he : (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs))
      · have hr := (hCong s v hs hv).mp he
        simp only [if_pos he,if_pos hr]
      · have hr : ratio s ≠ ratio v :=
          fun h => he ((hCong s v hs hv).mpr h)
        simp only [if_neg he,if_neg hr]
    _ = ∑ v ∈ T.image ratio,
      ‖∑ s ∈ T.filter (fun s => ratio s = v), base s‖^2 := by
      simpa only using hFibers
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughActiveGatedTriples -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The true ORIGINAL Q/P physical tagged position-cofactor triple support
with the ORIGINAL alpha fields of both endpoints (not D20 proxy and no
artificial K restrictions). Each source/target factor is zero off support,
with the original P-part gates still INSIDE the projected amplitudes. -/
noncomputable def sourceNativeB534OriginalRoughActiveTriples434
    {ι : Type} [Fintype ι]
    (Spos : Finset ℕ) (P : ι → Finset ℕ)
    (k : ℤ) (F H : PrimeSlotCore) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Spos.sigma (fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors)).filter
    (fun s => F.alpha s.2.1 ≠ 0 ∧ H.alpha s.2.2 ≠ 0)

/-- Exact zero of the literal P-gated, parity-projected Q/P cofactor term
outside true original alpha support at either physical endpoint. -/
theorem source_native_B534_projected_zero_outside_original_alpha434
    {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (z m t : ℕ)
    (hout : F.alpha m = 0 ∨ H.alpha t = 0) :
    sourceNativeB524GatedProjectedCofactorTerm434
      P R F H k a1 a2 psi z m t = 0 := by
  rcases hout with hf | hh
  · have hz := source_native_B491_QP_cofactor_alpha_zero434 P F z m hf
    unfold sourceNativeB524GatedProjectedCofactorTerm434
      sourceNativeB523GatedCoprimeTerm434
    simp [hz]
  · have hz := source_native_B491_QP_cofactor_alpha_zero434 P H
      (((z:ℤ)+2*k).toNat) t hh
    unfold sourceNativeB524GatedProjectedCofactorTerm434
      sourceNativeB523GatedCoprimeTerm434
    simp [hz]

/-- The COMPLETE original T physical P-gated four-sign projected Q/P
correlation on the actual position support Spos with arbitrary original
rough-alpha source and target is EXACTLY the coherent sum over truly
nonzero original alpha (z,m,t) triples. No D20 proxy or cofactor-count
normalization; both P-part selectors remain inside each complex term. -/
theorem source_native_B534_full_rough_P_gated_active_triples_exact434
    {ι : Type} [Fintype ι]
    (Spos : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (W : ℝ) (hrough : ∀ m, F.alpha m ≠ 0 → rough W m)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ Spos, z ≠ 0) :
    let S := sourceNativeB534OriginalRoughActiveTriples434 Spos P k F H
    sourceNativeB522GatedPhysicalProjected434 Spos P R F H k a1 a2 psi =
      ∑ s ∈ S,
        sourceNativeB524GatedProjectedCofactorTerm434
          P R F H k a1 a2 psi s.1 s.2.1 s.2.2 := by
  dsimp only
  let D : ℕ → Finset (ℕ×ℕ) := fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors
  let Sfull : Finset (Σ _ : ℕ, ℕ×ℕ) := Spos.sigma D
  let S : Finset (Σ _ : ℕ, ℕ×ℕ) := Sfull.filter
    (fun s => F.alpha s.2.1 ≠ 0 ∧ H.alpha s.2.2 ≠ 0)
  let B : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB524GatedProjectedCofactorTerm434
      P R F H k a1 a2 psi s.1 s.2.1 s.2.2
  have hBase := source_native_B532_rough_alpha_FULL_P_gated_projected_coprime434
    Spos P R F H W hrough k hk hsmall a1 a2 psi hS
  have hSigma : (∑ z ∈ Spos, ∑ v ∈ D z, B ⟨z,v⟩) =
      ∑ s ∈ Sfull, B s := (Finset.sum_sigma Spos D B).symm
  have hZero (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ Sfull)
      (hsnot : s ∉ S) : B s = 0 := by
    have hn : ¬(F.alpha s.2.1 ≠ 0 ∧ H.alpha s.2.2 ≠ 0) := by
      intro he
      exact hsnot (Finset.mem_filter.mpr ⟨hs,he⟩)
    have hout : F.alpha s.2.1 = 0 ∨ H.alpha s.2.2 = 0 := by
      by_cases h : F.alpha s.2.1 = 0
      · exact Or.inl h
      · exact Or.inr (by by_contra hh; exact hn ⟨h,hh⟩)
    exact source_native_B534_projected_zero_outside_original_alpha434
      P R F H k a1 a2 psi s.1 s.2.1 s.2.2 hout
  have hFilter : (∑ s ∈ S, B s) = ∑ s ∈ Sfull, B s :=
    Finset.sum_subset (Finset.filter_subset _ _) hZero
  change sourceNativeB522GatedPhysicalProjected434 Spos P R F H k a1 a2 psi =
    ∑ s ∈ S, B s
  calc
    _ = ∑ z ∈ Spos,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
        B ⟨z,(m,t)⟩ := hBase
    _ = ∑ z ∈ Spos, ∑ v ∈ D z, B ⟨z,v⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Finset.sum_product
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors
        (fun v : ℕ×ℕ => B ⟨z,v⟩)).symm
    _ = ∑ s ∈ Sfull, B s := hSigma
    _ = ∑ s ∈ S, B s := hFilter.symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualTOriginalAlphaGatedRatioRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The LITERAL original `sourceNativePrimeCore` alpha field is rough-
supported whenever the ORIGINAL cofactor set K consists of rough
integers. There is NO requirement that alpha be the centered D20 delta,
and nothing is asserted about alpha outside K. -/
theorem source_native_B535_actual_K_mask_preserves_rough434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (W : ℝ)
    (hK : ∀ m ∈ K, rough W m)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ∀ m, (sourceNativePrimeCore r d L b slot δ ξ K alpha
      q χ σ₀ σ₁).alpha m ≠ 0 → rough W m := by
  intro m hn
  change (if m ∈ K then alpha m else 0) ≠ 0 at hn
  by_cases hm : m ∈ K
  · exact hK m hm
  · simp only [if_neg hm] at hn
    exact False.elim (hn rfl)

/-- The original T source **and target** sorted-QSkip/factorial cores have
ARBITRARY original alphaF,alphaG and INDEPENDENT finite rough sets KF,KG.
At the TRUE physical integer shift 2k and finite tagged original z set,
with BOTH ORIGINAL P-part gates, Q/P residuals, marked weights, Mellin
phases and four signs, their complete post-square normalized character RMS
is EXACTLY the sum of coherent physical cofactor ratio-fiber squared
amplitudes. This is the first literal original-alpha production specialization
of B534: NO global D20-alpha replacement and NO hidden source-test
normalization, though it does not establish signed TypeII decay. -/
theorem source_native_B535_actual_original_alpha_K_gated_ratio_RMS434
    (g : ℕ) (P : Fin g → Finset ℕ) (Spos R : Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (alphaF alphaG : ℕ → ℂ) (W : ℝ)
    (hKF : ∀ m ∈ KF, rough W m)
    (hKG : ∀ t ∈ KG, rough W t)
    (σF0 σF1 σG0 σG1 : ℝ)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hS : ∀ z ∈ Spos, z ≠ 0) :
    let Fcore := sourceNativePrimeCore r d L b slot δF ξF KF
      alphaF 1 1 σF0 σF1
    let Gcore := sourceNativePrimeCore r d L b slot δG ξG KG
      alphaG 1 1 σG0 σG1
    let T := sourceNativeB532RoughActiveGatedTriples434 Spos P k Fcore Gcore
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB524GatedProjectedCofactorTerm434 P R Fcore Gcore
        k a1 a2 psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
          (sourceNativePrimeCore r d L b slot δF ξF KF
            alphaF k.natAbs χ σF0 σF1)
          (sourceNativePrimeCore r d L b slot δG ξG KG
            alphaG k.natAbs χ σG0 σG1)
          k a1 a2 psi‖^2) =
      ∑ v ∈ T.image ratio,
        ‖∑ s ∈ T.filter (fun s => ratio s = v), base s‖^2 := by
  dsimp only
  let Fcore := sourceNativePrimeCore r d L b slot δF ξF KF
    alphaF 1 1 σF0 σF1
  let Gcore := sourceNativePrimeCore r d L b slot δG ξG KG
    alphaG 1 1 σG0 σG1
  have hRoughF : ∀ m, Fcore.alpha m ≠ 0 → rough W m :=
    source_native_B535_actual_K_mask_preserves_rough434
      r d L b slot δF ξF KF alphaF W hKF 1 1 σF0 σF1
  have hRoughG : ∀ m, Gcore.alpha m ≠ 0 → rough W m :=
    source_native_B535_actual_K_mask_preserves_rough434
      r d L b slot δG ξG KG alphaG W hKG 1 1 σG0 σG1
  have hh := source_native_B534_full_original_rough_gated_ratio_RMS434
    g P Spos R Fcore Gcore W hRoughF hRoughG k hk hsmall
    a1 a2 psi hS
  change (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
          (sourceNativePrimeCore r d L b slot δF ξF KF
            alphaF k.natAbs χ σF0 σF1)
          (sourceNativePrimeCore r d L b slot δG ξG KG
            alphaG k.natAbs χ σG0 σG1)
          k a1 a2 psi‖^2) =
    ∑ v ∈ (sourceNativeB532RoughActiveGatedTriples434
      Spos P k Fcore Gcore).image
        (fun s => (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹),
      ‖∑ s ∈ (sourceNativeB532RoughActiveGatedTriples434
        Spos P k Fcore Gcore).filter
        (fun s => (s.2.2 : ZMod k.natAbs) *
          (s.2.1 : ZMod k.natAbs)⁻¹ = v),
          sourceNativeB524GatedProjectedCofactorTerm434 P R Fcore Gcore
            k a1 a2 psi s.1 s.2.1 s.2.2‖^2 at hh
  exact hh
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## GeneralRoughGatedRatioRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- FULL original T P-PART-GATED physically four-sign-projected Q/P
correlation on actual tagged positions Spos and arbitrary original source,
target cofactor fields alpha. Their nonzero supports satisfy the literal
original rough W hypothesis, NOT D20 full-cell proxy or sorted-QSkip K.
The exact normalized CHARACTER RMS after squaring equals the nonnegative
sum of coherent ratio-fiber norms. Every original P gate, prime slot,
residual, Mellin, source marked weight and physical shift 2k remains
inside each amplitude. No log saving or scalar transfer is claimed. -/
theorem source_native_B535_general_rough_P_gated_character_RMS_ratio_fibers434
    {ι : Type} [Fintype ι]
    (Spos : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (W : ℝ) (hF : ∀ m, F.alpha m ≠ 0 → rough W m)
    (hH : ∀ t, H.alpha t ≠ 0 → rough W t)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hPos : ∀ z ∈ Spos, z ≠ 0) :
    let F0 := sourceNativeWithoutCharacter434 F
    let H0 := sourceNativeWithoutCharacter434 H
    let S := sourceNativeB534OriginalRoughActiveTriples434 Spos P k F0 H0
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB524GatedProjectedCofactorTerm434 P R F0 H0
        k a1 a2 psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs)*(s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
          (sourceNativeWithCharacter434 F0 k.natAbs χ)
          (sourceNativeWithCharacter434 H0 k.natAbs χ)
          k a1 a2 psi‖^2) =
      ∑ t ∈ S.image ratio,
        ‖∑ s ∈ S.filter (fun s => ratio s = t), base s‖^2 := by
  dsimp only
  let F0 := sourceNativeWithoutCharacter434 F
  let H0 := sourceNativeWithoutCharacter434 H
  let S := sourceNativeB534OriginalRoughActiveTriples434 Spos P k F0 H0
  let base : (Σ _ : ℕ,ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB524GatedProjectedCofactorTerm434 P R F0 H0
      k a1 a2 psi s.1 s.2.1 s.2.2
  let ratio : (Σ _ : ℕ,ℕ×ℕ) → ZMod k.natAbs := fun s =>
    (s.2.2 : ZMod k.natAbs)*(s.2.1 : ZMod k.natAbs)⁻¹
  have hroughF0 : ∀ m, F0.alpha m ≠ 0 → rough W m := hF
  have hroughH0 : ∀ t, H0.alpha t ≠ 0 → rough W t := hH
  have hnk : k.natAbs ≤ (2*k).natAbs := by
    rw [Int.natAbs_mul]
    change k.natAbs ≤ 2*k.natAbs
    omega
  have hqW : ((k.natAbs:ℕ):ℝ) ≤ W :=
    (by exact_mod_cast hnk : ((k.natAbs:ℕ):ℝ) ≤ ((2*k).natAbs:ℝ)).trans hsmall
  have hUnit (s : Σ _ : ℕ,ℕ×ℕ) (hs : s ∈ S) :
      IsUnit (s.2.1 : ZMod k.natAbs) := by
    have ha := (Finset.mem_filter.mp hs).2.1
    exact source_native_B529_original_rough_cofactor_unit_mod434
      W s.2.1 k.natAbs (hroughF0 s.2.1 ha)
      (Int.natAbs_pos.mpr hk) hqW
  have hCross : ∀ s ∈ S, ∀ v ∈ S,
      IsUnit (((v.2.1*s.2.2:ℕ):ZMod k.natAbs)) := by
    intro s hs v hv
    have hmp := (Finset.mem_filter.mp hv).2.1
    have ht := (Finset.mem_filter.mp hs).2.2
    exact source_native_B529_original_rough_cross_unit_mod434
      W v.2.1 s.2.2 k.natAbs
      (hroughF0 v.2.1 hmp) (hroughH0 s.2.2 ht)
      (Int.natAbs_pos.mpr hk) hqW
  have hFactor (χ : DirichletCharacter ℂ k.natAbs)
      (s : Σ _ : ℕ,ℕ×ℕ) :
      sourceNativeB524GatedProjectedCofactorTerm434 P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 H0 k.natAbs χ)
        k a1 a2 psi s.1 s.2.1 s.2.2 =
      base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hh := source_native_B533_original_rough_P_gated_PROJECTED_factor434
      P R F0 H0 k.natAbs χ k a1 a2 psi s.1 s.2.1 s.2.2
    change _ = sourceNativeB496PhysicalPairCharacter434
      k.natAbs s.2.1 s.2.2 χ * base s at hh
    rw [hh]
    ring
  have hWhole (χ : DirichletCharacter ℂ k.natAbs) :
      sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 H0 k.natAbs χ)
        k a1 a2 psi =
      ∑ s ∈ S, base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hh := source_native_B534_full_rough_P_gated_active_triples_exact434
      Spos P R (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 H0 k.natAbs χ)
      W (by intro m hm; exact hroughF0 m hm)
      k hk hsmall a1 a2 psi hPos
    change sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativeWithCharacter434 F0 k.natAbs χ)
        (sourceNativeWithCharacter434 H0 k.natAbs χ)
        k a1 a2 psi =
      ∑ s ∈ S,
        sourceNativeB524GatedProjectedCofactorTerm434 P R
          (sourceNativeWithCharacter434 F0 k.natAbs χ)
          (sourceNativeWithCharacter434 H0 k.natAbs χ)
          k a1 a2 psi s.1 s.2.1 s.2.2 at hh
    calc
      _ = ∑ s ∈ S,
        sourceNativeB524GatedProjectedCofactorTerm434 P R
          (sourceNativeWithCharacter434 F0 k.natAbs χ)
          (sourceNativeWithCharacter434 H0 k.natAbs χ)
          k a1 a2 psi s.1 s.2.1 s.2.2 := hh
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hFactor χ s
  have hGram := source_native_B501_finite_physical_character_RMS_residue_only434
    S k.natAbs (Int.natAbs_pos.mpr hk)
    (fun s => s.2.1) (fun s => s.2.2) base hCross
  have hFibers := source_native_B506_finite_ratio_fiber_square_identity434
    S ratio base
  have hCong (s v : Σ _ : ℕ,ℕ×ℕ) (hs : s ∈ S) (hv : v ∈ S) :
      (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
       ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) ↔ ratio s = ratio v :=
    source_native_B505_original_QP_cross_residue_iff_ratio434
      k.natAbs s.2.1 s.2.2 v.2.1 v.2.2 (hUnit s hs) (hUnit v hv)
  calc
    _ = ∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖∑ s ∈ S,
          base s * sourceNativeB496PhysicalPairCharacter434
            k.natAbs s.2.1 s.2.2 χ‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hWhole χ]
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) then
        (star (base s)*base v).re else 0 := hGram
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if ratio s = ratio v then (star (base s)*base v).re else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      by_cases he : (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs))
      · have hr := (hCong s v hs hv).mp he
        simp only [if_pos he,if_pos hr]
      · have hr : ratio s ≠ ratio v :=
          fun h => he ((hCong s v hs hv).mpr h)
        simp only [if_neg he,if_neg hr]
    _ = ∑ t ∈ S.image ratio,
      ‖∑ s ∈ S.filter (fun s => ratio s = t), base s‖^2 := by
      simpa only using hFibers
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalRoughPGatedModTwoNoGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Every ORIGINAL T rough cofactor n for W≥2 is odd. This is true for
arbitrary nonzero alpha support, not merely source D20 proxy. -/
theorem source_native_B536_original_rough_odd434
    (W : ℝ) (hW : 2 ≤ W) (n : ℕ) (hn : rough W n) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · have h2 : 2 ∣ n := even_iff_two_dvd.mp he
    exact False.elim ((not_lt_of_ge hW) (hn.2 2 Nat.prime_two h2))
  · exact ho

/-- Original T rough cofactor carries the trivial character value for
q=2, with no modification of the exact Q/P residual and Mellin phases. -/
theorem source_native_B536_rough_character_mod2_one434
    (W : ℝ) (hW : 2 ≤ W) (n : ℕ) (hn : rough W n)
    (χ : DirichletCharacter ℂ 2) : χ (n : ZMod 2) = 1 := by
  obtain ⟨v,hv⟩ := source_native_B536_original_rough_odd434 W hW n hn
  have hmod : (n : ZMod 2) = 1 := by
    rw [hv]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp only [htwo,zero_mul,zero_add]
  rw [hmod]
  exact map_one χ

/-- For FULL ORIGINAL P-PART-GATED physically projected native T Q/P
cofactor amplitudes, modulo two all original rough-supported source AND
target alpha characters disappear independently. This holds even with
original K/source-P pair gating, all tagged positions, original marked
weights and BOTH endpoint signs retained before character averaging. -/
theorem source_native_B536_general_rough_P_gated_mod2_character_independence434
    {ι : Type} [Fintype ι]
    (Spos : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (W : ℝ) (hW : 2 ≤ W)
    (hF : ∀ m, F.alpha m ≠ 0 → rough W m)
    (hH : ∀ t, H.alpha t ≠ 0 → rough W t)
    (k : ℤ) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hPos : ∀ z ∈ Spos, z ≠ 0)
    (χ : DirichletCharacter ℂ 2) :
    let F0 := sourceNativeWithoutCharacter434 F
    let H0 := sourceNativeWithoutCharacter434 H
    sourceNativeB522GatedPhysicalProjected434 Spos P R
      (sourceNativeWithCharacter434 F0 2 χ)
      (sourceNativeWithCharacter434 H0 2 χ) k a1 a2 psi =
    sourceNativeB522GatedPhysicalProjected434 Spos P R F0 H0
      k a1 a2 psi := by
  dsimp only
  let F0 := sourceNativeWithoutCharacter434 F
  let H0 := sourceNativeWithoutCharacter434 H
  let S := sourceNativeB534OriginalRoughActiveTriples434 Spos P k F0 H0
  have hroughF0 : ∀ m, F0.alpha m ≠ 0 → rough W m := hF
  have hL := source_native_B534_full_rough_P_gated_active_triples_exact434
    Spos P R (sourceNativeWithCharacter434 F0 2 χ)
    (sourceNativeWithCharacter434 H0 2 χ) W
    (by intro m hm; exact hroughF0 m hm)
    k hk hsmall a1 a2 psi hPos
  have hR := source_native_B534_full_rough_P_gated_active_triples_exact434
    Spos P R F0 H0 W hroughF0 k hk hsmall a1 a2 psi hPos
  change sourceNativeB522GatedPhysicalProjected434 Spos P R
      (sourceNativeWithCharacter434 F0 2 χ)
      (sourceNativeWithCharacter434 H0 2 χ) k a1 a2 psi =
      ∑ s ∈ S,
        sourceNativeB524GatedProjectedCofactorTerm434 P R
          (sourceNativeWithCharacter434 F0 2 χ)
          (sourceNativeWithCharacter434 H0 2 χ) k a1 a2 psi
          s.1 s.2.1 s.2.2 at hL
  change sourceNativeB522GatedPhysicalProjected434 Spos P R F0 H0
      k a1 a2 psi =
      ∑ s ∈ S,
        sourceNativeB524GatedProjectedCofactorTerm434 P R F0 H0
          k a1 a2 psi s.1 s.2.1 s.2.2 at hR
  rw [hL,hR]
  apply Finset.sum_congr rfl
  intro s hs
  have hnonzero : F0.alpha s.2.1 ≠ 0 ∧ H0.alpha s.2.2 ≠ 0 :=
    (Finset.mem_filter.mp hs).2
  have hm := source_native_B536_rough_character_mod2_one434
    W hW s.2.1 (hF s.2.1 hnonzero.1) χ
  have ht := source_native_B536_rough_character_mod2_one434
    W hW s.2.2 (hH s.2.2 hnonzero.2) χ
  have hf := source_native_B533_original_rough_P_gated_PROJECTED_factor434
    P R F0 H0 2 χ k a1 a2 psi s.1 s.2.1 s.2.2
  change _ = sourceNativeB496PhysicalPairCharacter434 2 s.2.1 s.2.2 χ *
    sourceNativeB524GatedProjectedCofactorTerm434 P R F0 H0
      k a1 a2 psi s.1 s.2.1 s.2.2 at hf
  rw [hf]
  simp [sourceNativeB496PhysicalPairCharacter434,hm,ht]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## TrueOriginalQPTagPositive -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- EXACT original SourceNativeQPTagData state, including unrestricted
repeated P-prime powers, true OrderedQSkip choices and the two separate
cofactor/physical-prime coordinates. -/
abbrev SourceQPPhysicalTag {n : ℕ} (Q : Fin n → Finset ℕ) (δ : Fin n → Bool) :=
  (ℕ × (ℕ × OrderedQSkip n Q δ)) × ℕ

/-- LITERAL original T finite physical source-tag set: m, Q-prime,
QSkip factorial choices, actual repeated-P-part label v. -/
noncomputable def sourceQPPhysicalTagSet {n : ℕ}
    (Q : Fin n → Finset ℕ) (δ : Fin n → Bool) (K D R : Finset ℕ) :
    Finset (SourceQPPhysicalTag Q δ) :=
  (K ×ˢ (D ×ˢ (Finset.univ : Finset (OrderedQSkip n Q δ)))) ×ˢ R

/-- Original T tag cofactor m. -/
def sourceQPTagM {n : ℕ} {Q : Fin n → Finset ℕ} {δ : Fin n → Bool}
    (a : SourceQPPhysicalTag Q δ) : ℕ := a.1.1

/-- Original T tag positive physical h = D-prime * full QSkip product *
actual P-part v; no prime multiplicity is discarded. -/
noncomputable def sourceQPTagH {n : ℕ} {Q : Fin n → Finset ℕ} {δ : Fin n → Bool}
    (a : SourceQPPhysicalTag Q δ) : ℕ := (a.1.2.1 * orderedSkipProduct a.1.2.2) * a.2

/-- The EXACT original Q/P physical tagged positions `m*h` are positive
under the literal original source K/D/R/Q positivity contracts, with the
same dependent QSkip choices and no model replacement. This constructs
the `hS` gate required by the complete P-gated B535 ratio-fiber RMS. -/
theorem source_native_B536_true_original_QP_tagged_position_positive434
    {n : ℕ} (Q : Fin n → Finset ℕ) (δ : Fin n → Bool)
    (K D R : Finset ℕ)
    (hK : ∀ m ∈ K, 0 < m)
    (hD : ∀ p ∈ D, 0 < p)
    (hR : ∀ v ∈ R, 0 < v)
    (hQ : ∀ i p, p ∈ Q i → 0 < p) :
    ∀ a ∈ sourceQPPhysicalTagSet Q δ K D R,
      0 < sourceQPTagM a * sourceQPTagH a := by
  intro a ha
  obtain ⟨htag,hv⟩ := Finset.mem_product.mp ha
  obtain ⟨hm,hrest⟩ := Finset.mem_product.mp htag
  obtain ⟨hp,hskip⟩ := Finset.mem_product.mp hrest
  have hSkipPos : 0 < orderedSkipProduct a.1.2.2 := by
    unfold orderedSkipProduct
    apply Finset.prod_pos
    intro i hi
    exact hQ i.val (a.1.2.2 i).val (a.1.2.2 i).property
  change 0 < a.1.1 * ((a.1.2.1 * orderedSkipProduct a.1.2.2) * a.2)
  exact Nat.mul_pos (hK _ hm) (Nat.mul_pos (Nat.mul_pos (hD _ hp) hSkipPos) (hR _ hv))

/-- Literal original finite image of source T physical positions has
positive entries, even with repeated P powers, and is therefore legal as
the TRUE tagged z-domain of the fully gated physical correlation. -/
theorem source_native_B536_true_tagged_image_nonzero434
    {n : ℕ} (Q : Fin n → Finset ℕ) (δ : Fin n → Bool)
    (K D R : Finset ℕ)
    (hK : ∀ m ∈ K, 0 < m)
    (hD : ∀ p ∈ D, 0 < p)
    (hR : ∀ v ∈ R, 0 < v)
    (hQ : ∀ i p, p ∈ Q i → 0 < p) :
    ∀ z ∈ (sourceQPPhysicalTagSet Q δ K D R).image
      (fun a => sourceQPTagM a * sourceQPTagH a), z ≠ 0 := by
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  exact Nat.ne_of_gt
    (source_native_B536_true_original_QP_tagged_position_positive434
      Q δ K D R hK hD hR hQ a ha)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## GeneralRoughPGatedModTwoRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- At TRUE physical modulus |k|=2, normalized character RMS of the
FULL ORIGINAL T P-PART-GATED four-sign-projected Q/P correlation for
arbitrary rough-supported alpha is EXACTLY the coherent character-free
physical square. ALL original P gates, tagged positions, two Mellin
parameters and residual/source marked weights survive unchanged. Not
only does character averaging not prove saving: it is an IDENTITY with
no gain whatever in the actual original rough sector. -/
theorem source_native_B537_original_rough_FULL_P_gated_mod2_RMS_no_gain434
    {ι : Type} [Fintype ι]
    (Spos : Finset ℕ) (P : ι → Finset ℕ) (R : Finset ℕ)
    (F H : PrimeSlotCore)
    (W : ℝ) (hW : 2 ≤ W)
    (hF : ∀ m, F.alpha m ≠ 0 → rough W m)
    (hH : ∀ t, H.alpha t ≠ 0 → rough W t)
    (k : ℤ) (hk : k ≠ 0) (hk2 : k.natAbs = 2)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (a1 a2 : ℝ) (psi : ℕ → ℂ)
    (hPos : ∀ z ∈ Spos, z ≠ 0) :
    let F0 := sourceNativeWithoutCharacter434 F
    let H0 := sourceNativeWithoutCharacter434 H
    let x0 := sourceNativeB522GatedPhysicalProjected434 Spos P R F0 H0
      k a1 a2 psi
    (∑ χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖ *
      ‖sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativeWithCharacter434 F0 2 χ)
        (sourceNativeWithCharacter434 H0 2 χ) k a1 a2 psi‖^2) = ‖x0‖^2 := by
  dsimp only
  let F0 := sourceNativeWithoutCharacter434 F
  let H0 := sourceNativeWithoutCharacter434 H
  let x0 := sourceNativeB522GatedPhysicalProjected434 Spos P R F0 H0
    k a1 a2 psi
  have hIndep (χ : DirichletCharacter ℂ 2) :
      sourceNativeB522GatedPhysicalProjected434 Spos P R
        (sourceNativeWithCharacter434 F0 2 χ)
        (sourceNativeWithCharacter434 H0 2 χ) k a1 a2 psi = x0 := by
    exact source_native_B536_general_rough_P_gated_mod2_character_independence434
      Spos P R F H W hW hF hH k hk hsmall a1 a2 psi hPos χ
  have hMass : (∑ _χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖) = 1 := by
    have hh := source_original_B430_character_probability_mass434 (2:ℤ) (by norm_num)
    norm_num at hh ⊢
    exact_mod_cast hh
  calc
    _ = ∑ χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖ * ‖x0‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hIndep χ]
    _ = (∑ _χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖) * ‖x0‖^2 := by
      rw [Finset.sum_mul]
    _ = ‖x0‖^2 := by rw [hMass,one_mul]
end Green64Analytic.ShiftTwoTerminal

end

end

