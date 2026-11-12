module

public import Green64.Library.Correlation.Part039
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part046
public import Green64.Library.Correlation.Part037
public import Green64.Library.Weights.Part047
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part043
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part042
public import Green64.Library.Correlation.Part034
public import Green64.Library.Analysis.Estimates.Part010

@[expose] public section

/-!
# Correlation / Part040

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalProbeFullKnuRational -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- SOURCE03 pattern ν with its ACTUAL two different finite prime
sets, harmonic weights, and canonically chosen ACTIVE log-product
cells. This theorem discharges all external probability law and
retained cell mass assumptions from C118; these follow from
hV_g=sum_{p in P_g} 1/p, V_g>0 and the actual source03 active cells.
Only TRUE analytic BIG group band geometry and Vmin remain explicit.
No artificial independent prime law or arbitrary cell masses. -/
theorem source_original_probe_full_Knu_rational_comparison434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (hVp : ∀ g, 0 < V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hAllVmin : ∀ g, Vmin ≤ V g)
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (pA : SourceOriginalGramPrimeTuple434
          (fun z : ν.1 => P z.val.1))
      (pB : SourceOriginalGramPrimeTuple434
          (fun z : ν.2 => P z.val.1))
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.1 => P z.val.1) pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.2 => P z.val.1) pB))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let eps : ℝ := (K/Vmin)*L^(-B)
      let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
      let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
      let α : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434
          Q JA JB hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (sourceOriginalGramPrimeProduct434 SA q.1)
          (sourceOriginalGramPrimeProduct434 SA pA)
          (sourceOriginalGramPrimeProduct434 SB q.2)
          (sourceOriginalGramPrimeProduct434 SB pB)
          (ν.1.card+ν.2.card) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
          (sourceOriginalGramPrimeProduct434 SA q.1 *
           sourceOriginalGramPrimeProduct434 SB q.2)) -
        α * sourceOriginalPositiveRationalPhaseAtNat434 r hr u
          (sourceOriginalGramPrimeProduct434 SA pA *
           sourceOriginalGramPrimeProduct434 SB pB)‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) := by
  obtain ⟨K,Y,hK,hEstimate⟩ :=
    source_original_probe_rational_comparison_instantiated434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instDec m ν P V hV hVp Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi iA iB uA vA uB vB
    huA huB huvA huvB hvA hvB huLargeA huLargeB
    huBIGA huBIGB hYA hYB Vmin hVmin hAllVmin
    hBandA hBandB pA pB hCellA hCellB r hr hrQ u
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let eps : ℝ := (K/Vmin)*L^(-B)
  let α : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let wA := sourceOriginalGramPrimeMass434 SA muA
  let wB := sourceOriginalGramPrimeMass434 SB muB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q {jA} hA
      (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalGramPrimeProduct434 SA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q {jB} hB
      (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalGramPrimeProduct434 SB p)
  let phase : XA × XB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2)
  have hMA : sourceOriginalProbeCellA434 m P V ν hA =
      sourceOriginalRealGramCellMass434 SA muA hA := by
    funext j
    exact source_original_probe_A_cell_probability_gram434
      m ν P V hA j
  have hMB : sourceOriginalProbeCellB434 m P V ν hB =
      sourceOriginalRealGramCellMass434 SB muB hB := by
    funext j
    exact source_original_probe_B_cell_probability_gram434
      m ν P V hB j
  have hKernel (q : XA × XB) :
      sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB
        (sourceOriginalProbeCellA434 m P V ν hA)
        (sourceOriginalProbeCellB434 m P V ν hB)
        (sourceOriginalGramPrimeProduct434 SA q.1)
        (sourceOriginalGramPrimeProduct434 SA pA)
        (sourceOriginalGramPrimeProduct434 SB q.2)
        (sourceOriginalGramPrimeProduct434 SB pB)
        (ν.1.card+ν.2.card) =
          α * (KA q.1 pA * KB q.2 pB) := by
    unfold sourceOriginalActualPrimitiveComparisonKernel434
    rw [hMA,hMB,
      source_original_actual_active_kernel_collapse434
        Q JA hA hhA
        (sourceOriginalRealGramCellMass434 SA muA hA)
        jA hjA (sourceOriginalGramPrimeProduct434 SA q.1)
        (sourceOriginalGramPrimeProduct434 SA pA) hCellA,
      source_original_actual_active_kernel_collapse434
        Q JB hB hhB
        (sourceOriginalRealGramCellMass434 SB muB hB)
        jB hjB (sourceOriginalGramPrimeProduct434 SB q.2)
        (sourceOriginalGramPrimeProduct434 SB pB) hCellB]
    simp only [α,KA,KB,mul_assoc]
  have hRaw := hEstimate
    m ν P V hV hVp Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi iA iB
    uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin hAllVmin hBandA hBandB
    pA pB hCellA hCellB r hr hrQ u
  have hOrig :
      ‖(∑ q : XA × XB,
        ((wA q.1:ℂ)*(wB q.2:ℂ)) *
          (KA q.1 pA*KB q.2 pB)*phase q) -
        phase (pA,pB)‖ ≤
         (eps+eps+eps*eps)*(r:ℝ) := by
    simpa only [SA,SB,muA,muB,eps,XA,XB,wA,wB,
      KA,KB,phase] using hRaw
  have hSignNorm : ‖α‖ = 1 := by
    simp [α]
  have hSum :
      (∑ q : XA × XB,
        ((wA q.1:ℂ)*(wB q.2:ℂ)) *
          (α*(KA q.1 pA*KB q.2 pB))*phase q) =
      α*(∑ q : XA × XB,
        ((wA q.1:ℂ)*(wB q.2:ℂ)) *
          (KA q.1 pA*KB q.2 pB)*phase q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hSigned :
      ‖(∑ q : XA × XB,
        ((wA q.1:ℂ)*(wB q.2:ℂ)) *
          (α*(KA q.1 pA*KB q.2 pB))*phase q) -
        α*phase (pA,pB)‖ ≤
         (eps+eps+eps*eps)*(r:ℝ) := by
    rw [hSum,← mul_sub,norm_mul,hSignNorm,one_mul]
    exact hOrig
  change ‖(∑ q : XA × XB,
        ((wA q.1:ℂ)*(wB q.2:ℂ)) *
          (sourceOriginalActualPrimitiveComparisonKernel434
            Q JA JB hA hB
            (sourceOriginalProbeCellA434 m P V ν hA)
            (sourceOriginalProbeCellB434 m P V ν hB)
            (sourceOriginalGramPrimeProduct434 SA q.1)
            (sourceOriginalGramPrimeProduct434 SA pA)
            (sourceOriginalGramPrimeProduct434 SB q.2)
            (sourceOriginalGramPrimeProduct434 SB pB)
            (ν.1.card+ν.2.card))*phase q) -
        α*phase (pA,pB)‖ ≤
         (eps+eps+eps*eps)*(r:ℝ)
  convert hSigned using 1
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [hKernel q]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeSignedRationalError -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT SOURCE03 original ν-dependent SIGNED major-rational
comparison-error FUNCTION on the true physical unshared
source/target endpoint arrays. Unlike a hypothetical local
error kernel, this is the literal expectation over independently
labelled auxiliary A/B prime slots of the ORIGINAL full-active
primitive comparison Kν, with true harmonic probabilities and
the original -(-1)^card sign. It is defined even on discarded
physical output cells, which will be explicitly masked in
the L2 comparison. No probability or analytic bound is
postulated by this definition. -/
noncomputable def sourceOriginalProbeSignedRationalError434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
           SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2)) -
  σ * sourceOriginalPositiveRationalPhaseAtNat434 r hr u (XA*XB)

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDroppedRationalError -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- On ANY original SOURCE03 ν-pattern physical endpoint with
a discarded TARGET A GLOBAL cell or SOURCE B GLOBAL cell,
the WHOLE original comparison Knu auxiliary expectation is
exactly ZERO, not merely bounded by Q^4/xi². Its signed
major-RATIONAL residual is precisely MINUS the original
unit-modulus signed rational phase, with the exact source03
minus(-1)^card factor and genuine integer products X_A,X_B.
No prime independence, Siegel-Walfisz or artificial smallness
hypothesis is used in this support identity. -/
theorem source_original_probe_signed_rational_error_eq_discarded434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi) :
    sourceOriginalProbeSignedRationalError434
      J ell m hmJ ν P V Q hA hB xi r hr u source target =
    -((-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      sourceOriginalPositiveRationalPhaseAtNat434 r hr u
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
         sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)) := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let ma := sourceOriginalProbeCellA434 m P V ν hA
  let mb := sourceOriginalProbeCellB434 m P V ν hB
  let sig : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℂ :=
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u (XA*XB)
  have hK0
      (ab : SourceOriginalGramPrimeTuple434 SA ×
            SourceOriginalGramPrimeTuple434 SB) :
      sourceOriginalActualPrimitiveComparisonKernel434 Q
        JA JB hA hB ma mb
        (sourceOriginalGramPrimeProduct434 SA ab.1) XA
        (sourceOriginalGramPrimeProduct434 SB ab.2) XB
        (ν.1.card+ν.2.card) = 0 := by
    exact source_original_actual_primitive_comparison_zero_discarded434
      Q JA JB hA hB hhA hhB ma mb
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) hDrop
  have hS : (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
       SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB ma mb
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro ab hab
    rw [hK0 ab]
    ring
  unfold sourceOriginalProbeSignedRationalError434
  change (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
       SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB ma mb
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2)) -
      sig*phase = -(sig*phase)
  rw [hS,zero_sub]

/-- The exact original SOURCE03 signed major-rational error has
UNIT modulus outside either of its true active GLOBAL cells.
This permits a sharp rare-event L² estimate on the FULL
physical variables; applying a Q-dependent uniform kernel
upper bound there would be spurious and much weaker. -/
theorem source_original_probe_signed_rational_error_norm_discarded434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi) :
    ‖sourceOriginalProbeSignedRationalError434
      J ell m hmJ ν P V Q hA hB xi r hr u source target‖ = 1 := by
  rw [source_original_probe_signed_rational_error_eq_discarded434
    J ell m hmJ ν P V Q hA hB xi hhA hhB
    r hr u source target hDrop, norm_neg, norm_mul]
  have hsig : ‖-((-1:ℂ)^(ν.1.card+ν.2.card))‖ = 1 := by simp
  rw [hsig, one_mul]
  exact source_original_positive_rational_phase_norm_one434
    r hr u
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
     sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03BigNuBoundedEnergy -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The ORIGINAL SOURCE03 manuscript defines its BIG group
harmonic normalizer by V_g=sum_{p∈Tb_g}1/p.
Under this honest arithmetic source-admissibility equality,
the actual ν-selected independent prime-label probability
measure is exactly normalized (total mass ONE), and the
weighted L² energy of EVERY complex test bounded by one
is <=1. No f=f(product) assumption and no unproved L²
amplitude saving. The pre-existing SourceComparisonData434
record omits V_g=sum; it is therefore explicitly supplied
as a genuine SOURCE assumption, not claimed to follow
from V_g>=vmin alone. -/
theorem source_original_source03_big_nu_bounded_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hVbig : ∀ g : β, d.Vbig g =
      ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (m : ℕ) (A : Finset (β × Fin m))
    (f : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (hf : ∀ v, ‖f v‖ ≤ 1) :
    (∑ v : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1),
      sourceOriginalGramPrimeMass434
        (fun z : A => d.Tb z.val.1)
        (fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)) v*
        ‖f v‖^2) ≤ 1 := by
  classical
  let S : A → Finset ℕ := fun z => d.Tb z.val.1
  let mu : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  have hVpos (z : A) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hAtom (z : A) (p : ℕ) (hp : p ∈ S z) :
      0 ≤ mu z p := by
    dsimp [mu]
    have hPrime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by
      exact_mod_cast hPrime.pos
    exact div_nonneg (div_nonneg zero_le_one hpp.le)
      (hVpos z).le
  have hTot (z : A) :
      (∑ p ∈ S z, mu z p) = 1 := by
    have hh := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) (hVpos z).ne'
    calc
      _ = ∑ p ∈ S z,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [mu,sourcePrimeSharedAtom434,
            one_div,div_eq_mul_inv,mul_inv_rev]
          ring
      _ = 1 := hh
  have hMass (v : SourceOriginalGramPrimeTuple434 S) :
      0 ≤ sourceOriginalGramPrimeMass434 S mu v :=
    source_original_physical_gram_prime_mass_nonneg434
      S mu hAtom v
  have hSumOne : (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v) = 1 :=
    source_original_physical_gram_prime_mass_total434
      S mu hTot
  have hF (v : SourceOriginalGramPrimeTuple434 S) :
      ‖f v‖^2 ≤ 1 := by
    have h := hf v
    have h0 := norm_nonneg (f v)
    nlinarith
  calc
    (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v * ‖f v‖^2) ≤
      ∑ v : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu v * 1 := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (hF v) (hMass v)
    _ = 1 := by simpa only [mul_one] using hSumOne
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03NuMinorMultiplier -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The ACTUAL SOURCE03 two BIG-block integer minor Fourier
multiplier on all chosen ν-pattern prime positions has squared
modulus <= 125 L^-Bsave for every pair of unit-bounded complex
mark tests, under the exact original manuscript harmonic
normalization V_g=sum_{p∈P_g}1/p. No equality of the old formal
Vbig field to that sum is invented: it is a visible additional
source admissibility premise. True source disjoint group
separation, original C6 Diophantine and dyadic scale conditions
remain explicit, as must the saving exponent budget.
No assertion about final RAW/Hoeffding residual. -/
theorem source_original_source03_true_nu_big_bounded_minor_multiplier434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (hfA : ∀ v, ‖fA v‖ ≤ 1)
    (hfB : ∀ v, ‖fB v‖ ≤ 1)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ vA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
        (∑ vB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (((a:ℝ)/(r:ℝ)+beta0)*
                  ((sourceOriginalGramPrimeProduct434 SB vB:ℕ):ℝ))
                ((sourceOriginalGramPrimeProduct434 SA vA:ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤
       125*L^(-Bsave) := by
  have hMinor :=
    source_original_source03_true_nu_two_big_physical_minor_L2_log_power434
      cfg x L Y Hprime d sep blockA blockB hDisjoint
      m hm A B hPattern fA fB M N P Q hM hN
      a r beta0 hr hcop hbeta hP hQ
      D Bsave hL hR hNlarge hMlarge hMNlarge
      C hExponent hSaving
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v * ‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v * ‖fB v‖^2
  have hEA : EA ≤ 1 := by
    exact source_original_source03_big_nu_bounded_energy434
      cfg x L Y Hprime d hVbig m A fA hfA
  have hEB : EB ≤ 1 := by
    exact source_original_source03_big_nu_bounded_energy434
      cfg x L Y Hprime d hVbig m B fB hfB
  have hPosA (z : A) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hPosB (z : B) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hAtomA (z : A) (p : ℕ) (hp : p ∈ SA z) :
      0 ≤ muA z p := by
    dsimp [muA]
    have hprime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by
      exact_mod_cast hprime.pos
    exact div_nonneg (div_nonneg zero_le_one hpp.le)
      (hPosA z).le
  have hAtomB (z : B) (p : ℕ) (hp : p ∈ SB z) :
      0 ≤ muB z p := by
    dsimp [muB]
    have hprime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by
      exact_mod_cast hprime.pos
    exact div_nonneg (div_nonneg zero_le_one hpp.le)
      (hPosB z).le
  have hEA0 : 0 ≤ EA := by
    dsimp [EA]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (source_original_physical_gram_prime_mass_nonneg434
        SA muA hAtomA v)
      (sq_nonneg _)
  have hEB0 : 0 ≤ EB := by
    dsimp [EB]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (source_original_physical_gram_prime_mass_nonneg434
        SB muB hAtomB v)
      (sq_nonneg _)
  have hBoundEnergy : EA*EB ≤ 1 := by
    calc
      EA*EB ≤ 1*EB :=
        mul_le_mul_of_nonneg_right hEA hEB0
      _ ≤ 1*1 :=
        mul_le_mul_of_nonneg_left hEB (by norm_num)
      _ = 1 := by ring
  have hLpow : 0 ≤ L^(-Bsave) :=
    Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hUniform :
      125*(EA*EB)*L^(-Bsave) ≤
      125*L^(-Bsave) := by
    have hh :=
      mul_le_mul_of_nonneg_right hBoundEnergy hLpow
    nlinarith
  dsimp only at hMinor
  dsimp only
  exact hMinor.trans hUniform
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuSignedKnuWeightedL2Minor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- A WEIGHTED-L2 original source03 signed Knu *minor* physical
bilinear estimate, not an asserted cancellation hypothesis.
The original two independent BIG marked groups, real ν
pattern, all-conductor primitive character family, real
global log-cell amplitudes, physical integer dyad windows,
original -(-1)^(cardA+cardB) and additive Fourier frequency
-k*theta are all preserved. The actual group separation, active-cell lower masses, and the
three TRUE C6 spectral scale bounds are explicit hypotheses.
Unlike the earlier signed minor theorem, arbitrary selected
complex prime-tuple tests are allowed in true weighted L2; no polynomial upper
cap is imposed on the Dirichlet denominator. The proof
will invoke the independently kernel-checked C281 true
ν-character-mode C6 inequality, C280 exact signed
physical expansion, C284 actual mode coefficient L1 budget
and C285 quantitative mode sum. No raw/Hoeffding
transference is claimed. -/
theorem source_original_source03_true_nu_signed_Knu_weighted_L2_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (bA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (bB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := sourceOriginalGramPrimeProduct434 SA vA
    let XB : ℕ := sourceOriginalGramPrimeProduct434 SB vB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖bA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖bB v‖^2
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then bA v else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then bB v else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*(EA*EB)*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    bA bB vA vB
    M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  dsimp
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖bA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖bB v‖^2
  let pa : SourceOriginalGramPrimeTuple434 SA → ℕ :=
    sourceOriginalGramPrimeProduct434 SA
  let pb : SourceOriginalGramPrimeTuple434 SB → ℕ :=
    sourceOriginalGramPrimeProduct434 SB
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  let XA : ℕ := pa vA
  let XB : ℕ := pb vB
  let phase : ℕ → ℕ → ℂ :=
    fun n mm => Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (((n*mm:ℕ):ℤ))
  let chars := sourceOriginalActualPrimitiveCharacters434 Qchar
  let IA := JA.product chars
  let IB := JB.product chars
  let outA : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i => sourceOriginalPrimitiveOutputCellCoefficient434
      Qchar hA massA i.1 i.2 XA
  let outB : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun j => sourceOriginalPrimitiveOutputCellCoefficient434
      Qchar hB massB j.1 j.2 XB
  let modeA : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun i v => sourceOriginalPrimitiveInputCellMode434
      Qchar hA i.1 i.2 (pa v)
  let modeB : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun j v => sourceOriginalPrimitiveInputCellMode434
      Qchar hB j.1 j.2 (pb v)
  let bAW : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => if pa v ∈ AW then bA v else 0
  let bBW : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => if pb v ∈ BW then bB v else 0
  let H : SourceOriginalGramPrimeTuple434 SA ×
          SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => phase (pa v.1) (pb v.2)
  let coef :
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) →
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i j => -((-1:ℂ)^(A.card+B.card)) * outA i*outB j
  let mmode :
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) →
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i j => sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => bAW v*modeA i v)
      (fun v => bBW v*modeB j v)
      H
  let cost : ℝ := (Qchar:ℝ)^4*(xi⁻¹)^4
  let saving : ℝ := 125*(EA*EB)*L^(-Bsave)
  have hVposA (z : A) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hVposB (z : B) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hmuA (z : A) (p : ℕ) (hp : p ∈ SA z) :
      0 ≤ muA z p := by
    have hPrime : p.Prime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by exact_mod_cast hPrime.pos
    dsimp [muA]
    exact div_nonneg (div_nonneg zero_le_one hpp.le) (hVposA z).le
  have hmuB (z : B) (p : ℕ) (hp : p ∈ SB z) :
      0 ≤ muB z p := by
    have hPrime : p.Prime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by exact_mod_cast hPrime.pos
    dsimp [muB]
    exact div_nonneg (div_nonneg zero_le_one hpp.le) (hVposB z).le
  have hEA0 : 0 ≤ EA := by
    dsimp [EA]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (source_original_physical_gram_prime_mass_nonneg434
        SA muA hmuA v) (sq_nonneg _)
  have hEB0 : 0 ≤ EB := by
    dsimp [EB]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (source_original_physical_gram_prime_mass_nonneg434
        SB muB hmuB v) (sq_nonneg _)
  have hSavingPos : 0 ≤ saving := by
    dsimp only [saving]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg hEA0 hEB0))
      (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _)
  have hCostPos : 0 ≤ cost := by dsimp [cost]; positivity
  have hCoeffBudget :
      (∑ i ∈ IA, ∑ j ∈ IB, ‖coef i j‖) ≤ cost := by
    have hh := source_original_signed_minor_endpoint_l1_cost434
      Qchar (A.card+B.card) JA JB hA hB
      massA massB xi hxi hMassA hMassB hTotalA hTotalB
      XA XB
    simpa only [IA,IB,chars,outA,outB,coef,cost]
      using hh
  have hModeBudget (i : ℤ × (Σ q : Fin Qchar,
       DirichletCharacter ℂ (q.val+1)))
      (hi : i ∈ IA)
      (j : ℤ × (Σ q : Fin Qchar,
       DirichletCharacter ℂ (q.val+1)))
      (hj : j ∈ IB) :
      ‖mmode i j‖^2 ≤ saving := by
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => bA v*modeA i v
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => bB v*modeB j v
    have hFub :=
      source_original_physical_masked_mode_minor_fubini434
        wA wB pa pb bA (modeA i) bB (modeB j)
        AW BW phase
    have hC6 :=
      source_original_true_nu_weighted_primitive_mode_minor434
        cfg x L Y Hprime d sep
        blockA blockB hDisjoint m hm (A,B) hPattern
        Qchar i.2 j.2 hA hB i.1 j.1 bA bB
        M N P Q hM hN a r beta0 theta k hApprox
        hr hcop hbeta hP hQ D Bsave hL hR
        hNlarge hMlarge hMNlarge C hExponent hSaving
    dsimp only at hC6
    change ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => (if pa v ∈ AW then bA v else 0)*modeA i v)
      (fun v => (if pb v ∈ BW then bB v else 0)*modeB j v)
      (fun v => phase (pa v.1) (pb v.2))‖^2 ≤ saving
    rw [hFub]
    simpa only [fA,fB,SA,SB,muA,muB,
      modeA,modeB,pa,pb,AW,BW,phase,saving,EA,EB]
      using hC6
  have hOverall :=
    source_original_finite_two_global_minor_mode_square434
      IA IB coef mmode saving cost
      hSavingPos hCostPos hModeBudget hCoeffBudget
  have hFactor :=
    source_original_physical_signed_minor_Knu_mode_expansion434
      SA muA SB muB bA bB AW BW
      Qchar JA JB hA hB massA massB XA XB
      (A.card+B.card) phase
  dsimp only at hFactor
  change
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB bAW bBW
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (pa v.1) XA (pb v.2) XB (A.card+B.card) *
        phase (pa v.1) (pb v.2))‖^2 ≤
      cost^2*saving
  rw [hFactor]
  exact hOverall
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuKnuDyadUnitInputMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The TRUE SOURCE03 signed primitive Knu Fourier minor is
pointwise small for EACH original output labelled-prime tuple
(vA,vB), when independently sampled auxiliary D_A,D_B prime
products are restricted to genuine two input-product dyads.
Input tests are the constant 1; normalized ORIGINAL harmonic
tuple masses reduce the arbitrary weighted-L2 C6 theorem
to an output-UNIFORM spectral estimate.
No fake primitive pointwise saving or output cardinality loss,
no artificial common major-arc radius. This is ONE input
window only: all-dyad Knu still requires globalization. -/
theorem source_original_true_nu_Knu_dyad_unit_input_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := sourceOriginalGramPrimeProduct434 SA vA
    let XB : ℕ := sourceOriginalGramPrimeProduct434 SB vB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    vA vB M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  have hNormA (z : A) : ∑ p ∈ SA z, muA z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hNormB (z : B) : ∑ p ∈ SB z, muB z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hTupleTotalA := source_original_physical_gram_prime_mass_total434
    SA muA hNormA
  have hTupleTotalB := source_original_physical_gram_prime_mass_total434
    SB muB hNormB
  have hKnu := source_original_source03_true_nu_signed_Knu_weighted_L2_minor434
    cfg D Bsave hD C hExponent hSaving
    L hL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    (fun _ => (1:ℂ)) (fun _ => (1:ℂ))
    vA vB M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hNlarge hMlarge hMNlarge
  dsimp only at hKnu
  have hAenergy :
      (∑ v : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA v * ‖(1:ℂ)‖^2) = 1 := by
    simpa only [norm_one,one_pow,mul_one] using hTupleTotalA
  have hBenergy :
      (∑ v : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB v * ‖(1:ℂ)‖^2) = 1 := by
    simpa only [norm_one,one_pow,mul_one] using hTupleTotalB
  rw [hAenergy,hBenergy] at hKnu
  simpa only [one_mul,mul_one,mul_assoc] using hKnu
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuSignedKnuMellinWeightedMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- The ACTUAL signed original SOURCE03 Knu physical weighted-L2
C6 minor bound with arbitrary real Mellin twist ζ, identical
log saving and all genuine primitive χA/χB cell kernels.
The Mellin multiplier factors EXACTLY across independent
prime products D_A,D_B and preserves both original weighted
L2 test energies. True dyad masks, -k theta, harmonic
measures, original ν sign, and full C6 large denominator
hypotheses remain unchanged. This alone does not establish
the full physical RAW-minus-Knu correlation or its major arcs. -/
theorem source_original_source03_true_nu_signed_Knu_mellin_weighted_L2_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (ζ : ℝ)
    (bA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (bB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := sourceOriginalGramPrimeProduct434 SA vA
    let XB : ℕ := sourceOriginalGramPrimeProduct434 SB vB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖bA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖bB v‖^2
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then bA v else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then bB v else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
        sourceOriginalPureMellinPhase434 ζ
          (sourceOriginalGramPrimeProduct434 SA v.1 *
           sourceOriginalGramPrimeProduct434 SB v.2))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*(EA*EB)*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    ζ bA bB vA vB
    M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun i => N+i)
  let XA : ℕ := pa vA
  let XB : ℕ := pb vB
  let EA : ℝ := ∑ a : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA a*‖bA a‖^2
  let EB : ℝ := ∑ b : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB b*‖bB b‖^2
  let bAz : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => bA a*sourceOriginalPureMellinPhase434 ζ (pa a)
  let bBz : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => bB b*sourceOriginalPureMellinPhase434 ζ (pb b)
  let K : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun ab =>
    sourceOriginalActualPrimitiveComparisonKernel434
      Qchar JA JB hA hB massA massB
      (pa ab.1) XA (pb ab.2) XB (A.card+B.card) *
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((pa ab.1*pb ab.2:ℕ):ℤ))
  have hPA (a : SourceOriginalGramPrimeTuple434 SA) :
      0 < pa a := by
    unfold pa sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (d.hTbPrime z.val.1 (a z).val (a z).property).pos
  have hPB (b : SourceOriginalGramPrimeTuple434 SB) :
      0 < pb b := by
    unfold pb sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (d.hTbPrime z.val.1 (b z).val (b z).property).pos
  have hEnergy :=
    source_original_true_nu_mellin_two_energy_eq434
      m (A,B) d.Tb
      (fun a : SourceOriginalGramPrimeTuple434 SA =>
        sourceOriginalGramPrimeMass434 SA muA a)
      (fun b : SourceOriginalGramPrimeTuple434 SB =>
        sourceOriginalGramPrimeMass434 SB muB b)
      ζ bA bB
  have hEA :
      (∑ a : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA a*‖bAz a‖^2) = EA :=
    hEnergy.1
  have hEB :
      (∑ b : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB b*‖bBz b‖^2) = EB :=
    hEnergy.2
  have hMaskA (a : SourceOriginalGramPrimeTuple434 SA) :
      (if pa a ∈ AW then bAz a else 0) =
      (if pa a ∈ AW then bA a else 0) *
        sourceOriginalPureMellinPhase434 ζ (pa a) := by
    by_cases h : pa a ∈ AW
    · simp only [if_pos h,bAz]
    · simp only [if_neg h,zero_mul]
  have hMaskB (b : SourceOriginalGramPrimeTuple434 SB) :
      (if pb b ∈ BW then bBz b else 0) =
      (if pb b ∈ BW then bB b else 0) *
        sourceOriginalPureMellinPhase434 ζ (pb b) := by
    by_cases h : pb b ∈ BW
    · simp only [if_pos h,bBz]
    · simp only [if_neg h,zero_mul]
  have hTransport := source_original_finite_mellin_bilinear_transfer434
    wA wB
    (fun a => if pa a ∈ AW then bA a else 0)
    (fun b => if pb b ∈ BW then bB b else 0)
    pa pb hPA hPB K ζ
  have hIdentity :
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if pa a ∈ AW then bAz a else 0)
      (fun b => if pb b ∈ BW then bBz b else 0)
      K =
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if pa a ∈ AW then bA a else 0)
      (fun b => if pb b ∈ BW then bB b else 0)
      (fun q => K q *
        sourceOriginalPureMellinPhase434 ζ (pa q.1*pb q.2)) := by
    calc
      _ = sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
        (fun a => (if pa a ∈ AW then bA a else 0) *
          sourceOriginalPureMellinPhase434 ζ (pa a))
        (fun b => (if pb b ∈ BW then bB b else 0) *
          sourceOriginalPureMellinPhase434 ζ (pb b))
        K := by
          apply congrArg₂
            (fun f g => sourceOriginalFiniteTwoSidedMinorBilinear434
              wA wB f g K)
          · funext a; exact hMaskA a
          · funext b; exact hMaskB b
      _ = _ := hTransport
  have hBase := source_original_source03_true_nu_signed_Knu_weighted_L2_minor434
    cfg D Bsave hD C hExponent hSaving
    L hL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern Qchar
    JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    bAz bBz vA vB M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta hP hQ
    hR hNlarge hMlarge hMNlarge
  dsimp only at hBase
  change
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if pa a ∈ AW then bAz a else 0)
      (fun b => if pb b ∈ BW then bBz b else 0)
      K‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
        (125*((∑ a : SourceOriginalGramPrimeTuple434 SA,
          sourceOriginalGramPrimeMass434 SA muA a*‖bAz a‖^2) *
          (∑ b : SourceOriginalGramPrimeTuple434 SB,
          sourceOriginalGramPrimeMass434 SB muB b*‖bBz b‖^2)) *
        L^(-Bsave)) at hBase
  rw [hIdentity,hEA,hEB] at hBase
  change
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if pa a ∈ AW then bA a else 0)
      (fun b => if pb b ∈ BW then bB b else 0)
      (fun q => K q * sourceOriginalPureMellinPhase434 ζ
        (pa q.1*pb q.2))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
        (125*(EA*EB)*L^(-Bsave))
  exact hBase
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuKnuDyadMellinUnitInputMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The TRUE SOURCE03 signed primitive Knu Fourier minor is
pointwise small for EACH original output labelled-prime tuple
(vA,vB), when independently sampled auxiliary D_A,D_B prime
products are restricted to genuine two input-product dyads.
Input tests are the constant 1; normalized ORIGINAL harmonic
tuple masses reduce the arbitrary weighted-L2 C6 theorem
to an output-UNIFORM spectral estimate.
No fake primitive pointwise saving or output cardinality loss,
no artificial common major-arc radius. This is ONE input
window only: all-dyad Knu still requires globalization. -/
theorem source_original_true_nu_Knu_dyad_mellin_unit_input_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (ζ : ℝ)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := sourceOriginalGramPrimeProduct434 SA vA
    let XB : ℕ := sourceOriginalGramPrimeProduct434 SB vB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
        sourceOriginalPureMellinPhase434 ζ
          (sourceOriginalGramPrimeProduct434 SA v.1 *
           sourceOriginalGramPrimeProduct434 SB v.2))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    ζ vA vB M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  have hNormA (z : A) : ∑ p ∈ SA z, muA z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hNormB (z : B) : ∑ p ∈ SB z, muB z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hTupleTotalA := source_original_physical_gram_prime_mass_total434
    SA muA hNormA
  have hTupleTotalB := source_original_physical_gram_prime_mass_total434
    SB muB hNormB
  have hKnu := source_original_source03_true_nu_signed_Knu_mellin_weighted_L2_minor434
    cfg D Bsave hD C hExponent hSaving
    L hL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    ζ (fun _ => (1:ℂ)) (fun _ => (1:ℂ))
    vA vB M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hNlarge hMlarge hMNlarge
  dsimp only at hKnu
  have hAenergy :
      (∑ v : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA v * ‖(1:ℂ)‖^2) = 1 := by
    simpa only [norm_one,one_pow,mul_one] using hTupleTotalA
  have hBenergy :
      (∑ v : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB v * ‖(1:ℂ)‖^2) = 1 := by
    simpa only [norm_one,one_pow,mul_one] using hTupleTotalB
  rw [hAenergy,hBenergy] at hKnu
  simpa only [one_mul,mul_one,mul_assoc] using hKnu
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuKnuOutputAtomMellinMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- For ANY two original numerically ATTAINABLE output
source03 BIG prime products nA,nB, the original canonical
signed Knu auxiliary-Dirichlet Fourier minor is controlled
UNIFORMLY in those outputs. Uses existence of genuine
labelled prime tuples in the original supports and the
certified unit-auxiliary dyadic C6 theorem. No synthetic
uniform atom law or input/output identification. This bound
applies to ONE auxiliary input dyad only. -/
theorem source_original_true_nu_Knu_actual_output_atom_mellin_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (ζ : ℝ) (nA nB : ℕ)
    (hnA : nA ∈ sourceOriginalPhysicalProductAtomSupport434
      (fun z : A => d.Tb z.val.1))
    (hnB : nB ∈ sourceOriginalPhysicalProductAtomSupport434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := nA
    let XB : ℕ := nB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
        sourceOriginalPureMellinPhase434 ζ
          (sourceOriginalGramPrimeProduct434 SA v.1 *
           sourceOriginalGramPrimeProduct434 SB v.2))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    ζ nA nB hnA hnB M N P Q hM hN
    a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  change nA ∈ (Finset.univ :
    Finset (SourceOriginalGramPrimeTuple434 SA)).image
      (sourceOriginalGramPrimeProduct434 SA) at hnA
  change nB ∈ (Finset.univ :
    Finset (SourceOriginalGramPrimeTuple434 SB)).image
      (sourceOriginalGramPrimeProduct434 SB) at hnB
  obtain ⟨vA, hvA, hXA⟩ := Finset.mem_image.mp hnA
  obtain ⟨vB, hvB, hXB⟩ := Finset.mem_image.mp hnB
  have hWindow := source_original_true_nu_Knu_dyad_mellin_unit_input_minor434
    cfg D Bsave hD C hExponent hSaving
    L hL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    ζ vA vB M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hNlarge hMlarge hMNlarge
  dsimp only at hWindow
  rw [hXA,hXB] at hWindow
  exact hWindow
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TrueNuEventualMinorMultiplier -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The true SOURCE03 TWO-BIG-block ν-selected physical C6
minor Fourier multiplier has genuine fixed log-power
saving FOR EVERY sufficiently large L. ALL C6 spectral
window boundary conditions follow from the ACTUAL
ν-selected BIG-prime products, not unrelated F1/F2
numeric placeholders. Correct physical group-dependent
harmonic law, group-separation, ν pattern, arbitrary
unit-bounded mark-dependent tests and exponent feasibility
are explicit. Nonempty selected physical prime tuples
vA,vB in their containing dyads are true witnesses,
NOT an assumed final minor estimate.
This is not yet the full ν signed RAW-minus-Knu operator. -/
theorem source_original_source03_eventually_true_nu_big_minor_multiplier434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
       sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (hfA : ∀ v, ‖fA v‖ ≤ 1)
    (hfB : ∀ v, ‖fB v‖ ≤ 1)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hrCap : (r:ℝ) ≤ L^cfg.Carc)
    (hDyadA :
      ((sourceOriginalGramPrimeProduct434
        (fun z : A => d.Tb z.val.1) vA:ℕ):ℝ) ≤ 2*(M:ℝ))
    (hDyadB :
      ((sourceOriginalGramPrimeProduct434
        (fun z : B => d.Tb z.val.1) vB:ℕ):ℝ) ≤ 2*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ vA' : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA' ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA':ℂ)*fA vA'*
        (∑ vB' : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB' ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB':ℂ)*fB vB'*
              Green64SourceC6.integerPhase
                (((a:ℝ)/(r:ℝ)+beta0)*
                  ((sourceOriginalGramPrimeProduct434 SB vB':ℕ):ℝ))
                ((sourceOriginalGramPrimeProduct434 SA vA':ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤
       125*L^(-Bsave) := by
  obtain ⟨L0,hBound⟩ :=
    source_original_source03_true_nu_eventual_C6_boundaries434
      cfg D hD
  refine ⟨max L0 4,?_⟩
  intro L hL
  have hL0 : L0 ≤ L := (le_max_left _ _).trans hL
  have hL4 : (4:ℝ) ≤ L := (le_max_right _ _).trans hL
  intro ι β instI instIE instB instBE
    x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern
    fA fB hfA hfB vA vB M N P Q hM hN
    a r beta0 hr hcop hbeta hP hQ hR hrCap hDyadA hDyadB
  obtain ⟨hNlarge,hMlarge,hMNlarge⟩ :=
    hBound L hL0 x Y Hprime d
      blockA blockB m A B hPattern hTbLower
      vA vB M N r hM hN hr hrCap hDyadA hDyadB
  exact source_original_source03_true_nu_big_bounded_minor_multiplier434
    cfg x L Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    fA fB hfA hfB M N P Q hM hN
    a r beta0 hr hcop hbeta hP hQ
    D Bsave (by linarith) hR
    hNlarge hMlarge hMNlarge
    C hExponent hSaving
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TrueNuFourierMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- The TRUE SOURCE03 ν-physical two-BIG-block integer
minor Fourier multiplier, at its correct shifted-correlation
frequency -k*theta, is uniformly log-power small for all
sufficiently large L. The exact SOURCE03 unit sine/exponential
normalization and frequency SIGN have been verified against
C6 integerPhase, including 2π, with no conjectural phase
identification. Fully marked source/target test weights
remain arbitrary complex functions bounded by one.
The authentic BIG prime lower support, harmonic normalizer
equality, group separation, full ν-index origin and
Diophantine minor denominator restrictions are explicit.
Still NOT the source RAW-minus-Knu/Hoeffding signed residual. -/
theorem source_original_source03_eventually_true_nu_fourier_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
       sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (hfA : ∀ v, ‖fA v‖ ≤ 1)
    (hfB : ∀ v, ‖fB v‖ ≤ 1)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hrCap : (r:ℝ) ≤ L^cfg.Carc)
    (hDyadA :
      ((sourceOriginalGramPrimeProduct434
        (fun z : A => d.Tb z.val.1) vA:ℕ):ℝ) ≤ 2*(M:ℝ))
    (hDyadB :
      ((sourceOriginalGramPrimeProduct434
        (fun z : B => d.Tb z.val.1) vB:ℕ):ℝ) ≤ 2*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ vA' : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA' ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA':ℂ)*fA vA'*
        (∑ vB' : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB' ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB':ℂ)*fB vB'*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA vA' *
                  sourceOriginalGramPrimeProduct434 SB vB'):ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤
       125*L^(-Bsave) := by
  obtain ⟨L0,hMinor⟩ :=
    source_original_source03_eventually_true_nu_big_minor_multiplier434
      cfg D Bsave hD C hExponent hSaving
  refine ⟨L0,?_⟩
  intro L hL ι β instI instIE instB instBE
    x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern
    fA fB hfA hfB vA vB M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hrCap hDyadA hDyadB
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  have hBound := hMinor L hL x Y Hprime
    d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern
    fA fB hfA hfB vA vB
    M N P Q hM hN a r beta0 hr hcop hbeta
    hP hQ hR hrCap hDyadA hDyadB
  have hPhase :=
    source_original_physical_minor_fourier_phase_identity434
      SA muA SB muB fA fB AW BW
      theta k a r beta0 hApprox
  dsimp only at hBound ⊢
  rw [hPhase] at hBound
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueActiveGateBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT half-open source03 log-cell semantics: there is a
retained cell containing X iff X's UNIQUE actual index
belongs to the active family. This is not an extra assumption
about a physical endpoint, and no logarithmic cell overlap
is possible. -/
theorem source_original_true_active_exists_iff_index434
    (active : Finset ℤ) (h : ℝ) (hh : 0 < h) (X : ℕ) :
    (∃ j ∈ active, sourceOriginalLiteralLogCell434 h j X) ↔
      sourceOriginalLiteralLogCellIndex434 h X ∈ active := by
  constructor
  · rintro ⟨j,hj,hCell⟩
    have heq := (source_original_literal_log_cell_iff_index434
      h hh X j).mp hCell
    simpa only [heq] using hj
  · intro hj
    exact ⟨sourceOriginalLiteralLogCellIndex434 h X,
      hj,source_original_literal_log_cell_index_mem434 h hh X⟩

/-- Original physical source03 ν-pattern EXACT dropped-state
signed rational-error modulus ONE. Here both endpoint states
are the entire group-variable free-slot arrays, and the A/B
products are computed from the injective true ν-index maps.
Thus C161 genuinely applies to the FULL physical comparison,
not only to abstract independent prime-tuple endpoints. -/
theorem source_original_probe_true_physical_dropped_error_norm434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (source target : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1,
          ((target
            (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν z).1
            (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2,
          ((source
            (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν z).1
            (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi) :
    ‖sourceOriginalProbeSignedRationalError434
      J ell m hmJ ν P V Q hA hB xi r hr u
      (fun g i => (source g i).val)
      (fun g i => (target g i).val)‖ = 1 := by
  have hExactA :
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (target g i).val) =
      ∏ z : ν.1,
         ((target
           (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν z).1
           (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν z).2).val:ℕ) := by
    rfl
  have hExactB :
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (source g i).val) =
      ∏ z : ν.2,
         ((source
           (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν z).1
           (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν z).2).val:ℕ) := by
    rfl
  have hDrop' :
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (target g i).val)) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (source g i).val)) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi := by
    simpa only [hExactA,hExactB] using hDrop
  exact source_original_probe_signed_rational_error_norm_discarded434
    J ell m hmJ ν P V Q hA hB xi hhA hhB
    r hr u (fun g i => (source g i).val)
    (fun g i => (target g i).val) hDrop'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalActiveBadBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- TRUE original source03 ν-pattern ACTIVE GLOBAL source/target
masks are exactly the complement of the discarded GLOBAL cells
when evaluated at the original selected physical prime-mark
products. This bridges all four ORIGINAL predicate formulations:
B source, A target, actual embedding to ν selected slots, and
literal half-open log-product cells. No fictitious laws or
chosen external masks; the result is a genuine finite equality. -/
theorem source_original_probe_true_physical_active_bad_iff434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (s v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    ((∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))) ↔
      ¬(sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, (s (eB z).1 (eB z).2).val) ∉ activeB)) ∧
    ((∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))) ↔
      ¬(sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, (v (eA z).1 (eA z).2).val) ∉ activeA)) := by
  classical
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  have hPB :
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val) =
      (∏ z : ν.2, (s (eB z).1 (eB z).2).val) := by
    rfl
  have hPA :
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val) =
      (∏ z : ν.1, (v (eA z).1 (eA z).2).val) := by
    rfl
  have hs := source_original_true_active_exists_iff_index434
    activeB hB hhB
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val))
  have ht := source_original_true_active_exists_iff_index434
    activeA hA hhA
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val))
  rw [hPB] at hs
  rw [hPA] at ht
  exact ⟨hs.trans (not_not.symm), ht.trans (not_not.symm)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueDyadWindowBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact source03 dyadic integer window: no artificial
rounding loss or extension outside [M,2M). -/
theorem source_original_true_dyad_ico_range434 (M : ℕ) :
    Finset.Ico M (2*M) =
      (Finset.range M).image (fun i => M+i) := by
  ext n
  simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨n-M,by omega,by omega⟩
  · rintro ⟨i,hi,rfl⟩
    constructor <;> omega

/-- The original physical two-prime-tuple bilinear sum,
with arbitrary tuple-dependent complex tests and coupled
integer kernel, is EXACTLY the integer C6 atom bilinear
rectangle on [M,2M)×[N,2N). This also works for empty
dyads and repeated numerical primes across distinct slots. -/
theorem source_original_true_dyad_finite_bilinear_C6_identity434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N : ℕ) (K : ℕ → ℕ → ℂ) :
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
       fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
    let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
       fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      (fun a => if pa a ∈ Finset.Ico M (2*M) then fA a else 0)
      (fun b => if pb b ∈ Finset.Ico N (2*N) then fB b else 0)
      (fun q => K (pa q.1) (pb q.2)) =
    ∑ i ∈ Finset.range M,
      sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
      (∑ j ∈ Finset.range N,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          K (M+i) (N+j)) := by
  classical
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  have hBridge :=
    source_original_physical_window_mode_bilinear_bridge434
      wa wb pa pb fA fB
      (Finset.Ico M (2*M)) (Finset.Ico N (2*N)) K
  have hFub :=
    source_original_physical_two_shifted_window_fubini434
      SA muA SB muB fA fB M N M N K
  dsimp only at hFub
  rw [←source_original_true_dyad_ico_range434 M,
      ←source_original_true_dyad_ico_range434 N] at hFub
  exact hBridge.trans hFub
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCellRectangleAtom -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- One genuine source03 GLOBAL-cell rectangle is IDENTICAL
to its original C6 integer-atom dyad, with arbitrary
prime-label-dependent coefficients and an arbitrary joint
kernel. The source cell gates remain part of the tests. -/
theorem source_original_true_cell_rectangle_atom_exact434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (jA jB : ℤ)
    (baseA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (baseB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N : ℕ) (K : ℕ → ℕ → ℂ) :
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
    let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a)
        then baseA a else 0
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b)
        then baseB b else 0
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      (fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
        pa a ∈ Finset.Ico M (2*M) then baseA a else 0)
      (fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
        pb b ∈ Finset.Ico N (2*N) then baseB b else 0)
      (fun q => K (pa q.1) (pb q.2)) =
    ∑ i ∈ Finset.range M,
      sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
      (∑ j ∈ Finset.range N,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          K (M+i) (N+j)) := by
  classical
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a)
      then baseA a else 0
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b)
      then baseB b else 0
  have hMaskA (a : SourceOriginalGramPrimeTuple434 SA) :
      (if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
          pa a ∈ Finset.Ico M (2*M) then baseA a else 0) =
      (if pa a ∈ Finset.Ico M (2*M) then fA a else 0) := by
    by_cases hc : sourceOriginalLiteralLogCell434 hA jA (pa a)
    · by_cases hw : pa a ∈ Finset.Ico M (2*M)
      · simp [hc,hw,fA]
      · simp [hc,hw,fA]
    · simp [hc,fA]
  have hMaskB (b : SourceOriginalGramPrimeTuple434 SB) :
      (if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
          pb b ∈ Finset.Ico N (2*N) then baseB b else 0) =
      (if pb b ∈ Finset.Ico N (2*N) then fB b else 0) := by
    by_cases hc : sourceOriginalLiteralLogCell434 hB jB (pb b)
    · by_cases hw : pb b ∈ Finset.Ico N (2*N)
      · simp [hc,hw,fB]
      · simp [hc,hw,fB]
    · simp [hc,fB]
  have hAtom := source_original_true_dyad_finite_bilinear_C6_identity434
    SA muA SB muB fA fB M N K
  dsimp only at hAtom
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      (fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
        pa a ∈ Finset.Ico M (2*M) then baseA a else 0)
      (fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
        pb b ∈ Finset.Ico N (2*N) then baseB b else 0)
      (fun q => K (pa q.1) (pb q.2)) = _
  calc
    _ = sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      (fun a => if pa a ∈ Finset.Ico M (2*M) then fA a else 0)
      (fun b => if pb b ∈ Finset.Ico N (2*N) then fB b else 0)
      (fun q => K (pa q.1) (pb q.2)) := by
        have hfunA :
          (fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
            pa a ∈ Finset.Ico M (2*M) then baseA a else 0) =
          (fun a => if pa a ∈ Finset.Ico M (2*M) then fA a else 0) :=
            funext hMaskA
        have hfunB :
          (fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
            pb b ∈ Finset.Ico N (2*N) then baseB b else 0) =
          (fun b => if pb b ∈ Finset.Ico N (2*N) then fB b else 0) :=
            funext hMaskB
        rw [hfunA,hfunB]
    _ = _ := hAtom
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFourAtomExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Literal original source03 shifted integer-atom C6 rectangle;
only a convenient name for the existing finite double sum. -/
noncomputable def sourceOriginalTrueDyadC6Rectangle434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range M,
    sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
    (∑ j ∈ Finset.range N,
      sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
        K (M+i) (N+j))

/-- Actual source03 two independently marked GLOBAL cells:
the entire physical bilinear sum is EXACTLY the FOUR shifted
C6 integer-atom rectangles, preserving arbitrary complex
mark-dependent endpoint tests, true prime laws and any
joint Fourier phase, with zero discarded support. -/
theorem source_original_true_two_cells_four_C6_rectangles_exact434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hPrimeA : ∀ i p, p ∈ SA i → p.Prime)
    (hPrimeB : ∀ i p, p ∈ SB i → p.Prime)
    (hA hB : ℝ) (hwA : hA ≤ 1) (hwB : hB ≤ 1)
    (jA jB : ℤ)
    (baseA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (baseB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (K : ℕ → ℕ → ℂ) :
    let MA : ℕ := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let MB : ℕ := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
    let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a)
        then baseA a else 0
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b)
        then baseB b else 0
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb fA fB
      (fun q => K (pa q.1) (pb q.2)) =
      sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
        fA fB MA MB K +
      sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
        fA fB MA (2*MB) K +
      sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
        fA fB (2*MA) MB K +
      sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
        fA fB (2*MA) (2*MB) K := by
  classical
  let MA : ℕ := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let MB : ℕ := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a)
      then baseA a else 0
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b)
      then baseB b else 0
  let a0 : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
      pa a ∈ Finset.Ico MA (2*MA) then baseA a else 0
  let a1 : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434 hA jA (pa a) ∧
      pa a ∈ Finset.Ico (2*MA) (4*MA) then baseA a else 0
  let b0 : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
      pb b ∈ Finset.Ico MB (2*MB) then baseB b else 0
  let b1 : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434 hB jB (pb b) ∧
      pb b ∈ Finset.Ico (2*MB) (4*MB) then baseB b else 0
  have hPprodA (a : SourceOriginalGramPrimeTuple434 SA) :
      0 < pa a := by
    dsimp [pa,sourceOriginalGramPrimeProduct434]
    apply Finset.prod_pos
    intro i hi
    exact (hPrimeA i (a i).val (a i).property).pos
  have hPprodB (b : SourceOriginalGramPrimeTuple434 SB) :
      0 < pb b := by
    dsimp [pb,sourceOriginalGramPrimeProduct434]
    apply Finset.prod_pos
    intro i hi
    exact (hPrimeB i (b i).val (b i).property).pos
  have hFour :=
    source_original_true_two_cell_four_physical_rectangles434
      pa pb hPprodA hPprodB hA hB hwA hwB
      jA jB wa wb baseA baseB
      (fun q => K (pa q.1) (pb q.2))
  change sourceOriginalFiniteTwoSidedMinorBilinear434
      wa wb fA fB (fun q => K (pa q.1) (pb q.2)) =
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a0 b0 (fun q => K (pa q.1) (pb q.2)) +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a0 b1 (fun q => K (pa q.1) (pb q.2)) +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a1 b0 (fun q => K (pa q.1) (pb q.2)) +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a1 b1 (fun q => K (pa q.1) (pb q.2)) at hFour
  have h00 := source_original_true_cell_rectangle_atom_exact434
    SA muA SB muB hA hB jA jB baseA baseB MA MB K
  have h01 := source_original_true_cell_rectangle_atom_exact434
    SA muA SB muB hA hB jA jB baseA baseB MA (2*MB) K
  have h10 := source_original_true_cell_rectangle_atom_exact434
    SA muA SB muB hA hB jA jB baseA baseB (2*MA) MB K
  have h11 := source_original_true_cell_rectangle_atom_exact434
    SA muA SB muB hA hB jA jB baseA baseB (2*MA) (2*MB) K
  have hDoubleA : 2*(2*MA) = 4*MA := by omega
  have hDoubleB : 2*(2*MB) = 4*MB := by omega
  simp only [hDoubleA,hDoubleB] at h01 h10 h11
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a0 b0 (fun q => K (pa q.1) (pb q.2)) =
        sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
          fA fB MA MB K at h00
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a0 b1 (fun q => K (pa q.1) (pb q.2)) =
        sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
          fA fB MA (2*MB) K at h01
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a1 b0 (fun q => K (pa q.1) (pb q.2)) =
        sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
          fA fB (2*MA) MB K at h10
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      a1 b1 (fun q => K (pa q.1) (pb q.2)) =
        sourceOriginalTrueDyadC6Rectangle434 SA muA SB muB
          fA fB (2*MA) (2*MB) K at h11
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      fA fB (fun q => K (pa q.1) (pb q.2)) = _
  rw [hFour,h00,h01,h10,h11]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexFullCellMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Complete original source03 TWO GLOBAL-log-cell physical
minor multiplier for ONE actual five-index term z.
All four genuine dyadic C6 rectangles are assembled.
Hcell and both integer windows are derived from z itself;
arbitrary tuple-labelled endpoint tests and the signed
-k*theta phase remain exact. Quantitative squared saving
is 16*125=2000, no log-exponent loss. This is not
yet the full multi-pattern RAW-minus-Knu comparison. -/
theorem eventually_source_original_true_five_index_full_cell_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D) (C : ℕ)
    (hExponent : cfg.C0*Real.log
      (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (blockA blockB : Finset β)
      (hDisjoint : Disjoint blockA blockB)
      (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
        Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hA hB : SourceOriginalProbePattern434 β m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hA ν ∧ hA ν ≤ 1)
      (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hB ν ∧ hB ν ≤ 1)
      (xi : ℝ)
      (z : Σ ν : SourceOriginalProbePattern434 β m,
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) ×
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))))
      (hz : z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar d.Tb d.Vbig hA hB xi)
      (baseA : SourceOriginalGramPrimeTuple434
        (fun t : z.1.1 => d.Tb t.val.1) → ℂ)
      (baseB : SourceOriginalGramPrimeTuple434
        (fun t : z.1.2 => d.Tb t.val.1) → ℂ)
      (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
      (hOutside : (theta:AddCircle (1:ℝ)) ∉
         sourceCircleRationalArcs434
           (k.natAbs*Nat.ceil (L^(D+1)))
           (L^cfg.Carc/
             sourceOriginalProbeTrueHprime434 m Qchar hA hB z)),
      let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
      let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
      let muA : z.1.1 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let muB : z.1.2 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let pa := sourceOriginalGramPrimeProduct434 SA
      let pb := sourceOriginalGramPrimeProduct434 SB
      let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
      let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
      let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => if sourceOriginalLiteralLogCell434
          (hA z.1) z.2.1.1 (pa a) then baseA a else 0
      let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => if sourceOriginalLiteralLogCell434
          (hB z.1) z.2.2.1 (pb b) then baseB b else 0
      let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
      let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
      ‖sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
        fA fB (fun q => Green64SourceC6.integerPhase
           (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))‖^2 ≤
        2000*(EA*EB)*L^(-Bsave) := by
  have hLocal :=
    eventually_source_original_true_five_index_circle_dyadic434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hLocal] with L hLocalL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep blockA blockB hDisjoint
    m Qchar hm hTbLower hA hB hhA hhB xi
    z hz baseA baseB theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434
      (hA z.1) z.2.1.1 (pa a) then baseA a else 0
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434
      (hB z.1) z.2.2.1 (pb b) then baseB b else 0
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  let MA : ℕ := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hA z.1))
  let MB : ℕ := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hB z.1))
  let phase : ℕ → ℕ → ℂ := fun n p =>
    Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (((n*p:ℕ):ℤ))
  let Z00 : ℂ := sourceOriginalTrueDyadC6Rectangle434
    SA muA SB muB fA fB MA MB phase
  let Z01 : ℂ := sourceOriginalTrueDyadC6Rectangle434
    SA muA SB muB fA fB MA (2*MB) phase
  let Z10 : ℂ := sourceOriginalTrueDyadC6Rectangle434
    SA muA SB muB fA fB (2*MA) MB phase
  let Z11 : ℂ := sourceOriginalTrueDyadC6Rectangle434
    SA muA SB muB fA fB (2*MA) (2*MB) phase
  let Ksave : ℝ := 125*(EA*EB)*L^(-Bsave)
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hFour := source_original_true_two_cells_four_C6_rectangles_exact434
    SA muA SB muB
    (fun t p hp => d.hTbPrime t.val.1 p hp)
    (fun t p hp => d.hTbPrime t.val.1 p hp)
    (hA z.1) (hB z.1)
    (hhA z.1 hν).2 (hhB z.1 hν).2
    z.2.1.1 z.2.2.1 baseA baseB phase
  change sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
      fA fB (fun q => phase (pa q.1) (pb q.2)) =
      Z00+Z01+Z10+Z11 at hFour
  have h00 := hLocalL x Y Hprime d sep
      blockA blockB hDisjoint m Qchar hm hTbLower
      hA hB hhA hhB xi z hz fA fB
      MA MB (Or.inl rfl) (Or.inl rfl) theta k hk hOutside
  have h01 := hLocalL x Y Hprime d sep
      blockA blockB hDisjoint m Qchar hm hTbLower
      hA hB hhA hhB xi z hz fA fB
      MA (2*MB) (Or.inl rfl) (Or.inr rfl)
      theta k hk hOutside
  have h10 := hLocalL x Y Hprime d sep
      blockA blockB hDisjoint m Qchar hm hTbLower
      hA hB hhA hhB xi z hz fA fB
      (2*MA) MB (Or.inr rfl) (Or.inl rfl)
      theta k hk hOutside
  have h11 := hLocalL x Y Hprime d sep
      blockA blockB hDisjoint m Qchar hm hTbLower
      hA hB hhA hhB xi z hz fA fB
      (2*MA) (2*MB) (Or.inr rfl) (Or.inr rfl)
      theta k hk hOutside
  change ‖Z00‖^2 ≤ Ksave at h00
  change ‖Z01‖^2 ≤ Ksave at h01
  change ‖Z10‖^2 ≤ Ksave at h10
  change ‖Z11‖^2 ≤ Ksave at h11
  have hKnonneg : 0 ≤ Ksave :=
    (sq_nonneg (‖Z00‖)).trans h00
  have hAssembly :=
    source_original_four_dyad_triangle_square434
      Z00 Z01 Z10 Z11 Ksave hKnonneg h00 h01 h10 h11
  change ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wa wb fA fB (fun q => phase (pa q.1) (pb q.2))‖^2 ≤
      2000*(EA*EB)*L^(-Bsave)
  calc
    _ = ‖Z00+Z01+Z10+Z11‖^2 :=
      congrArg (fun v : ℂ => ‖v‖^2) hFour
    _ ≤ 16*Ksave := hAssembly
    _ = 2000*(EA*EB)*L^(-Bsave) := by
      dsimp only [Ksave]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexUnitCellMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Source03's genuine harmonic normalization makes the
complete two-GLOBAL-cell original ν-physical minor estimate
UNIFORM for arbitrary supnorm-one marked tests:
‖full cell multiplier‖² ≤ 2000*L^(-Bsave).
No extra energy or product-dependent-test assumptions.
This is per original five-index term and outside its
genuine moving-Hcell major arcs, not the full Knu family. -/
theorem eventually_source_original_true_five_index_unit_cell_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D) (C : ℕ)
    (hExponent : cfg.C0*Real.log
      (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g =
        ∑ p ∈ d.Tb g,1/(p:ℝ))
      (blockA blockB : Finset β)
      (hDisjoint : Disjoint blockA blockB)
      (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
        Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hA hB : SourceOriginalProbePattern434 β m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hA ν ∧ hA ν ≤ 1)
      (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hB ν ∧ hB ν ≤ 1)
      (xi : ℝ)
      (z : Σ ν : SourceOriginalProbePattern434 β m,
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) ×
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))))
      (hz : z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar d.Tb d.Vbig hA hB xi)
      (baseA : SourceOriginalGramPrimeTuple434
        (fun t : z.1.1 => d.Tb t.val.1) → ℂ)
      (baseB : SourceOriginalGramPrimeTuple434
        (fun t : z.1.2 => d.Tb t.val.1) → ℂ)
      (hbA : ∀ v, ‖baseA v‖ ≤ 1)
      (hbB : ∀ v, ‖baseB v‖ ≤ 1)
      (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
      (hOutside : (theta:AddCircle (1:ℝ)) ∉
         sourceCircleRationalArcs434
           (k.natAbs*Nat.ceil (L^(D+1)))
           (L^cfg.Carc/
             sourceOriginalProbeTrueHprime434 m Qchar hA hB z)),
      let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
      let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
      let muA : z.1.1 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let muB : z.1.2 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let pa := sourceOriginalGramPrimeProduct434 SA
      let pb := sourceOriginalGramPrimeProduct434 SB
      let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
      let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
      let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => if sourceOriginalLiteralLogCell434
          (hA z.1) z.2.1.1 (pa a) then baseA a else 0
      let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => if sourceOriginalLiteralLogCell434
          (hB z.1) z.2.2.1 (pb b) then baseB b else 0
      ‖sourceOriginalFiniteTwoSidedMinorBilinear434 wa wb
        fA fB (fun q => Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))‖^2 ≤
        2000*L^(-Bsave) := by
  have hOriginal :=
    eventually_source_original_true_five_index_full_cell_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hOriginal,eventually_ge_atTop (1:ℝ)]
    with L hBound hL
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hA hB hhA hhB xi z hz baseA baseB hbA hbB
    theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => if sourceOriginalLiteralLogCell434
      (hA z.1) z.2.1.1 (pa a) then baseA a else 0
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => if sourceOriginalLiteralLogCell434
      (hB z.1) z.2.2.1 (pb b) then baseB b else 0
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  have hfA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖fA v‖ ≤ 1 := by
    dsimp [fA]
    split_ifs
    · exact hbA v
    · norm_num
  have hfB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖fB v‖ ≤ 1 := by
    dsimp [fB]
    split_ifs
    · exact hbB v
    · norm_num
  have hEA : EA ≤ 1 :=
    source_original_source03_big_nu_bounded_energy434
      cfg x L Y Hprime d hVbig m z.1.1 fA hfA
  have hEB : EB ≤ 1 :=
    source_original_source03_big_nu_bounded_energy434
      cfg x L Y Hprime d hVbig m z.1.2 fB hfB
  have hMassNonnegB
      (v : SourceOriginalGramPrimeTuple434 SB) :
      0 ≤ sourceOriginalGramPrimeMass434 SB muB v := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    have hp := d.hTbPrime i.val.1 (v i).val (v i).property
    have hpR : (0:ℝ) < (v i).val := by
      exact_mod_cast hp.pos
    have hV : 0 < d.Vbig i.val.1 :=
      cfg.hv.trans_le (d.hVbig i.val.1)
    dsimp [muB]
    positivity
  have hEBnonneg : 0 ≤ EB := by
    dsimp [EB]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (hMassNonnegB v) (sq_nonneg _)
  have hEprod : EA*EB ≤ 1 := by
    calc
      _ ≤ (1:ℝ)*1 :=
        mul_le_mul hEA hEB hEBnonneg (by norm_num)
      _ = 1 := by ring
  have hOrig := hBound x Y Hprime d sep blockA blockB
      hDisjoint m Qchar hm hTbLower hA hB hhA hhB xi
      z hz baseA baseB theta k hk hOutside
  change ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wa wb fA fB
      (fun q => Green64SourceC6.integerPhase
        (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))‖^2 ≤
        2000*(EA*EB)*L^(-Bsave) at hOrig
  have hPower : 0 ≤ L^(-Bsave) :=
    Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hScale : 0 ≤ 2000*L^(-Bsave) := by positivity
  have hCompare :
      (2000*L^(-Bsave))*(EA*EB) ≤
      (2000*L^(-Bsave))*1 :=
    mul_le_mul_of_nonneg_left hEprod hScale
  change ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wa wb fA fB
      (fun q => Green64SourceC6.integerPhase
        (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))‖^2 ≤
        2000*L^(-Bsave)
  calc
    _ ≤ 2000*(EA*EB)*L^(-Bsave) := hOrig
    _ = (2000*L^(-Bsave))*(EA*EB) := by ring
    _ ≤ (2000*L^(-Bsave))*1 := hCompare
    _ = 2000*L^(-Bsave) := by ring
end Green64Analytic.CorrelationSquare

end

