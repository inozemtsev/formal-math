module

public import Green64.Library.Weights.Part053
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part046
public import Green64.Library.Correlation.Part040
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part051
public import Green64.Library.Correlation.Part037
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part052
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part021
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Correlation / Part041

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalCanonicalDyadicIntegerMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Exact joint two-INTEGER output pushforward; the coupled residual
is not replaced by a function of only the product nA*nB. -/
theorem source_original_actual_two_output_joint_atom_pushforward434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (F : ℕ → ℕ → ℂ) :
    (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
              SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
       (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
         fA ab.1 * fB ab.2 *
         F (sourceOriginalGramPrimeProduct434 SA ab.1)
            (sourceOriginalGramPrimeProduct434 SB ab.2)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 SA,
      ∑ m ∈ sourceOriginalPhysicalProductAtomSupport434 SB,
        sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA n *
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB m *
        F n m := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let prodA : XA → ℕ := sourceOriginalGramPrimeProduct434 SA
  let prodB : XB → ℕ := sourceOriginalGramPrimeProduct434 SB
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let TA : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 SB
  let aCoeff := sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA
  let bCoeff := sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB
  have hCollapseA (m : ℕ) :
      (∑ a : XA, (wA a:ℂ)*fA a*F (prodA a) m) =
      ∑ n ∈ TA, aCoeff n*F n m := by
    exact source_original_physical_product_atom_test_pushforward434
      SA muA fA (fun n => F n m)
  have hCollapseB (a : XA) :
      (∑ b : XB, (wB b:ℂ)*fB b*F (prodA a) (prodB b)) =
      ∑ m ∈ TB, bCoeff m*F (prodA a) m := by
    exact source_original_physical_product_atom_test_pushforward434
      SB muB fB (fun m => F (prodA a) m)
  change (∑ ab : XA × XB,
    ((wA ab.1:ℂ)*(wB ab.2:ℂ))*fA ab.1*fB ab.2*
      F (prodA ab.1) (prodB ab.2)) =
    ∑ n ∈ TA, ∑ m ∈ TB, aCoeff n*bCoeff m*F n m
  calc
    _ = ∑ a : XA, ∑ b : XB,
          ((wA a:ℂ)*fA a)*((wB b:ℂ)*fB b*
              F (prodA a) (prodB b)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
    _ = ∑ a : XA, ((wA a:ℂ)*fA a)*
          (∑ b : XB, (wB b:ℂ)*fB b*
              F (prodA a) (prodB b)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
    _ = ∑ a : XA, ((wA a:ℂ)*fA a)*
          (∑ m ∈ TB, bCoeff m*F (prodA a) m) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hCollapseB a]
    _ = ∑ m ∈ TB, bCoeff m*
          (∑ a : XA, (wA a:ℂ)*fA a*
              F (prodA a) m) := by
        calc
          _ = ∑ a : XA, ∑ m ∈ TB,
                bCoeff m*((wA a:ℂ)*fA a*
                  F (prodA a) m) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = ∑ m ∈ TB, ∑ a : XA,
                bCoeff m*((wA a:ℂ)*fA a*
                  F (prodA a) m) := by
            rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
    _ = ∑ m ∈ TB, bCoeff m*
          (∑ n ∈ TA, aCoeff n*F n m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hCollapseA m]
    _ = ∑ n ∈ TA, ∑ m ∈ TB,
          aCoeff n*bCoeff m*F n m := by
        calc
          _ = ∑ m ∈ TB, ∑ n ∈ TA,
                aCoeff n*bCoeff m*F n m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = _ := by
            rw [Finset.sum_comm]

/-- Two independent real product-atom inverse lifts recover arbitrary
coefficients against the ORIGINAL joint two-output residual. -/
theorem source_original_actual_joint_window_inverse_pairing434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i p, p ∈ SA i → 0 < muA i p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i p, p ∈ SB i → 0 < muB i p)
    (WA WB : Finset ℕ) (a b : ℕ → ℂ)
    (H : ℕ → ℕ → ℂ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
      (sourceOriginalPhysicalProductAtomWindowInverseLift434 SA muA WA a)
      (sourceOriginalPhysicalProductAtomWindowInverseLift434 SB muB WB b)
      (fun p => H (sourceOriginalGramPrimeProduct434 SA p.1)
                  (sourceOriginalGramPrimeProduct434 SB p.2)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 SA,
      ∑ m ∈ sourceOriginalPhysicalProductAtomSupport434 SB,
        (if n ∈ WA then a n else 0) *
        (if m ∈ WB then b m else 0) * H n m := by
  classical
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  rw [source_original_actual_two_output_joint_atom_pushforward434]
  apply Finset.sum_congr rfl
  intro n hn
  rw [source_original_physical_atom_window_inverse_recovers434
    SA muA hmuA WA a n hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [source_original_physical_atom_window_inverse_recovers434
    SB muB hmuB WB b m hm]

/-- Actual inverse-atom C6 minor bound for the original canonical
joint two-integer signed residual. It inherits uniform thresholds
before the group type and has no assumed residual smallness. -/
theorem eventually_source_original_CANONICAL_DYADIC_INTEGER_minor434
    (cfg : SourceComparisonFixed434)
    (Cq : ℕ) (Cxi gamma dscale : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma) (hdscale : 0 ≤ dscale) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J)
      (aCoeff bCoeff : ℕ → ℂ),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (ζ : ℝ)
      (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
      (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
      (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
      (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
      (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
      (hP : P ≤ M) (hQ : Q ≤ N)
      (D Bsave : ℝ)
      (hR : L^D ≤ (r:ℝ))
      (hNlarge : L^D ≤ (N:ℝ))
      (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
      (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))
      (C : ℕ)
      (hExponent : cfg.C0*
        Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
          (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
      (hSaving : Bsave+2*(C:ℝ) ≤ D)
      (NA NB : ℕ) (hNA : 0 < NA) (hNB : 0 < NB)
      (hAlignA : hA = Real.log 2/(NA:ℝ))
      (hAlignB : hB = Real.log 2/(NB:ℝ))
      (sA sB : ℕ) (hMA : M = 2^sA) (hNBscale : N = 2^sB)
      (hPM : P = M) (hQN : Q = N),
    let AW := Finset.Ico (2^sA) (2^(sA+1))
    let BW := Finset.Ico (2^sB) (2^(sB+1))
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let EA : ℝ := ∑ n ∈ TA, if n ∈ AW then
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n else 0
    let EB : ℝ := ∑ n ∈ TB, if n ∈ BW then
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n else 0
    ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
      (if nA ∈ AW then aCoeff nA else 0) *
      (if nB ∈ BW then bCoeff nB else 0) *
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k nA nB)‖^2 ≤
      4250*(EA*EB)*L^(-Bsave) := by
  obtain ⟨Y0,hEvent⟩ :=
    eventually_source_original_CANONICAL_DYADIC_RESIDUAL_minor434
      cfg Cq Cxi gamma dscale hCxi hgamma hdscale
  refine ⟨Y0,?_⟩
  filter_upwards [hEvent] with L hMinor
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ aCoeff bCoeff
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let AW := Finset.Ico (2^sA) (2^(sA+1))
  let BW := Finset.Ico (2^sB) (2^(sB+1))
  let fA := sourceOriginalPhysicalProductAtomWindowInverseLift434 SA muA AW aCoeff
  let fB := sourceOriginalPhysicalProductAtomWindowInverseLift434 SB muB BW bCoeff
  have hmuA : ∀ z : ν.1, ∀ p ∈ SA z, 0 < muA z p := by
    intro z p hp
    have hVpos := cfg.hv.trans_le (d.hVbig z.val.1)
    have hpp : (0:ℝ) < p := by exact_mod_cast (d.hTbPrime z.val.1 p hp).pos
    exact div_pos (div_pos zero_lt_one hpp) hVpos
  have hmuB : ∀ z : ν.2, ∀ p ∈ SB z, 0 < muB z p := by
    intro z p hp
    have hVpos := cfg.hv.trans_le (d.hVbig z.val.1)
    have hpp : (0:ℝ) < p := by exact_mod_cast (d.hTbPrime z.val.1 p hp).pos
    exact div_pos (div_pos zero_lt_one hpp) hVpos
  have hSuppA (p : SourceOriginalGramPrimeTuple434 SA)
      (hp : sourceOriginalGramPrimeProduct434 SA p ∉ AW) : fA p=0 := by
    simp only [fA,sourceOriginalPhysicalProductAtomWindowInverseLift434,
      sourceOriginalPhysicalProductAtomInverseLift434,if_neg hp,zero_div]
  have hSuppB (p : SourceOriginalGramPrimeTuple434 SB)
      (hp : sourceOriginalGramPrimeProduct434 SB p ∉ BW) : fB p=0 := by
    simp only [fB,sourceOriginalPhysicalProductAtomWindowInverseLift434,
      sourceOriginalPhysicalProductAtomInverseLift434,if_neg hp,zero_div]
  have hResult := hMinor x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ fA fB
    iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN hSuppA hSuppB
  dsimp only at hResult
  rw [source_original_actual_joint_window_inverse_pairing434
      SA muA hmuA SB muB hmuB AW BW aCoeff bCoeff] at hResult
  rw [source_original_physical_atom_window_inverse_energy434 SA muA hmuA AW aCoeff,
      source_original_physical_atom_window_inverse_energy434 SB muB hmuB BW bCoeff] at hResult
  exact hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalDyadicPhysicalMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 34000000

/-- The LITERAL original signed Fourier/Mellin comparison residual
on one actual coarse rectangle, for arbitrary FULL free-prime-mark
source and target tests with the exact harmonic law and exact local
dyadic energies. Its C6 minor estimate is proved here, not supplied
as a spectral premise. No fine-cell or projection-fibre count loss. -/
theorem eventually_source_original_CANONICAL_DYADIC_PHYSICAL_minor434
    (cfg : SourceComparisonFixed434)
    (Cq : ℕ) (Cxi gamma dscale : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma) (hdscale : 0 ≤ dscale) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (ζ : ℝ)
      (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
      (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
      (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
      (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
      (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
      (hP : P ≤ M) (hQ : Q ≤ N)
      (D Bsave : ℝ)
      (hR : L^D ≤ (r:ℝ))
      (hNlarge : L^D ≤ (N:ℝ))
      (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
      (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))
      (C : ℕ)
      (hExponent : cfg.C0*
        Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
          (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
      (hSaving : Bsave+2*(C:ℝ) ≤ D)
      (NA NB : ℕ) (hNA : 0 < NA) (hNB : 0 < NB)
      (hAlignA : hA = Real.log 2/(NA:ℝ))
      (hAlignB : hB = Real.log 2/(NB:ℝ))
      (sA sB : ℕ) (hMA : M = 2^sA) (hNBscale : N = 2^sB)
      (hPM : P = M) (hQN : Q = N),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : β) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (fun g i => (v g i).val)
    let AW := Finset.Ico (2^sA) (2^(sA+1))
    let BW := Finset.Ico (2^sB) (2^(sB+1))
    ∀ (sourceTest targetTest : X → ℂ),
    let ES : ℝ := ∑ s : X, if projS s ∈ BW then w s*‖sourceTest s‖^2 else 0
    let ET : ℝ := ∑ v : X, if projT v ∈ AW then w v*‖targetTest v‖^2 else 0
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) * star (sourceTest ab.1)*targetTest ab.2 *
        (if projS ab.1 ∈ BW ∧ projT ab.2 ∈ AW then
          sourceOriginalProbeSignedMajorFourierError434
            J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
            (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
         else 0))‖^2 ≤ 4250*L^(-Bsave)*ES*ET := by
  obtain ⟨Y0,hEvent⟩ :=
    eventually_source_original_CANONICAL_DYADIC_INTEGER_minor434
      cfg Cq Cxi gamma dscale hCxi hgamma hdscale
  refine ⟨Y0,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1:ℝ)] with L hMinor hL
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN
  intro sourceTest targetTest
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : β) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (fun g i => (v g i).val)
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let AW := Finset.Ico (2^sA) (2^(sA+1))
  let BW := Finset.Ico (2^sB) (2^(sB+1))
  let budget := 4250*L^(-Bsave)
  let err : ℕ → ℕ → ℂ := fun nA nB =>
    sourceOriginalProbeSignedSelectedFourierError434
      J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k nA nB
  let H : ℕ → ℕ → ℂ := fun nB nA =>
    if nB ∈ BW ∧ nA ∈ AW then err nA nB else 0
  have hBudget : 0 ≤ budget := by dsimp [budget]; positivity
  have hVpos (g : β) : 0 < d.Vbig g := cfg.hv.trans_le (d.hVbig g)
  have hAtomA (n : ℕ) (hn : n ∈ TA) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n :=
    source_original_true_prime_harmonic_atom_pos434
      SA (fun z => d.Vbig z.val.1) (fun z => hVpos z.val.1)
      (fun z p hp => d.hTbPrime z.val.1 p hp) n hn
  have hAtomB (n : ℕ) (hn : n ∈ TB) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n :=
    source_original_true_prime_harmonic_atom_pos434
      SB (fun z => d.Vbig z.val.1) (fun z => hVpos z.val.1)
      (fun z p hp => d.hTbPrime z.val.1 p hp) n hn
  have hSelected (bCoeff aCoeff : ℕ → ℂ) :
      ‖(∑ ij ∈ TB.product TA, bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2)‖^2 ≤
      budget*(∑ n ∈ TB, ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n)*
             (∑ n ∈ TA, ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n) := by
    have hResult := hMinor x Y Hprime d sep hVbig
      blockA blockB hDisjoint m hm ν hPattern Qchar
      hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ aCoeff bCoeff
      iA iB uA vA uB vB huA huB huvA huvB
      hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
      ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
      D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
      NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN
    dsimp only at hResult
    let EA := ∑ n ∈ TA, ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB := ∑ n ∈ TB, ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let EAwin := ∑ n ∈ TA, if n ∈ AW then
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n else 0
    let EBwin := ∑ n ∈ TB, if n ∈ BW then
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n else 0
    have hEA : EAwin ≤ EA := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : n ∈ AW
      · simp only [if_pos h,le_refl]
      · simp only [if_neg h]; exact div_nonneg (sq_nonneg _) (hAtomA n hn).le
    have hEB : EBwin ≤ EB := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : n ∈ BW
      · simp only [if_pos h,le_refl]
      · simp only [if_neg h]; exact div_nonneg (sq_nonneg _) (hAtomB n hn).le
    have hEA0 : 0 ≤ EA := by
      apply Finset.sum_nonneg
      intro n hn
      exact div_nonneg (sq_nonneg _) (hAtomA n hn).le
    have hEBw0 : 0 ≤ EBwin := by
      apply Finset.sum_nonneg
      intro n hn
      split_ifs
      · exact div_nonneg (sq_nonneg _) (hAtomB n hn).le
      · exact le_rfl
    have hProd : EAwin*EBwin ≤ EA*EB := mul_le_mul hEA hEB hEBw0 hEA0
    have hEq :
        (∑ ij ∈ TB.product TA, bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2) =
        ∑ nA ∈ TA, ∑ nB ∈ TB,
          (if nA ∈ AW then aCoeff nA else 0) *
          (if nB ∈ BW then bCoeff nB else 0) * err nA nB := by
      have hProduct :
          (∑ ij ∈ TB.product TA, bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2) =
          ∑ nB ∈ TB, ∑ nA ∈ TA, bCoeff nB*aCoeff nA*H nB nA :=
        Finset.sum_product TB TA (fun ij : ℕ × ℕ => bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2)
      rw [hProduct,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro nA hnA
      apply Finset.sum_congr rfl
      intro nB hnB
      by_cases ha : nA ∈ AW <;> by_cases hb : nB ∈ BW
      all_goals simp only [H,ha,hb,and_self,ite_true,ite_false,
        and_false,false_and,mul_zero,zero_mul]
      ring
    rw [hEq]
    calc
      _ ≤ 4250*(EAwin*EBwin)*L^(-Bsave) := hResult
      _ = budget*(EAwin*EBwin) := by dsimp [budget]; ring
      _ ≤ budget*(EA*EB) := mul_le_mul_of_nonneg_left hProd hBudget
      _ = budget*EB*EA := by ring
  let fS : X → ℂ := fun s => if projS s ∈ BW then sourceTest s else 0
  let fT : X → ℂ := fun v => if projT v ∈ AW then targetTest v else 0
  have hLift := source_original_true_physical_matched_atom_operator434
    J ell m hmJ ν d.Tb d.Vbig hVbig hVpos d.hTbPrime
    H budget hBudget hSelected fS fT
  have hES : (∑ s : X, w s*‖fS s‖^2) =
      ∑ s : X, if projS s ∈ BW then w s*‖sourceTest s‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : projS s ∈ BW <;> simp [fS,h]
  have hET : (∑ v : X, w v*‖fT v‖^2) =
      ∑ v : X, if projT v ∈ AW then w v*‖targetTest v‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : projT v ∈ AW <;> simp [fT,h]
  dsimp only at hLift
  rw [hES,hET] at hLift
  convert hLift using 1
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro ab hab
  change ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*targetTest ab.2 *
      (if projS ab.1 ∈ BW ∧ projT ab.2 ∈ AW then
        sourceOriginalProbeSignedMajorFourierError434
          J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
          (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
       else 0) =
    ((w ab.1*w ab.2:ℝ):ℂ)*star (fS ab.1)*fT ab.2*H (projS ab.1) (projT ab.2)
  have hKernel := source_original_true_signed_fourier_selected_factor434
    J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
    (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  by_cases hs : projS ab.1 ∈ BW <;> by_cases ht : projT ab.2 ∈ AW
  all_goals simp only [fS,fT,H,hs,ht,and_self,ite_true,ite_false,
    and_false,false_and,mul_zero,zero_mul,star_zero]
  exact congrArg (fun z : ℂ =>
    ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*targetTest ab.2*z) hKernel
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeRetainedLocalDyadL2 -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- ORIGINAL ν-pattern source03 signed primitive comparison
on ALL physically RETAINED GLOBAL cells inside one TRUE
pair of product dyads X_A<=2Uscale, X_B<=2Vscale, with
arbitrary complex source/target tests (allowed to depend
on all physical free prime marks). It uses the actual
ν-dependent independent normalized group prime laws.
The O(L^-B) L² estimate follows from the source03 local
per-cell dyad estimate C191 and true measured-point
Cauchy-Schwarz, without summing over cells, without any
coarse exp(m*L^d) bound, and uniform |zeta|<=L^C4.
The dropped region/minor arcs are NOT included. -/
theorem source_original_probe_retained_local_dyad_signed_L2_unconditional434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
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
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (ζ beta : ℝ) (Uscale Vscale S : ℝ)
      (hUscale : 0 ≤ Uscale) (hVscale : 0 ≤ Vscale)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hDir : |beta| *(Uscale*Vscale) ≤ 2*S/(r:ℝ))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4)
      (sourceTest targetTest :
        SourceOriginalVariableBIGState434
          (fun g : G => {p : ℕ // p ∈ P g})
          (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ),
      let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
      let t : G → ℕ := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
      let prime : (g : G) → BP g → ℕ := fun g p => p.val
      let mu := sourceOriginalJointHarmonicMu434 BP prime V
      let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
      let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
      let gateSource : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun s =>
          (∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
            (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
              (fun g i => (s g i).val))) ∧
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
      let gateTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun v =>
          (∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
            (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
              (fun g i => (v g i).val))) ∧
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
      let err : (SourceOriginalVariableBIGState434 BP t) ×
                (SourceOriginalVariableBIGState434 BP t) → ℂ :=
        fun ab => sourceOriginalProbeSignedMajorSlowError434
          J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val)
      let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
      ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                    (SourceOriginalVariableBIGState434 BP t),
        ((sourceOriginalVariableBIGMass434 BP t mu ab.1 *
           sourceOriginalVariableBIGMass434 BP t mu ab.2 :ℝ):ℂ) *
          star (sourceTest ab.1) * targetTest ab.2 *
          (if gateSource ab.1 ∧ gateTarget ab.2 then err ab else 0))‖^2 ≤
      eps^2 *
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  obtain ⟨K,Y,hK,hMajor⟩ :=
    source_original_probe_active_local_dyad_log_power_unconditional434
      Cq Cxi Cs C4 gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q hBIGA hBIGB hA hB xi hhA hhB hxi L hL
    hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB r hr hrQ u ζ beta
    Uscale Vscale S hUscale hVscale hS hSscale
    hDir hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  dsimp
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let gateSource : SourceOriginalVariableBIGState434 BP t → Prop :=
    fun s =>
      (∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))) ∧
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
  let gateTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
    fun v =>
      (∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))) ∧
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
  let err : (SourceOriginalVariableBIGState434 BP t) ×
              (SourceOriginalVariableBIGState434 BP t) → ℂ :=
    fun ab => sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    have hkv : 0 ≤ K/Vmin := div_nonneg hK hVmin.le
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
  have hVpos (g : G) : 0 < V g :=
    hVmin.trans_le (hMass g)
  have hVEq (g : G) :
      V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      V g = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa [BP,prime] using
          (Finset.sum_coe_sort (P g)
            (fun p : ℕ => 1/(p:ℝ))).symm
  have hPoint (s v : SourceOriginalVariableBIGState434 BP t)
      (hS : gateSource s) (hT : gateTarget v) :
      ‖err (s,v)‖ ≤ eps := by
    obtain ⟨⟨jB,hjB,hCellB⟩,hDyadB⟩ := hS
    obtain ⟨⟨jA,hjA,hCellA⟩,hDyadA⟩ := hT
    have ht (g : G) (i : Fin (t g)) :
        (v g i).val ∈ P g := (v g i).property
    have hs (g : G) (i : Fin (t g)) :
        (s g i).val ∈ P g := (s g i).property
    have hRaw := hMajor J ell m hmJ ν P V
      hV Vmin hVmin hMass Q hBIGA hBIGB
      hA hB xi hhA hhB hxi jA jB hjA hjB
      L hL hLdyad hQ hXi
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB
      hBandA hBandB
      (fun g i => (v g i).val)
      (fun g i => (s g i).val)
      (fun g i => ht g i)
      (fun g i => hs g i)
      hCellA hCellB r hr hrQ u ζ beta
      Uscale Vscale S hUscale hVscale
      hDyadA hDyadB hS hSscale hDir hC4
      hDeltaLe hWidth hWidth1 hZeta
    change ‖err (s,v)‖ ≤ eps at hRaw
    exact hRaw
  have hL2 := source_original_true_variable_BIG_retained_L2_error434
    BP t prime V hVpos hVEq
    sourceTest targetTest gateSource gateTarget err eps heps hPoint
  convert hL2 using 1
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro ab hab
  have hGate :
      (((∃ jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi,
        sourceOriginalLiteralLogCell434 hB jB
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (ab.1 g i).val))) ∧
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (ab.1 g i).val):ℝ) ≤ 2*Vscale) ∧
       ((∃ jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi,
        sourceOriginalLiteralLogCell434 hA jA
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (ab.2 g i).val))) ∧
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (ab.2 g i).val):ℝ) ≤ 2*Uscale)) ↔
      gateSource ab.1 ∧ gateTarget ab.2 := Iff.rfl
  by_cases hg : gateSource ab.1 ∧ gateTarget ab.2
  · have hh := hGate.mpr hg
    simp only [if_pos hh, if_pos hg]
    rfl
  · have hh : ¬(
      ((∃ jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi,
        sourceOriginalLiteralLogCell434 hB jB
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (ab.1 g i).val))) ∧
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (ab.1 g i).val):ℝ) ≤ 2*Vscale) ∧
       ((∃ jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi,
        sourceOriginalLiteralLogCell434 hA jA
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (ab.2 g i).val))) ∧
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (ab.2 g i).val):ℝ) ≤ 2*Uscale)) :=
      fun ha => hg (hGate.mp ha)
    simp only [if_neg hh, if_neg hg]
    rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDroppedMajorSlow -/

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
theorem source_original_probe_signed_major_slow_error_eq_discarded434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi) :
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta source target =
    -((-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      sourceOriginalPositiveRationalPhaseAtNat434 r hr u
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
         sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) *
      sourceOriginalSlowMellinAdditivePhase434 ζ beta
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
    (sourceOriginalPositiveRationalPhaseAtNat434 r hr u (XA*XB) *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta (XA*XB))
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
    (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2) *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2))) = 0 := by
    apply Finset.sum_eq_zero
    intro ab hab
    rw [hK0 ab]
    ring
  unfold sourceOriginalProbeSignedMajorSlowError434
  change (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
       SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB ma mb
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2) *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta
      (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2))) -
      sig*phase =
      -((sig * sourceOriginalPositiveRationalPhaseAtNat434 r hr u (XA*XB)) *
        sourceOriginalSlowMellinAdditivePhase434 ζ beta (XA*XB))
  rw [hS,zero_sub]
  dsimp [sig,phase]
  ring

/-- The exact original SOURCE03 signed major-rational error has
UNIT modulus outside either of its true active GLOBAL cells.
This permits a sharp rare-event L² estimate on the FULL
physical variables; applying a Q-dependent uniform kernel
upper bound there would be spurious and much weaker. -/
theorem source_original_probe_signed_major_slow_error_norm_discarded434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi ∨
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi) :
    ‖sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta source target‖ = 1 := by
  rw [source_original_probe_signed_major_slow_error_eq_discarded434
    J ell m hmJ ν P V Q hA hB xi hhA hhB
    r hr u ζ beta source target hDrop, norm_neg, norm_mul, norm_mul]
  have hsig : ‖-((-1:ℂ)^(ν.1.card+ν.2.card))‖ = 1 := by simp
  rw [hsig, one_mul]
  rw [source_original_positive_rational_phase_norm_one434,
    source_original_slow_mellin_additive_phase_norm_one434]
  norm_num
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueDroppedMajorSlowPhysical -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original physical source03 ν-pattern EXACT dropped-state
signed rational-error modulus ONE. Here both endpoint states
are the entire group-variable free-slot arrays, and the A/B
products are computed from the injective true ν-index maps.
Thus C161 genuinely applies to the FULL physical comparison,
not only to abstract independent prime-tuple endpoints. -/
theorem source_original_probe_true_physical_dropped_major_slow_error_norm434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
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
    ‖sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
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
  exact source_original_probe_signed_major_slow_error_norm_discarded434
    J ell m hmJ ν P V Q hA hB xi hhA hhB
    r hr u ζ beta (fun g i => (source g i).val)
    (fun g i => (target g i).val) hDrop'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDroppedPhaseCutoff -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- The ORIGINAL signed rational/Mellin major error on true physical
source and target free-mark arrays has modulus at most one once it
is restricted to the genuine discarded GLOBAL-cell event.
The source-side test and target-side test are not replaced with
functions of their integer products; no phase separation is used. -/
theorem source_original_probe_true_dropped_phase_cutoff_norm434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (source target : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let badSource : Prop :=
      sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((source (eB z).1 (eB z).2).val:ℕ)) ∉
          sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badTarget : Prop :=
      sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((target (eA z).1 (eA z).2).val:ℕ)) ∉
          sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    ‖(if badSource ∨ badTarget then
      sourceOriginalProbeSignedMajorSlowError434
        J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
        (fun g i => (source g i).val)
        (fun g i => (target g i).val)
     else 0)‖ ≤ (1:ℝ) := by
  classical
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let badSource : Prop :=
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((source (eB z).1 (eB z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badTarget : Prop :=
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((target (eA z).1 (eA z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  change ‖(if badSource ∨ badTarget then
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
      (fun g i => (source g i).val)
      (fun g i => (target g i).val)
    else 0)‖ ≤ (1:ℝ)
  by_cases hb : badSource ∨ badTarget
  · have hdrop : badTarget ∨ badSource := Or.comm.mp hb
    have hnorm :=
      source_original_probe_true_physical_dropped_major_slow_error_norm434
        J ell m hmJ ν P V Q hA hB xi hhA hhB
        r hr u ζ beta source target hdrop
    simpa only [if_pos hb] using hnorm.le
  · simp only [if_neg hb, norm_zero]
    norm_num
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueSignedDiscardedDyadL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The actual source03 signed physical rational/Mellin error,
restricted to discarded GLOBAL cells in one original product
dyad pair, obeys the true ν-dependent weighted-L² loss.
Unlike the generic rare-event theorem, the phase here is the
literal sourceOriginalProbeSignedMajorSlowError434. -/
theorem source_original_probe_true_signed_discarded_dyad_L2_sq434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (Uscale Vscale : ℝ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let dyadSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
    let dyadTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
    let nA := (sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA).card
    let nB := (sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB).card
    let HDrop : (SourceOriginalVariableBIGState434 BP t) ×
                 (SourceOriginalVariableBIGState434 BP t) → ℂ :=
      fun ab => if badSource ab.1 ∨ badTarget ab.2 then
        sourceOriginalProbeSignedMajorSlowError434
          J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val)
      else 0
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                 (SourceOriginalVariableBIGState434 BP t),
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then
            (if badSource ab.1 ∨ badTarget ab.2 then HDrop ab else 0)
           else 0))‖^2 ≤
      (2*((nA+nB:ℕ):ℝ)*xi) *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
    fun s => sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
    fun v => sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉
        sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let HDrop : (SourceOriginalVariableBIGState434 BP t) ×
               (SourceOriginalVariableBIGState434 BP t) → ℂ :=
    fun ab => if badSource ab.1 ∨ badTarget ab.2 then
      sourceOriginalProbeSignedMajorSlowError434
        J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    else 0
  have hHDrop (ab : (SourceOriginalVariableBIGState434 BP t) ×
        (SourceOriginalVariableBIGState434 BP t)) : ‖HDrop ab‖ ≤ 1 := by
    exact source_original_probe_true_dropped_phase_cutoff_norm434
      J ell m hmJ ν P V Q hA hB xi hhA hhB
      r hr u ζ beta ab.1 ab.2
  exact source_original_probe_true_physical_dyadic_discarded_union_L2_sq434
    J ell m hmJ ν P V hV hVpos
    hA hB xi hhA hhB hxi Uscale Vscale
    sourceTest targetTest HDrop hHDrop
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeFullDyadicLocalMajorL2 -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 40000000

/-- C196: ORIGINAL source03 signed ν-dependent FULL physical
major rational+Mellin+irrational-beta comparison on ONE ACTUAL
pair of target-product dyads, across both ALL retained and
ALL discarded GLOBAL product-log cells. Actual independent
harmonic 1/(p*Vg) free-slot measures and arbitrary complex
tests on ALL source/target mark-tuples are preserved.
The retained part uses unconditional C192 (local cell scale);
the discarded part C195 (actual physical mass), and the
precise signed kernel is literally zero on discarded states.
No coarse exp(m L^d) comparison premise. Still only r<=Q
major arcs; large denominator and RAW-Hoeffding open. -/
theorem source_original_probe_full_dyadic_major_L2_unconditional434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
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
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (ζ beta : ℝ) (Uscale Vscale S : ℝ)
      (hUscale : 0 ≤ Uscale) (hVscale : 0 ≤ Vscale)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hDir : |beta| *(Uscale*Vscale) ≤ 2*S/(r:ℝ))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4)
      (sourceTest targetTest :
        SourceOriginalVariableBIGState434
          (fun g : G => {p : ℕ // p ∈ P g})
          (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ),
      let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
      let t : G → ℕ := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
      let prime : (g : G) → BP g → ℕ := fun g p => p.val
      let mu := sourceOriginalJointHarmonicMu434 BP prime V
      let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
      let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
      let gateSource : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun s =>
          (∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
            (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
              (fun g i => (s g i).val))) ∧
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
      let gateTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun v =>
          (∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
            (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
              (fun g i => (v g i).val))) ∧
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
      let dyadSource : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun s => (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
      let dyadTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun v => (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
      let nA := (sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card
      let nB := (sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card
      let droppedLoss : ℝ := 2*((nA+nB:ℕ):ℝ)*xi
      let err : (SourceOriginalVariableBIGState434 BP t) ×
                (SourceOriginalVariableBIGState434 BP t) → ℂ :=
        fun ab => sourceOriginalProbeSignedMajorSlowError434
          J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val)
      let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
      ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                    (SourceOriginalVariableBIGState434 BP t),
        ((sourceOriginalVariableBIGMass434 BP t mu ab.1 *
           sourceOriginalVariableBIGMass434 BP t mu ab.2 :ℝ):ℂ) *
          star (sourceTest ab.1) * targetTest ab.2 *
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then err ab else 0))‖^2 ≤
      2*(eps^2+droppedLoss) *
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  obtain ⟨K,Y,hK,hRet⟩ :=
    source_original_probe_retained_local_dyad_signed_L2_unconditional434
      Cq Cxi Cs C4 gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q hBIGA hBIGB hA hB xi hhA hhB hxi
    L hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB r hr hrQ u ζ beta
    Uscale Vscale S hUscale hVscale hS hSscale hDir hC4
    hDeltaLe hWidth hWidth1 hZeta sourceTest targetTest
  dsimp
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeSource : X → Prop := fun s =>
    ∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let activeTarget : X → Prop := fun v =>
    ∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let dyadSource : X → Prop := fun s =>
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
  let dyadTarget : X → Prop := fun v =>
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
  let gateSource : X → Prop := fun s =>
    activeSource s ∧ dyadSource s
  let gateTarget : X → Prop := fun v =>
    activeTarget v ∧ dyadTarget v
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let bad : X × X → Prop := fun ab =>
    badSource ab.1 ∨ badTarget ab.2
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
  let nA := (sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA).card
  let nB := (sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB).card
  let droppedLoss : ℝ := 2*((nA+nB:ℕ):ℝ)*xi
  let ESource : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
  let ETarget : ℝ := ∑ v : X, w v*‖targetTest v‖^2
  have hVpos (g : G) : 0 < V g :=
    hVmin.trans_le (hMass g)
  have hActiveS (s : X) : activeSource s ↔ ¬badSource s := by
    have hGate :=
      (source_original_probe_true_physical_active_bad_iff434
        J ell m hmJ ν P V hA hB xi hhA hhB s s).1
    exact hGate
  have hActiveT (v : X) : activeTarget v ↔ ¬badTarget v := by
    have hGate :=
      (source_original_probe_true_physical_active_bad_iff434
        J ell m hmJ ν P V hA hB xi hhA hhB v v).2
    exact hGate
  have hEnergySource :
      sourceOriginalVariableBIGEnergy434 BP t mu sourceTest =
        ESource := by
    simp only [sourceOriginalVariableBIGEnergy434,
      Complex.normSq_eq_norm_sq,ESource,w]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  have hEnergyTarget :
      sourceOriginalVariableBIGEnergy434 BP t mu targetTest =
        ETarget := by
    simp only [sourceOriginalVariableBIGEnergy434,
      Complex.normSq_eq_norm_sq,ETarget,w]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  have hGoodRaw := hRet J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi
    L hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB r hr hrQ u ζ beta
    Uscale Vscale S hUscale hVscale hS hSscale
    hDir hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  let HDrop : X × X → ℂ := fun ab =>
    if bad ab then err ab else 0
  have hBadRaw :=
    source_original_probe_true_signed_discarded_dyad_L2_sq434
      J ell m hmJ ν P V hV hVpos
      Q hA hB xi hhA hhB hxi
      r hr u ζ beta Uscale Vscale sourceTest targetTest
  have hHDropEq (ab : X × X)
      (hb : badSource ab.1 ∨ badTarget ab.2) :
      HDrop ab = err ab := by
    have hbad : bad ab := hb
    simp only [HDrop, if_pos hbad]
  have hBad :
      ‖(∑ ab : X × X,
          ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then
            (if badSource ab.1 ∨ badTarget ab.2 then HDrop ab else 0)
           else 0))‖^2 ≤
        droppedLoss*ESource*ETarget := by
    simpa only [droppedLoss, ESource, ETarget] using hBadRaw
  have hGood :
      ‖(∑ ab : X × X,
          ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if (activeSource ab.1 ∧ dyadSource ab.1) ∧
              activeTarget ab.2 ∧ dyadTarget ab.2
           then err ab else 0))‖^2 ≤
        (eps^2)*ESource*ETarget := by
    have hRaw := hGoodRaw
    convert hRaw using 1
    · rw [← hEnergySource, ← hEnergyTarget]
  have hCombined :=
    source_original_finite_dyadic_combine_any_decision434
      w w sourceTest targetTest err HDrop
      dyadSource dyadTarget activeSource activeTarget
      badSource badTarget (fun q => inferInstance)
      hActiveS hActiveT hHDropEq
      (eps^2) droppedLoss
      (by
        convert hGood using 1
        apply congrArg (fun z : ℂ => ‖z‖^2)
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hg :
            (activeSource q.1 ∧ dyadSource q.1) ∧
            (activeTarget q.2 ∧ dyadTarget q.2)
        · simp only [if_pos hg]
        · simp only [if_neg hg]) hBad
  rw [hEnergySource,hEnergyTarget]
  exact hCombined
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedFourierMajorGateTransport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- A genuine SOURCE03 physical major signed RAW-minus-primitive
comparison L² inequality can be transported from the original
rational+Mellin+β kernel to the literal Fourier frequency
-k*theta, on an ARBITRARY true source-target dyadic/active
gate (including all discarded states).
The exact rational real lift and original complete physical
ν prime-array law are preserved. No independent source/target
phase factorization, no new arithmetic saving premise:
hBound is precisely the already established rational
comparison for these same endpoint tests and gate. -/
theorem source_original_true_signed_fourier_major_gate_transport434
    {G X : Type} [DecidableEq G] [Fintype X]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (ζ beta theta : ℝ) (k Nshift : ℤ)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(r:ℝ)+beta-(Nshift:ℝ))
    (source target : X → ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (weight : X → ℝ)
    (sourceTest targetTest : X → ℂ)
    (gate : X × X → Prop)
    (budget : ℝ)
    (hBound :
      ‖(∑ ab : X × X,
        ((weight ab.1*weight ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if gate ab then
            sourceOriginalProbeSignedMajorSlowError434
              J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
              (source ab.1) (target ab.2)
           else 0))‖^2 ≤ budget) :
      ‖(∑ ab : X × X,
        ((weight ab.1*weight ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if gate ab then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ theta k
              (source ab.1) (target ab.2)
           else 0))‖^2 ≤ budget := by
  classical
  have hSum :
      (∑ ab : X × X,
        ((weight ab.1*weight ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if gate ab then
            sourceOriginalProbeSignedMajorSlowError434
              J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
              (source ab.1) (target ab.2)
           else 0)) =
      (∑ ab : X × X,
        ((weight ab.1*weight ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if gate ab then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ theta k
              (source ab.1) (target ab.2)
           else 0)) := by
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hg : gate ab
    · simp only [if_pos hg]
      rw [source_original_true_signed_major_fourier_error_eq434
        J ell m hmJ ν P V Q hA hB xi
        r hr u ζ beta theta k Nshift hLift
        (source ab.1) (target ab.2)]
    · simp only [if_neg hg]
  rw [←hSum]
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueFullDyadicFourierMajor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 43000000

/-- The source03 true full ν-physical C196 per-dyad signed
RAW-minus-canonical-Knu major L² comparison transported to
ACTUAL original integer Fourier frequency -k theta, preserving
all real prime-label harmonic state weights, active+discarded
GLOBAL cell contributions, arbitrary complex mark tests, true
prime interval groups, Dirichlet hDir and k-dependent rational
lift. This adds NO analytic hypotheses besides the genuine
exact Fourier-frequency lift, which relates the very same
rational+Mellin kernel to its actual Fourier form.
It is still on ONE source/target dyad pair under explicit C196
side conditions; all-dyad / all-mode uniform instantiation,
B signed memory transfer and full Green64 remain separate. -/
theorem source_original_probe_true_full_dyadic_fourier_major_L2_434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
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
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (ζ beta theta : ℝ) (k Nshift : ℤ)
      (hLift : -(k:ℝ)*theta = (u:ℝ)/(r:ℝ)+beta-(Nshift:ℝ))
      (Uscale Vscale S : ℝ)
      (hUscale : 0 ≤ Uscale) (hVscale : 0 ≤ Vscale)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hDir : |beta| *(Uscale*Vscale) ≤ 2*S/(r:ℝ))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4)
      (sourceTest targetTest :
        SourceOriginalVariableBIGState434
          (fun g : G => {p : ℕ // p ∈ P g})
          (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ),
      let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
      let t : G → ℕ := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
      let prime : (g : G) → BP g → ℕ := fun g p => p.val
      let mu := sourceOriginalJointHarmonicMu434 BP prime V
      let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
      let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
      let gateSource : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun s =>
          (∃ jB ∈ activeB, sourceOriginalLiteralLogCell434 hB jB
            (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
              (fun g i => (s g i).val))) ∧
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
      let gateTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun v =>
          (∃ jA ∈ activeA, sourceOriginalLiteralLogCell434 hA jA
            (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
              (fun g i => (v g i).val))) ∧
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
      let dyadSource : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun s => (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
      let dyadTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
        fun v => (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
      let nA := (sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card
      let nB := (sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card
      let droppedLoss : ℝ := 2*((nA+nB:ℕ):ℝ)*xi
      let err : (SourceOriginalVariableBIGState434 BP t) ×
                (SourceOriginalVariableBIGState434 BP t) → ℂ :=
        fun ab => sourceOriginalProbeSignedMajorFourierError434
          J ell m hmJ ν P V Q hA hB xi ζ theta k
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val)
      let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
      ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                    (SourceOriginalVariableBIGState434 BP t),
        ((sourceOriginalVariableBIGMass434 BP t mu ab.1 *
           sourceOriginalVariableBIGMass434 BP t mu ab.2 :ℝ):ℂ) *
          star (sourceTest ab.1) * targetTest ab.2 *
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then err ab else 0))‖^2 ≤
      2*(eps^2+droppedLoss) *
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  obtain ⟨K,Y,hK,hMain⟩ :=
    source_original_probe_full_dyadic_major_L2_unconditional434
      Cq Cxi Cs C4 gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q hBIGA hBIGB hA hB xi hhA hhB hxi
    L hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB r hr hrQ u ζ beta theta k Nshift hLift
    Uscale Vscale S hUscale hVscale hS hSscale hDir hC4
    hDeltaLe hWidth hWidth1 hZeta sourceTest targetTest
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let dyadSource : X → Prop := fun s =>
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
  let dyadTarget : X → Prop := fun v =>
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
  let nA := (sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA).card
  let nB := (sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB).card
  let droppedLoss : ℝ := 2*((nA+nB:ℕ):ℝ)*xi
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
  let bound : ℝ :=
    2*(eps^2+droppedLoss)*
      sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
      sourceOriginalVariableBIGEnergy434 BP t mu targetTest
  have hRational := hMain J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi
    L hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB r hr hrQ u ζ beta
    Uscale Vscale S hUscale hVscale hS hSscale
    hDir hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  have hRationalForTransport :
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then
            sourceOriginalProbeSignedMajorSlowError434
              J ell m hmJ ν P V Q hA hB xi
              r hr u ζ beta
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤ bound := by
    exact hRational
  have hFourier :
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if dyadSource ab.1 ∧ dyadTarget ab.2 then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤ bound :=
    by
      simpa only [source_original_true_signed_major_fourier_error_eq434
        J ell m hmJ ν P V Q hA hB xi r hr u ζ beta theta k Nshift hLift]
        using hRationalForTransport
  exact hFourier
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalDyadicAllFrequencies -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option stderrAsMessages false
set_option maxHeartbeats 44000000

/-- ORIGINAL signed physical comparison on one ACTUAL coarse rectangle
at EVERY Fourier frequency, with full label-dependent endpoint tests.
Major and minor alternatives are proved and instantiated, not assumed.
The explicit aligned mesh and retention budget have uniform thresholds.
Global dyad summation, the pattern family and Memory remain separate. -/
theorem eventually_source_original_CANONICAL_DYADIC_ALL_FREQUENCIES434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D) :
    ∃ Kout Y0 : ℝ, 0 ≤ Kout ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (sA sB : ℕ)
      (vTupleA : SourceOriginalGramPrimeTuple434 SA)
      (vTupleB : SourceOriginalGramPrimeTuple434 SB)
      (hTupleA : sourceOriginalGramPrimeProduct434 SA vTupleA ∈
        Finset.Ico (2^sA) (2^(sA+1)))
      (hTupleB : sourceOriginalGramPrimeProduct434 SB vTupleB ∈
        Finset.Ico (2^sB) (2^(sB+1)))
      (hQlower : L^D ≤ (Qchar:ℝ)),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : β) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (fun g i => (v g i).val)
    let AW := Finset.Ico (2^sA) (2^(sA+1))
    let BW := Finset.Ico (2^sB) (2^(sB+1))
    ∀ (sourceTest targetTest : X → ℂ),
    let ES : ℝ := ∑ s : X, if projS s ∈ BW then w s*‖sourceTest s‖^2 else 0
    let ET : ℝ := ∑ v : X, if projT v ∈ AW then w v*‖targetTest v‖^2 else 0
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) * star (sourceTest ab.1)*targetTest ab.2 *
        (if projS ab.1 ∈ BW ∧ projT ab.2 ∈ AW then
          sourceOriginalProbeSignedMajorFourierError434
            J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
            (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
         else 0))‖^2 ≤ Kout*L^(-Bsave)*ES*ET := by
  run_tac do
    dbg_trace "ALL_FREQ_STAGE start"
  obtain ⟨K,Ymaj,hK,hMajor⟩ :=
    source_original_probe_true_full_dyadic_fourier_major_L2_434
      Cq Cxi Cs C4 gamma dscale Bsave hgamma hd hB
  run_tac do
    dbg_trace "ALL_FREQ_STAGE minor-event"
  obtain ⟨Ymin,hMinorEvent⟩ :=
    eventually_source_original_CANONICAL_DYADIC_PHYSICAL_minor434
      cfg Cq (Cxi:ℝ) gamma dscale (by positivity) hgamma hd
  let Kout : ℝ := 4252+2*(3*(K/cfg.vmin)+2)^2
  have hKout : 0 ≤ Kout := by dsimp [Kout]; positivity
  refine ⟨Kout,max Ymaj Ymin,hKout,?_⟩
  have hDecay : ∀ᶠ L : ℝ in atTop, K/cfg.vmin ≤ L^(Bsave+(Cq:ℝ)) :=
    (tendsto_rpow_atTop (by positivity : 0 < Bsave+(Cq:ℝ))).eventually
      (eventually_ge_atTop (K/cfg.vmin))
  run_tac do
    dbg_trace "ALL_FREQ_STAGE filter"
  filter_upwards [hMinorEvent,
    eventually_source_original_ACTUAL_coarse_dirichlet434 cfg dscale D hd hD,
    eventually_source_original_aligned_mesh_bounds434 H hH,
    eventually_source_original_aligned_discarded_budget434
      cfg.C0 dscale H (Cxi:ℝ) Bsave cfg.hC0 hd hH hDropBudget cfg.tmax,
    hDecay,eventually_ge_atTop (192:ℝ)]
    with L hMinor hDirichlet hMesh hDrop hKlarge hL192
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta
    sA sB vTupleA vTupleB hTupleA hTupleB hQlower
  intro sourceTest targetTest
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : β) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (fun g i => (v g i).val)
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let M : ℕ := 2^sA
  let N : ℕ := 2^sB
  let AW := Finset.Ico (2^sA) (2^(sA+1))
  let BW := Finset.Ico (2^sB) (2^(sB+1))
  let ES : ℝ := ∑ s : X, if projS s ∈ BW then w s*‖sourceTest s‖^2 else 0
  let ET : ℝ := ∑ v : X, if projT v ∈ AW then w v*‖targetTest v‖^2 else 0
  let error : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  let Rval : ℂ := ∑ ab : X × X,
    ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*targetTest ab.2*
    (if projS ab.1 ∈ BW ∧ projT ab.2 ∈ AW then error ab else 0)
  change ‖Rval‖^2 ≤ Kout*L^(-Bsave)*ES*ET
  have hVpos (g : β) : 0 < d.Vbig g := cfg.hv.trans_le (d.hVbig g)
  have hw (v : X) : 0 ≤ w v := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun p : BP g => prime g p) (d.Vbig g) (hVpos g) p
  run_tac do
    dbg_trace "ALL_FREQ_STAGE local-energies"
  have hES : 0 ≤ ES := by
    apply Finset.sum_nonneg
    intro s hs
    split_ifs
    · exact mul_nonneg (hw s) (sq_nonneg _)
    · exact le_rfl
  have hET : 0 ≤ ET := by
    apply Finset.sum_nonneg
    intro v hv
    split_ifs
    · exact mul_nonneg (hw v) (sq_nonneg _)
    · exact le_rfl
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hUpperA (n : ℕ) (hn : n ∈ AW) : (n:ℝ) ≤ 2*(M:ℝ) := by
    have hh := (Finset.mem_Ico.mp hn).2.le
    have hh' : n ≤ 2*M := by simpa only [M,pow_succ,Nat.mul_comm] using hh
    exact_mod_cast hh'
  have hUpperB (n : ℕ) (hn : n ∈ BW) : (n:ℝ) ≤ 2*(N:ℝ) := by
    have hh := (Finset.mem_Ico.mp hn).2.le
    have hh' : n ≤ 2*N := by simpa only [N,pow_succ,Nat.mul_comm] using hh
    exact_mod_cast hh'
  run_tac do
    dbg_trace "ALL_FREQ_STAGE dyad-witnesses"
  have hWindowA : (M:ℝ) ≤ (sourceOriginalGramPrimeProduct434 SA vTupleA:ℝ) ∧
      (sourceOriginalGramPrimeProduct434 SA vTupleA:ℝ) ≤ 2*(M:ℝ) :=
    ⟨by exact_mod_cast (Finset.mem_Ico.mp hTupleA).1,hUpperA _ hTupleA⟩
  have hWindowB : (N:ℝ) ≤ (sourceOriginalGramPrimeProduct434 SB vTupleB:ℝ) ∧
      (sourceOriginalGramPrimeProduct434 SB vTupleB:ℝ) ≤ 2*(N:ℝ) :=
    ⟨by exact_mod_cast (Finset.mem_Ico.mp hTupleB).1,hUpperB _ hTupleB⟩
  run_tac do
    dbg_trace "ALL_FREQ_STAGE dirichlet"
  obtain ⟨a,r,beta,hr,hcop,hApprox,hBeta,hSlow,hCap,hCases⟩ :=
    @hDirichlet ι β instI instDI instB instDB x Y Hprime d
      blockA blockB m hm ν hPattern hTbLower hTbUpper
      vTupleA vTupleB M N hM hN hWindowA hWindowB theta k Qchar hQlower
  run_tac do
    dbg_trace "ALL_FREQ_STAGE dirichlet-obtained"
  rcases hCases with hMajorCase | ⟨hMinorCase,hR,hNlarge,hMlarge,hMNlarge⟩
  · let eps : ℝ := (3*(K/cfg.vmin)+2)*L^(-Bsave)
    let nA := (sourceOriginalCandidateLogCells434 SA hA).card
    let nB := (sourceOriginalCandidateLogCells434 SB hB).card
    let drop : ℝ := 2*((nA+nB:ℕ):ℝ)*xi
    let budget : ℝ := 2*(eps^2+drop)
    run_tac do
      dbg_trace "ALL_FREQ_STAGE major-positivity"
    have hDrop0 : 0 ≤ drop :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (nA+nB))) hxi.le
    have hBudget0 : 0 ≤ budget :=
      mul_nonneg (by norm_num) (add_nonneg (sq_nonneg eps) hDrop0)
    run_tac do
      dbg_trace "ALL_FREQ_STAGE major-drop"
    have hDropBound : drop ≤ L^(-Bsave) := by
      have hh := hDrop d.hBigGroups m hm ν d.Tb
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
      simpa only [drop,nA,nB,SA,SB,hMeshA,hMeshB,hXiExact] using hh
    have hDelta : (K/cfg.vmin)*L^(-(Bsave+(Cq:ℝ))) ≤ 1 := by
      rw [Real.rpow_neg hLp.le,← div_eq_mul_inv]
      exact (div_le_one (Real.rpow_pos_of_pos hLp _)).2 hKlarge
    have hWidth : hA+hB ≤ L^(-(Bsave+((4*Cq+C4:ℕ):ℝ))) := by
      calc
        _ ≤ L^(-H) := by simpa only [hMeshA,hMeshB] using hMesh.2.2.1
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hWidth0 : hA+hB ≤ L^(-H) := by
      simpa only [hMeshA,hMeshB] using hMesh.2.2.1
    have hWidth1 : hA+hB ≤ 1 := hWidth0.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith))
    have hSscale : L^(D+dscale+2) ≤ L^Cs := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL hCs
    have hDir : |beta| *((M:ℝ)*(N:ℝ)) ≤ 2*L^(D+dscale+2)/(r:ℝ) := by
      have hrp : 0 < (r:ℝ) := by exact_mod_cast hr
      have hp := Real.rpow_nonneg hLp.le (D+dscale+2)
      exact hSlow.trans (by apply (div_le_div_iff_of_pos_right hrp).2; linarith)
    let cutS : X → Prop := fun s => (projS s:ℝ) ≤ 2*(N:ℝ)
    let cutT : X → Prop := fun v => (projT v:ℝ) ≤ 2*(M:ℝ)
    run_tac do
      dbg_trace "ALL_FREQ_STAGE major-upper"
    have hUpper (ff gg : X → ℂ) :
        ‖(∑ ab : X × X, ((w ab.1*w ab.2:ℝ):ℂ)*star (ff ab.1)*gg ab.2*
          (if cutS ab.1 ∧ cutT ab.2 then error ab else 0))‖^2 ≤
        (Real.sqrt budget)^2*(∑ s : X,w s*‖ff s‖^2)*(∑ v : X,w v*‖gg v‖^2) := by
      rw [Real.sq_sqrt hBudget0]
      run_tac do
        dbg_trace "ALL_FREQ_STAGE major-application"
      have hh := hMajor (G := β) J ell m hmJ ν d.Tb d.Vbig hVbig cfg.vmin cfg.hv d.hVbig
        Qchar
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hBIG z.val.1 p hp⟩)
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hBIG z.val.1 p hp⟩)
        hA hB xi hhA hhB hxi L hL192
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
        (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
        hLdyad hQchar hXipoly iA iB uA vA uB vB huA huB huvA huvB hvA hvB
        huLargeA huLargeB huBIGA huBIGB
        ((le_max_left _ _).trans hYA) ((le_max_left _ _).trans hYB)
        hBandA hBandB r hr hMajorCase a ζ beta theta k 0 (by simpa using hApprox)
        (M:ℝ) (N:ℝ) (L^(D+dscale+2)) (by positivity) (by positivity)
        (Real.rpow_nonneg hLp.le _) hSscale hDir hC4 hDelta hWidth hWidth1 hZeta ff gg
      simpa only [sourceOriginalVariableBIGEnergy434,Complex.normSq_eq_norm_sq]
        using hh
    let idxS : X → Bool := fun s => decide (projS s ∈ BW)
    let idxT : X → Bool := fun v => decide (projT v ∈ AW)
    have hCutS (s : X) (hs : idxS s=true) : cutS s :=
      hUpperB _ (of_decide_eq_true hs)
    have hCutT (v : X) (hv : idxT v=true) : cutT v :=
      hUpperA _ (of_decide_eq_true hv)
    run_tac do
      dbg_trace "ALL_FREQ_STAGE exact-dyad-localization"
    have hLocal := source_original_finite_dyad_cutoff_to_exact_L2_sq434
      (X := X) (Y := X) (I := Bool) (J := Bool)
      w w idxS idxT true true cutS cutT hCutS hCutT error
      (Real.sqrt budget) hUpper sourceTest targetTest
    run_tac do
      dbg_trace "ALL_FREQ_STAGE exact-dyad-bound"
    have hSaved : ‖Rval‖^2 ≤ budget*ES*ET := by
      simpa only [idxS,idxT,decide_eq_true_eq,Real.sq_sqrt hBudget0] using hLocal
    run_tac do
      dbg_trace "ALL_FREQ_STAGE major-budget"
    have hPow : (L^(-Bsave))^2 ≤ L^(-Bsave) := by
      have hp := Real.rpow_nonneg hLp.le (-Bsave)
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith : -Bsave ≤ 0)
      nlinarith only [mul_nonneg hp (sub_nonneg.mpr hle)]
    have hEpsBound : eps^2 ≤ (3*(K/cfg.vmin)+2)^2*L^(-Bsave) := by
      dsimp [eps]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hPow (sq_nonneg _)
    have hBudget : budget ≤ Kout*L^(-Bsave) := by
      dsimp [budget,Kout]
      have hp := Real.rpow_nonneg hLp.le (-Bsave)
      nlinarith only [hEpsBound,hDropBound,hp]
    exact hSaved.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBudget hES) hET)
  · have hXiReal : xi⁻¹ ≤ L^(Cxi:ℝ) := by
      simpa only [Real.rpow_natCast] using hXipoly
    run_tac do
      dbg_trace "ALL_FREQ_STAGE minor-application"
    have hSaved := hMinor x Y Hprime d sep hVbig blockA blockB hDisjoint
      m hm ν hPattern Qchar hA hB hhA hhB xi hxi hXiReal hQchar hLdyad hBIG J ell hmJ
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB
      ((le_max_right _ _).trans hYA) ((le_max_right _ _).trans hYB)
      hBandA hBandB ζ M N M N hM hN a r beta theta k hApprox hr hcop hBeta
      le_rfl le_rfl D Bsave hR hNlarge hMlarge hMNlarge Cfactor hExponent hMinorBudget
      (Nat.ceil (4*L^H)) (Nat.ceil (4*L^H)) hMesh.1 hMesh.1
      hMeshA hMeshB sA sB rfl rfl rfl rfl sourceTest targetTest
    run_tac do
      dbg_trace "ALL_FREQ_STAGE minor-result"
    have hMain : ‖Rval‖^2 ≤ 4250*L^(-Bsave)*ES*ET := hSaved
    have hKbound : (4250:ℝ) ≤ Kout := by
      dsimp [Kout]
      nlinarith only [sq_nonneg (3*(K/cfg.vmin)+2)]
    exact hMain.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKbound (Real.rpow_nonneg hLp.le _)) hES) hET)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalGlobalComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 44000000

/-- The LITERAL original signed comparison on the COMPLETE physical law,
for every Fourier frequency and arbitrary full-mark endpoint tests.
The local major/minor estimate is PROVED and every actual coarse dyad
is summed with its exact energy partition. No fine-cell pair cost.
Physical source admissibility remains explicit; Memory remains separate. -/
theorem eventually_source_original_CANONICAL_GLOBAL_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H Bgoal : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D)
    (hSumBudget : Bgoal+(2*dscale+4)+2 ≤ Bsave) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (hQlower : L^D ≤ (Qchar:ℝ)),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : β) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    ∀ (sourceTest targetTest : X → ℂ),
    let ES : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
    let ET : ℝ := ∑ v : X, w v*‖targetTest v‖^2
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) * star (sourceTest ab.1)*targetTest ab.2 *
        (sourceOriginalProbeSignedMajorFourierError434
            J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
            (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
         ))‖^2 ≤ L^(-Bgoal)*ES*ET := by
  obtain ⟨K,Y0,hK,hLocalEvent⟩ :=
    eventually_source_original_CANONICAL_DYADIC_ALL_FREQUENCIES434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H
      hgamma hd hD hB hH hCs hC4 hWidthBudget hDropBudget hExponent hMinorBudget
  refine ⟨Y0,?_⟩
  filter_upwards [hLocalEvent,
    eventually_source_original_coarse_dyad_pair_count434
      cfg.C0 dscale cfg.hC0 hd cfg.tmax,
    eventually_ge_atTop (max (1:ℝ) K)] with L hLocal hCount hLarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hLarge
  have hLp : 0 < L := by linarith
  have hKlarge : K ≤ L^2 := by
    have hk := (le_max_right (1:ℝ) K).trans hLarge
    nlinarith
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower
  intro sourceTest targetTest
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : β) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (fun g i => (v g i).val)
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let CA := sourceOriginalCandidateLogCells434 SA (Real.log 2)
  let CB := sourceOriginalCandidateLogCells434 SB (Real.log 2)
  let idxS : X → ℤ := fun s => sourceOriginalLiteralLogCellIndex434 (Real.log 2) (projS s)
  let idxT : X → ℤ := fun v => sourceOriginalLiteralLogCellIndex434 (Real.log 2) (projT v)
  let ESource : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
  let ETarget : ℝ := ∑ v : X, w v*‖targetTest v‖^2
  let error : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  let z : X × X → ℂ := fun ab =>
    ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*targetTest ab.2*error ab
  let coeff : ℝ := K*L^(-Bsave)
  have hCoeff : 0 ≤ coeff := mul_nonneg hK (Real.rpow_nonneg hLp.le _)
  have hVpos (g : β) : 0 < d.Vbig g := cfg.hv.trans_le (d.hVbig g)
  have hw (v : X) : 0 ≤ w v := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun p : BP g => prime g p) (d.Vbig g) (hVpos g) p
  have hES : 0 ≤ ESource := Finset.sum_nonneg
    (fun s _ => mul_nonneg (hw s) (sq_nonneg _))
  have hET : 0 ≤ ETarget := Finset.sum_nonneg
    (fun v _ => mul_nonneg (hw v) (sq_nonneg _))
  have hPositive (g : β) (p : ℕ) (hp : p ∈ d.Tb g) : 0 < p :=
    (d.hTbPrime g p hp).pos
  have hOutputs (s : X) : 0 < projS s ∧ 0 < projT s :=
    source_original_actual_free_outputs_positive434
      J ell m hmJ ν d.Tb hPositive s
  have hEach : ∀ ij ∈ CB.product CA,
      ‖(∑ ab : X × X,
        if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2 then z ab else 0)‖^2 ≤
      (Real.sqrt coeff)^2*
        (∑ s : X, if idxS s=ij.1 then w s*‖sourceTest s‖^2 else 0)*
        (∑ v : X, if idxT v=ij.2 then w v*‖targetTest v‖^2 else 0) := by
    intro ij hij
    obtain ⟨sB,hsB,vB0,hvB0⟩ := source_original_actual_coarse_candidate_witness434
      SB (fun z p hp => hPositive z.val.1 p hp) ij.1 (Finset.mem_product.mp hij).1
    obtain ⟨sA,hsA,vA0,hvA0⟩ := source_original_actual_coarse_candidate_witness434
      SA (fun z p hp => hPositive z.val.1 p hp) ij.2 (Finset.mem_product.mp hij).2
    have hgateS (s : X) :
        idxS s=ij.1 ↔ projS s ∈ Finset.Ico (2^sB) (2^(sB+1)) := by
      rw [← hsB]
      exact source_original_log_two_cell_iff_dyad434 _ _ (hOutputs s).1
    have hgateT (v : X) :
        idxT v=ij.2 ↔ projT v ∈ Finset.Ico (2^sA) (2^(sA+1)) := by
      rw [← hsA]
      exact source_original_log_two_cell_iff_dyad434 _ _ (hOutputs v).2
    have hh := hLocal x Y Hprime d sep hVbig blockA blockB hDisjoint
      m hm ν hPattern Qchar hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
      hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta
      sA sB vA0 vB0 hvA0 hvB0 hQlower sourceTest targetTest
    change ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*targetTest ab.2*
        (if projS ab.1 ∈ Finset.Ico (2^sB) (2^(sB+1)) ∧
            projT ab.2 ∈ Finset.Ico (2^sA) (2^(sA+1))
         then error ab else 0))‖^2 ≤
      coeff*
        (∑ s : X, if projS s ∈ Finset.Ico (2^sB) (2^(sB+1))
          then w s*‖sourceTest s‖^2 else 0)*
        (∑ v : X, if projT v ∈ Finset.Ico (2^sA) (2^(sA+1))
          then w v*‖targetTest v‖^2 else 0) at hh
    simpa only [hgateS,hgateT,Real.sq_sqrt hCoeff,mul_ite,mul_zero,z] using hh
  have hSum := source_original_probe_true_physical_dyad_sum_L2434
    J ell m hmJ ν d.Tb d.Vbig hVpos sourceTest targetTest z (Real.sqrt coeff) hEach
  have hSummed : ‖(∑ ab : X × X,z ab)‖^2 ≤
      ((CB.product CA).card:ℝ)*coeff*ESource*ETarget := by
    simpa only [Real.sq_sqrt hCoeff,sourceOriginalVariableBIGEnergy434,
      Complex.normSq_eq_norm_sq] using hSum
  have hCard : ((CB.product CA).card:ℝ) ≤ L^(2*dscale+4) :=
    hCount d.hBigGroups m hm ν d.Tb
      (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
      (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hTbUpper z.val.1 p hp⟩)
  have hCoeffBound : ((CB.product CA).card:ℝ)*coeff ≤ L^(-Bgoal) := by
    calc
      _ ≤ L^(2*dscale+4)*coeff := mul_le_mul_of_nonneg_right hCard hCoeff
      _ ≤ L^(2*dscale+4)*(L^2*L^(-Bsave)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hKlarge (Real.rpow_nonneg hLp.le _))
          (Real.rpow_nonneg hLp.le _)
      _ = L^(2*dscale+6-Bsave) := by
        rw [← Real.rpow_two,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ L^(-Bgoal) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  change ‖(∑ ab : X × X,z ab)‖^2 ≤ L^(-Bgoal)*ESource*ETarget
  exact hSummed.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCoeffBound hES) hET)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalOrientedDivisor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Literal positive original edge scalar, including its complex K. -/
theorem source_original_edge_scalar_positive_fourier434
    (K : ℂ) (ζ theta : ℝ) (k : ℤ) (n : ℕ) :
    originalEdgeScalar K ζ theta n 1 k =
      K * (Green64SourceC6.integerPhase ((k:ℝ)*theta) (n:ℤ) *
        sourceOriginalPureMellinPhase434 ζ n) := by
  have hm : Complex.exp (Complex.I*(ζ:ℂ)*Complex.log (n:ℂ)) =
      sourceOriginalPureMellinPhase434 ζ n := by
    rw [← Complex.natCast_log]
    simp only [sourceOriginalPureMellinPhase434,Complex.ofReal_mul,mul_assoc]
  have hp : originalReturnPhase theta 1 k n =
      Green64SourceC6.integerPhase ((k:ℝ)*theta) (n:ℤ) := by
    unfold originalReturnPhase Green64SourceC6.integerPhase
    congr 1
    push_cast
    ring
  unfold originalEdgeScalar originalOrientedKernel
  rw [if_pos rfl,hm,hp]
  ring

/-- Negative original orientation conjugates the WHOLE scalar, including K. -/
theorem source_original_edge_scalar_negative_conjugate434
    (K : ℂ) (ζ theta : ℝ) (k : ℤ) (n : ℕ) :
    originalEdgeScalar K ζ theta n (-1) k =
      star (originalEdgeScalar K ζ theta n 1 k) := by
  have hp : originalReturnPhase theta (-1) k n =
      star (originalReturnPhase theta 1 k n) := by
    unfold originalReturnPhase
    change _ = (starRingEnd ℂ) (Complex.exp _)
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_mul,map_natCast,map_intCast,map_ofNat,map_one,
      Complex.conj_ofReal,Complex.conj_I]
    ring
  unfold originalEdgeScalar originalOrientedKernel
  simp only [show (-1:ℤ) ≠ 1 by norm_num,if_false,if_true,star_mul,hp]
  ring

/-- A frozen positive SMALL/shared divisor is only a unit Mellin factor
and a frequency rescaling. This retains the literal physical divisor. -/
theorem source_original_edge_scalar_positive_divisor434
    (K : ℂ) (ζ theta : ℝ) (k : ℤ) (c n : ℕ)
    (hc : 0<c) (hn : 0<n) :
    originalEdgeScalar K ζ theta (c*n) 1 k =
      sourceOriginalPureMellinPhase434 ζ c *
        (K * (Green64SourceC6.integerPhase
          (-(k:ℝ)*(-(c:ℝ)*theta)) (n:ℤ) *
          sourceOriginalPureMellinPhase434 ζ n)) := by
  rw [source_original_edge_scalar_positive_fourier434,
    source_original_pure_mellin_product_factor434 ζ c n hc hn]
  have hp : Green64SourceC6.integerPhase ((k:ℝ)*theta) ((c*n:ℕ):ℤ) =
      Green64SourceC6.integerPhase (-(k:ℝ)*(-(c:ℝ)*theta)) (n:ℤ) := by
    unfold Green64SourceC6.integerPhase
    congr 1
    push_cast
    ring
  rw [hp]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## IntegerPhysicalAdjoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local instance b650AdjointFrameFintype434 :
    Fintype (MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- Reversal of an actual physical edge is an exact iff, with all
auxiliary bans, shared slots, and original signed integer positions. -/
theorem b650_integer_frame_reverse_guard434 (positions : Finset ℤ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions (-1) k x y
      (b650SwapFrame434 BP J ell m patterns f) ↔
    b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions 1 k y x f := by
  constructor
  · rintro ⟨ho,hk,ha,hs,hpos⟩
    have hshare := (b650_frame_shared_reverse434 SP smallMod BP bigMod J ell m patterns y.val.2 x.val.2 f).mp hs
    have hd := b650_frame_divisor_reverse434 SP smallMod BP bigMod J ell m patterns y.val.2 x.val.2 f hshare
    refine ⟨Or.inl rfl,hk,?_,hshare,?_⟩
    · intro g j i
      exact ⟨(ha g j i).2,(ha g j i).1⟩
    · rw [hd] at hpos
      simp only [neg_mul,one_mul] at hpos ⊢
      omega
  · rintro ⟨ho,hk,ha,hs,hpos⟩
    have hshare := (b650_frame_shared_reverse434 SP smallMod BP bigMod J ell m patterns y.val.2 x.val.2 f).mpr hs
    have hd := b650_frame_divisor_reverse434 SP smallMod BP bigMod J ell m patterns y.val.2 x.val.2 f hs
    refine ⟨Or.inr rfl,hk,?_,hshare,?_⟩
    · intro g j i
      exact ⟨(ha g j i).2,(ha g j i).1⟩
    · rw [hd]
      simp only [neg_mul,one_mul] at hpos ⊢
      omega

/-- Actual physical row reversal conjugates the WHOLE multiplier. The
endpoint swap is before conjugation; q damping and all real source laws
are retained exactly, without an estimated or idealized adjoint. -/
theorem b650_integer_frame_adjoint434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta (-1) k x y (b650SwapFrame434 BP J ell m patterns f) =
    star (b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta 1 k y x f) := by
  unfold b650IntegerFrameScalar434
  by_cases ha : b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions 1 k y x f
  · have hb := (b650_integer_frame_reverse_guard434 SP smallMod BP bigMod J ell m patterns positions k x y f).mpr ha
    rw [ite_eq_left hb,ite_eq_left ha]
    have hd := b650_frame_divisor_reverse434 SP smallMod BP bigMod J ell m patterns y.val.2 x.val.2 f ha.2.2.2.1
    have hw := b650_real_frame_weight_reverse434 SP smallMod BP bigMod J ell m patterns q Vsmall Vbig y.val.2 x.val.2 f
    rw [hd,hw]
    simp only [memoryOrientationK,show (-1:ℤ)≠1 by norm_num,ite_false,ite_true,b650SwapFrame434]
    rw [source_original_edge_scalar_negative_conjugate434]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    exact mul_comm _ _
  · have hb : ¬ b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions (-1) k x y
        (b650SwapFrame434 BP J ell m patterns f) :=
      fun h => ha ((b650_integer_frame_reverse_guard434 SP smallMod BP bigMod J ell m patterns positions k x y f).mp h)
    rw [ite_eq_right hb,ite_eq_right ha,star_zero]

/-- Complete source physical matrix on a finite signed integer window.
It sums ALL original patterns/auxiliary draws/four permutations, and
all actual physical target mark lists. States have uniform original
mass b650IntegerStateMass434; thus the row matrix is unchanged under
the isometric conversion to Euclidean coordinates. -/
def b650IntegerPhysicalMatrix434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ) :
    Matrix (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
      (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ℂ :=
  fun x y => ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta o k x y f

/-- The complete actual backward row IS the Hermitian adjoint matrix,
with no normalization, detailed-balance, positivity or adjoint premise. -/
theorem b650_integer_matrix_adjoint434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) :
    b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta (-1) k =
    (b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta 1 k).conjTranspose := by
  ext x y
  let e : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns ≃
      MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns :=
    { toFun := b650SwapFrame434 BP J ell m patterns
      invFun := b650SwapFrame434 BP J ell m patterns
      left_inv := b650_swap_frame_involutive434 BP J ell m patterns
      right_inv := b650_swap_frame_involutive434 BP J ell m patterns }
  change (∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta (-1) k x y f) =
    star (∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
      b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta 1 k y x f)
  calc
    _ = ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
          q Vsmall Vbig Knu zeta (-1) k x y (e f) := (Equiv.sum_comp e _).symm
    _ = ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        star (b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
          q Vsmall Vbig Knu zeta 1 k y x f) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact b650_integer_frame_adjoint434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta k x y f
    _ = _ := (star_sum _ _).symm
end Green64FullPhysicalE

end

end

/-! ## EuclideanPhysicalRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

variable {X : Type} [Fintype X] [DecidableEq X]

/-- All states at the given physical position, in Euclidean coordinates.
There is no division by the cardinality or norm of the mark fibre. -/
def b650PositionRoot434 (pos : X → ℤ) (mu : ℝ) (n : ℤ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => if pos x=n then (Real.sqrt mu:ℂ) else 0)

/-- Exact conversion of the original constant physical state mass to
Euclidean coordinates. It retains every ordered mark state twice in
the endpoint sums and introduces NO Haar prime denominator. -/
theorem b650_position_root_pairing434 (pos : X → ℤ) (mu : ℝ) (hmu : 0 ≤ mu)
    (n : ℤ) (M : Matrix X X ℂ) :
    inner ℂ (b650PositionRoot434 pos mu n)
      (M.toEuclideanLin (b650PositionRoot434 pos mu n)) =
    (mu:ℂ) * ∑ x : X, (if pos x=n then (1:ℂ) else 0) *
      (M.mulVec (fun y => if pos y=n then (1:ℂ) else 0)) x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin,Matrix.toLpLin_apply,b650PositionRoot434,
    WithLp.ofLp_toLp,Matrix.mulVec,dotProduct,Pi.star_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxn : pos x=n <;> by_cases hyn : pos y=n
  · simp only [hxn,hyn,ite_true,Complex.star_def,Complex.conj_ofReal,one_mul,mul_one]
    have hs : (Real.sqrt mu:ℂ)*(Real.sqrt mu:ℂ)=(mu:ℂ) := by
      rw [← Complex.ofReal_mul,Real.mul_self_sqrt hmu]
    calc
      _ = ((Real.sqrt mu:ℂ)*(Real.sqrt mu:ℂ))*M x y := by ring
      _ = _ := by rw [hs]
  · simp [hxn,hyn]
  · simp [hxn,hyn]
  · simp [hxn,hyn]

/-- The true positive operator moment agrees with the matrix moment
under the same Euclidean realization, for every finite carrier. -/
theorem b650_euclidean_positive_moment434 (M : Matrix X X ℂ) (R : ℕ) :
    (M.toEuclideanLin.comp M.toEuclideanLin.adjoint)^R =
      ((M*M.conjTranspose)^R).toEuclideanLin := by
  rw [Matrix.toEuclideanLin,Matrix.toLpLin_pow,Matrix.toLpLin_mul_same]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
end Green64FullPhysicalE

end

end

