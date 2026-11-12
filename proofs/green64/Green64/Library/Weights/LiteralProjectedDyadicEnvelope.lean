module

public import Green64.Library.Weights.LiteralDyadicEnvelope

@[expose] public section

/-!
# Weights / LiteralProjectedDyadicEnvelope

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralProjectedDyadicEnvelope -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The original pattern sign times the parity of ALL original P primes.
The parity exponent is the inherited physical exponent, not an independent
sign or a replacement ordinary-part parity. -/
def b598ActualAllPPatternPhase434 (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m) (n : ℕ) : ℂ :=
  (((-1:ℝ)^(nu.1.card+nu.2.card) *
    (-1:ℝ)^(sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands r L)) n):ℝ):ℂ)

/-- Literal original all-P pattern projector in the complete-family
coordinates used by this packet. B604 owns its BIG+SMALL reindex adapter. -/
def b598ActualAllPPatternProjector434 (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m) (n : ℕ) : ℂ :=
  (1-b598ActualAllPPatternPhase434 r L m nu n)/2

/-- Both genuine endpoint sign choices are combined before a norm.
This is the literal (00-10-01+11)/4 expression on the same physical row. -/
theorem b598_actual_allP_four_sign_before_norm434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (w wp : ℕ) (z : ℂ) :
    b598ActualAllPPatternProjector434 r L m nu w *
      b598ActualAllPPatternProjector434 r L m nu wp * z =
    (z-b598ActualAllPPatternPhase434 r L m nu w*z-
      b598ActualAllPPatternPhase434 r L m nu wp*z+
      b598ActualAllPPatternPhase434 r L m nu w*
        b598ActualAllPPatternPhase434 r L m nu wp*z)/4 := by
  unfold b598ActualAllPPatternProjector434
  ring

/-- Contractivity is used only for the absolute envelope, after the two
original projectors have remained together in the complex row sum. -/
theorem b598_actual_allP_projector_norm434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m) (n : ℕ) :
    ‖b598ActualAllPPatternProjector434 r L m nu n‖ ≤ 1 := by
  have hphase : ‖b598ActualAllPPatternPhase434 r L m nu n‖=1 := by
    unfold b598ActualAllPPatternPhase434
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_pow]
    norm_num
  unfold b598ActualAllPPatternProjector434
  rw [norm_div]
  have hh := norm_sub_le (1:ℂ) (b598ActualAllPPatternPhase434 r L m nu n)
  rw [hphase] at hh
  norm_num at hh ⊢
  linarith

/-- Original two-endpoint parity projection stays INSIDE the physical
sum and its outer norm. The sigma-one D61, true marked Knu, complete
auxiliary ban and literal dyadic profile have the same xi-free absolute
budget, uniformly for all j,k and both actual Q Fourier arrays. -/
theorem eventually_b598_literal_projected_dyadic_D61_envelope434
    (r m : ℕ) (hr : 1 ≤ r) (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (U V0 : ℝ),Real.exp L/4 ≤ U*V0 → U*V0 ≤ 3*Real.exp L →
      ∀ (N0 j : ℕ),j ≤ N0 → (2:ℝ)^N0 ≤ 384*L^(89:ℝ) →
      ∀ (J : ℕ) (hmJ : m ≤ J)
        (blockA blockB : Finset (sourceOriginalPAllGroupType r L))
        (_hblocks : Disjoint blockA blockB)
        (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m),
      nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      ∀ (Q : ℕ) (hA hB xi : ℝ),0 < hA → 0 < hB → 0 < xi →
      ∀ (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
      aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu (sourceOriginalPAllActualBands r L)) →
      ∀ k∈sourceCorrectedSmoothKSet (L^K0) (L^(89:ℝ)),
      ∀ (d : ℕ) (b b' : Fin (d+1)) (slot slot' : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
        (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
        (K K' : Finset ℕ) (a eta b0 : ℝ),
      Real.exp (Real.sqrt L) ≤ (Real.exp L)^a →
      ∀ (χ : DirichletCharacter ℂ k.natAbs) (σ₀ σ₁ σ₀' σ₁' : ℝ),
      let P := sourceOriginalPAllActualBands r L
      let V := sourceNativeOriginalAllPMass434 r L
      let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
      let Z := sourceCorrectedDyadicScale U V0 (L^K0) j
      let N := ⌊3*Z*(D:ℝ)⌋₊
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
      let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
        (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
      ‖∑p∈b598PhysicalRows434 N D k,
        b598ActualAllPPatternProjector434 r L m nu p.1 *
        b598ActualAllPPatternProjector434 r L m nu p.2 *
        ((sourceB578NativePsi434 ((p.1:ℝ)/(Z*(D:ℝ)))/(p.1:ℂ)) *
          (primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)) *
          sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2)‖ ≤
      96*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*
        (1+Real.log (3*Z*(D:ℝ)))^15 := by
  obtain ⟨C,hC,hbound⟩ := eventually_b598_literal_dyadic_D61_envelope434 r m hr K0 hK0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with L hh
  intro U V0 hUVlo hUVhi N0 j hj hN0 J hmJ blockA blockB hblocks nu hnu Q hA hB xi
    hhA hhB hxi aux haux k hk d b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy χ σ₀ σ₁ σ₀' σ₁'
  have hraw := hh U V0 hUVlo hUVhi N0 j hj hN0 J hmJ blockA blockB hblocks nu hnu
    Q hA hB xi hhA hhB hxi aux haux k hk d b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy
    χ σ₀ σ₁ σ₀' σ₁'
  let P := sourceOriginalPAllActualBands r L
  let V := sourceNativeOriginalAllPMass434 r L
  let D := sourceOriginalProbeDA434 m nu aux*sourceOriginalProbeDB434 m nu aux
  let Z := sourceCorrectedDyadicScale U V0 (L^K0) j
  let N := ⌊3*Z*(D:ℝ)⌋₊
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
  let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
  let term := fun p : ℕ×ℕ =>
    (sourceB578NativePsi434 ((p.1:ℝ)/(Z*(D:ℝ)))/(p.1:ℂ)) *
      (primeSlotCoreValue P F p.1*star (primeSlotCoreValue P F' p.2)) *
      sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2
  change (∑p∈b598PhysicalRows434 N D k,‖term p‖) ≤ _ at hraw
  change ‖∑p∈b598PhysicalRows434 N D k,
    b598ActualAllPPatternProjector434 r L m nu p.1*
      b598ActualAllPPatternProjector434 r L m nu p.2*term p‖ ≤ _
  calc
    _ ≤ ∑p∈b598PhysicalRows434 N D k,
      ‖b598ActualAllPPatternProjector434 r L m nu p.1 *
        b598ActualAllPPatternProjector434 r L m nu p.2 * term p‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply le_trans _ hraw
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul,norm_mul]
      have hproj := mul_le_mul
        (b598_actual_allP_projector_norm434 r L m nu p.1)
        (b598_actual_allP_projector_norm434 r L m nu p.2)
        (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
end Green64Analytic.ShiftTwoTerminal

end

end

