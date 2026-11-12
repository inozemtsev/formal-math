module

public import Green64.Library.Correlation.Part068
public import Green64.Library.Weights.Part033

@[expose] public section

/-!
# Weights / LiteralDyadicEnvelope

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralDyadicEnvelope -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Exact original harmonic dyadic normalization at the real position
w/D. No integrality of w/D or a rescaled substitute profile is used. -/
theorem b598_literal_native_psi_over_w434
    (Z : ℝ) (D w : ℕ) (hZ : 0 < Z) (hD : 0 < D) (hw : 0 < w) :
    ‖sourceB578NativePsi434 ((w:ℝ)/(Z*(D:ℝ)))‖/(w:ℝ) =
      sourceCorrectedDyadicProfile ((w:ℝ)/(Z*(D:ℝ)))/(Z*(D:ℝ)) := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD
  have hwr : 0 < (w:ℝ) := by exact_mod_cast hw
  have hr : 0 < (w:ℝ)/(Z*(D:ℝ)) := div_pos hwr (mul_pos hZ hDr)
  have hp := source_corrected_dyadic_profile_range ((w:ℝ)/(Z*(D:ℝ)))
  change ‖(((w:ℝ)/(Z*(D:ℝ)):ℝ):ℂ)*
    (sourceCorrectedDyadicProfile ((w:ℝ)/(Z*(D:ℝ))):ℂ)‖/(w:ℝ) = _
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hr,abs_of_nonneg hp.1]
  field_simp

private theorem original_physical_cutoff_lower
    (L K U V : ℝ) (hL : 1 ≤ L) (hL32 : 2*Real.log 32 ≤ L) (hK : 0 ≤ K)
    (hUVlo : Real.exp L/4 ≤ U*V) (hUVhi : U*V ≤ 3*Real.exp L)
    (N j : ℕ) (hj : j ≤ N) (hN : (2:ℝ)^N ≤ 384*L^(89:ℝ))
    (D : ℕ) (hD : 0 < D) :
    Real.exp (L/2) ≤ 3*sourceCorrectedDyadicScale U V (L^K) j*(D:ℝ) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hd := source_native_original_dyad_bounds434 L K U V hL0 hUVlo hUVhi N j hj hN
  have hpow : 1 ≤ L^K := Real.one_le_rpow hL hK
  have he : 32*Real.exp (L/2) ≤ Real.exp L := by
    calc
      _ = Real.exp (Real.log 32+L/2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 32)]
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  have hZ : Real.exp (L/2) ≤ sourceCorrectedDyadicScale U V (L^K) j := by
    have hm := mul_le_mul_of_nonneg_left hpow (Real.exp_pos L).le
    nlinarith [hd.2.1]
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hmul := mul_le_mul_of_nonneg_left hD1 hd.1.le
  nlinarith [Real.exp_pos (L/2)]

/-- Native original dyadic physical envelope, with literal psi(w/(Z_jD))/w
and the exact full auxiliary product. Joint physical density cancels both
selected products before the original harmonic normalization removes D.
The bound is uniform over all original j,k and actual two Q arrays.
It is a positive budget, not comparison cancellation or RMS saving. -/
theorem eventually_b598_literal_dyadic_D61_envelope434
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
      (∑p∈b598PhysicalRows434 N D k,
        ‖(sourceB578NativePsi434 ((p.1:ℝ)/(Z*(D:ℝ)))/(p.1:ℂ)) *
          (primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)) *
          sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2‖) ≤
      96*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*
        (1+Real.log (3*Z*(D:ℝ)))^15 := by
  obtain ⟨C,hC,hbound⟩ := eventually_b598_literal_fixed_auxiliary_D61_envelope434 r m hr K0 hK0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (2*Real.log (32:ℝ))] with L hbnd hL1 hL32
  intro U V0 hUVlo hUVhi N0 j hj hN0 J hmJ blockA blockB hblocks nu hnu Q hA hB xi
    hhA hhB hxi aux haux k hk d b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy χ σ₀ σ₁ σ₀' σ₁'
  let P := sourceOriginalPAllActualBands r L
  let V := sourceNativeOriginalAllPMass434 r L
  let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
  let Z := sourceCorrectedDyadicScale U V0 (L^K0) j
  let N := ⌊3*Z*(D:ℝ)⌋₊
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
  let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
  let f := fun p : ℕ×ℕ =>
    ‖primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)‖ *
      ‖sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2‖
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hD : 0 < D := b601_original_aux_positive434 P
    (source_original_P_all_actual_band_prime r L) m nu aux haux
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD
  have hZ : 0 < Z := (source_native_original_dyad_bounds434 L K0 U V0 hL hUVlo hUVhi N0 j hj hN0).1
  have hZD : 0 < Z*(D:ℝ) := mul_pos hZ hDr
  have hY := original_physical_cutoff_lower L K0 U V0 hL1 hL32 hK0 hUVlo hUVhi N0 j hj hN0 D hD
  have hraw := hbnd J hmJ blockA blockB hblocks nu hnu Q hA hB xi hhA hhB hxi aux haux
    (3*Z*(D:ℝ)) hY k hk d b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy χ σ₀ σ₁ σ₀' σ₁'
  have hN : 0 < N := by
    have he : (1:ℝ) ≤ Real.exp (L/2) := Real.one_le_exp (by linarith)
    have hh : (1:ℕ) ≤ N := Nat.le_floor (by simpa using he.trans hY)
    omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNcap : (N:ℝ) ≤ 3*Z*(D:ℝ) := Nat.floor_le (by positivity)
  have hlogN : 0 ≤ 1+Real.log (N:ℝ) := by linarith [Real.log_nonneg hN1]
  have hlog : 1+Real.log (N:ℝ) ≤ 1+Real.log (3*Z*(D:ℝ)) := by
    linarith [Real.log_le_log hNr hNcap]
  have hCc : 0 ≤ C^(2*Fintype.card (sourceOriginalPAllGroupType r L)) := pow_nonneg (by linarith) _
  calc
    _ ≤ (1/(Z*(D:ℝ)))*(∑p∈b598PhysicalRows434 N D k,f p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hrow := b598_mem_physical_rows434.mp hp
      have hpsi : ‖sourceB578NativePsi434 ((p.1:ℝ)/(Z*(D:ℝ)))‖/(p.1:ℝ) ≤ 1/(Z*(D:ℝ)) := by
        rw [b598_literal_native_psi_over_w434 Z D p.1 hZ hD hrow.1.1]
        exact div_le_div_of_nonneg_right
          (source_corrected_dyadic_profile_range ((p.1:ℝ)/(Z*(D:ℝ)))).2 hZD.le
      simp only [norm_mul,norm_div,Complex.norm_natCast]
      dsimp only [f]
      have hh := mul_le_mul_of_nonneg_right hpsi
        (mul_nonneg (norm_nonneg (primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)))
          (norm_nonneg (sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2)))
      simpa only [norm_mul,norm_star,mul_assoc] using hh
    _ ≤ (1/(Z*(D:ℝ)))*(32*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*(N:ℝ)*
        (1+Real.log (N:ℝ))^15) := mul_le_mul_of_nonneg_left hraw (one_div_nonneg.mpr hZD.le)
    _ ≤ (1/(Z*(D:ℝ)))*(32*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*(3*Z*(D:ℝ))*
        (1+Real.log (3*Z*(D:ℝ)))^15) := by gcongr
    _ = _ := by
      change (1/(Z*(D:ℝ)))*(32*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*(3*Z*(D:ℝ))*
        (1+Real.log (3*Z*(D:ℝ)))^15) =
        96*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*(1+Real.log (3*Z*(D:ℝ)))^15
      field_simp [hZ.ne',hDr.ne']
      ring
end Green64Analytic.ShiftTwoTerminal

end

end

