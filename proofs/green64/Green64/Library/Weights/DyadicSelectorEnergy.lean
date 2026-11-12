module

public import Green64.Library.Weights.OutsideAveragedMarkedLiftObstruction
public import Mathlib

@[expose] public section

/-!
# Weights / DyadicSelectorEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualDyadicSelectorEnergy -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000

/-- Literal real body of the original sourceCorrectedDyadicProfile.
The separate name avoids pretending that the old complete Fourier module
has already been ported. The source body and provenance are preserved. -/
noncomputable def sourceOriginalB558LiteralDyadicProfile434 (u : ℝ) : ℝ :=
  Real.smoothTransition (2*u-1)-Real.smoothTransition (u-1)

/-- Literal harmonic profile psi(u)=u*eta(u) from the original comparison. -/
noncomputable def sourceOriginalB558LiteralHarmonicProfile434 (u : ℝ) : ℝ :=
  u*sourceOriginalB558LiteralDyadicProfile434 u

private theorem B558_telescope434 (N : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (N+1), sourceOriginalB558LiteralDyadicProfile434 (t/(2:ℝ)^j)) =
      Real.smoothTransition (2*t-1)-Real.smoothTransition (t/(2:ℝ)^N-1) := by
  induction N with
  | zero => simp [sourceOriginalB558LiteralDyadicProfile434]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold sourceOriginalB558LiteralDyadicProfile434
    have he : 2*(t/(2:ℝ)^(N+1))=t/(2:ℝ)^N := by
      rw [pow_succ]
      field_simp
    rw [he]
    ring

private theorem B558_partition434
    (N : ℕ) (Z0 z : ℝ) (hZ : 0 < Z0) (hlo : Z0 ≤ z)
    (hhi : z ≤ Z0*(2:ℝ)^N) :
    (∑ j ∈ Finset.range (N+1),
      sourceOriginalB558LiteralDyadicProfile434 (z/(Z0*(2:ℝ)^j)))=1 := by
  simp_rw [div_mul_eq_div_div]
  rw [B558_telescope434]
  have hlo' : 1 ≤ z/Z0 := (le_div_iff₀ hZ).mpr (by simpa using hlo)
  have hhi' : z/Z0/(2:ℝ)^N ≤ 1 := by
    rw [div_le_iff₀ (by positivity),div_le_iff₀ hZ]
    simpa only [one_mul,mul_comm] using hhi
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*(z/Z0)-1),
    Real.smoothTransition.zero_of_nonpos (by linarith : z/Z0/(2:ℝ)^N-1 ≤ 0)]
  norm_num

/-- The ONE original external Z_j and the original harmonic psi/w give
exactly 1/D after summing the true dyadic family. No probability mass or
second exterior Z is inserted. This is a physical scalar identity, not
an identification of either complete Fourier integral. -/
theorem source_original_B558_actual_dyadic_harmonic_weight434
    (N : ℕ) (Z0 w : ℝ) (D : ℕ) (hZ : 0 < Z0) (hD : 0 < D)
    (hlo : Z0*(D:ℝ) ≤ w) (hhi : w ≤ (Z0*(2:ℝ)^N)*(D:ℝ)) :
    (∑ j ∈ Finset.range (N+1),
      (Z0*(2:ℝ)^j/w)*sourceOriginalB558LiteralHarmonicProfile434
        (w/((Z0*(2:ℝ)^j)*(D:ℝ)))) = 1/(D:ℝ) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hw : 0 < w := (mul_pos hZ hDR).trans_le hlo
  have hp := B558_partition434 N Z0 (w/(D:ℝ)) hZ
    ((le_div_iff₀ hDR).mpr hlo) ((div_le_iff₀ hDR).mpr hhi)
  calc
    _ = ∑ j ∈ Finset.range (N+1),
        (1/(D:ℝ))*sourceOriginalB558LiteralDyadicProfile434
          ((w/(D:ℝ))/(Z0*(2:ℝ)^j)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold sourceOriginalB558LiteralHarmonicProfile434
      have harg : w/((Z0*(2:ℝ)^j)*(D:ℝ)) =
          (w/(D:ℝ))/(Z0*(2:ℝ)^j) := by ring
      rw [harg]
      have hcoef : (Z0*(2:ℝ)^j/w)*((w/(D:ℝ))/(Z0*(2:ℝ)^j)) = 1/(D:ℝ) := by
        field_simp
      rw [← mul_assoc, hcoef]
    _ = (1/(D:ℝ))*(∑ j ∈ Finset.range (N+1),
        sourceOriginalB558LiteralDyadicProfile434 ((w/(D:ℝ))/(Z0*(2:ℝ)^j))) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [hp,mul_one]

section Actual
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (d : SourceComparisonData434 ι G cfg x L Y Hprime)
  (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)

/-- Genuine one-endpoint C191 selector energy with the literal original
harmonic profile, physical w, auxiliary D, and the single exterior Z_j.
This contains no q/core/D20 coefficient and no e,n window. -/
noncomputable def sourceOriginalB558DyadicSelectorLiftEnergy434
    (N : ℕ) (Z0 : ℝ) (D : ℕ) (A B : ℤ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), ∑ w ∈ Finset.Ioc A B,
    ((Z0*(2:ℝ)^j/(w:ℝ))*sourceOriginalB558LiteralHarmonicProfile434
      ((w:ℝ)/((Z0*(2:ℝ)^j)*(D:ℝ)))) *
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun eta a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ eta a:ℂ) *
        sourceOriginalB554MarkedSelector434 d J ell m hmJ w eta a) ν

/-- Exact conversion on an interval contained in the TRUE dyadic plateau.
The original unnormalized harmonic energy equals H/D times the uniform
mean. The normalization factor is displayed rather than hidden. -/
theorem source_original_B558_selector_dyadic_energy_exact434
    (N : ℕ) (Z0 : ℝ) (D : ℕ) (A B : ℤ)
    (hZ : 0 < Z0) (hD : 0 < D) (hAB : A < B)
    (hlo : Z0*(D:ℝ) ≤ (A:ℝ))
    (hhi : (B:ℝ) ≤ (Z0*(2:ℝ)^N)*(D:ℝ)) :
    sourceOriginalB558DyadicSelectorLiftEnergy434 d J ell m hmJ ν N Z0 D A B =
      (((B-A:ℤ):ℝ)/(D:ℝ))*
        sourceOriginalB554AveragedSelectorLiftEnergy434 d J ell m hmJ ν A B := by
  unfold sourceOriginalB558DyadicSelectorLiftEnergy434
  rw [Finset.sum_comm]
  have hH : ((B-A:ℤ):ℝ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hAB))
  simp_rw [← Finset.sum_mul]
  have hW (w : ℤ) (hw : w ∈ Finset.Ioc A B) :
      (∑ j ∈ Finset.range (N+1),
        (Z0*(2:ℝ)^j/(w:ℝ))*sourceOriginalB558LiteralHarmonicProfile434
          ((w:ℝ)/((Z0*(2:ℝ)^j)*(D:ℝ)))) = 1/(D:ℝ) := by
    have hr := Finset.mem_Ioc.mp hw
    have hwB : (w:ℝ) ≤ (B:ℝ) := by exact_mod_cast hr.2
    exact source_original_B558_actual_dyadic_harmonic_weight434 N Z0 w D hZ hD
      (hlo.trans (by exact_mod_cast hr.1.le)) (hwB.trans hhi)
  simp_rw [sourceOriginalB554AveragedSelectorLiftEnergy434]
  calc
    _ = ∑ w ∈ Finset.Ioc A B, (1/(D:ℝ))*
        sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
          (fun eta a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ eta a:ℂ) *
            sourceOriginalB554MarkedSelector434 d J ell m hmJ w eta a) ν := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hW w hw]
    _ = _ := by rw [← Finset.mul_sum]; field_simp

end Actual

/-- The actual dyadic harmonic weighting does not by itself make the
unchanged full-P selector lift polynomial. On any interval in its real
plateau of original length at least Z*D, it retains the full BIG product
lower bound. This is an energy-envelope obstruction, not a signed RMS
lower bound or a full two-Fourier comparison estimate. -/
theorem eventually_source_original_B558_actual_dyadic_selector_lower434
    (cfg : SourceComparisonFixed434) (ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι G : Type}
      [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      (hx : x = Real.exp L)
      (J : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
      (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, (1:ℝ)/(p:ℝ))
      (hBIG : ∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hDisj : ∀ g h p, p ∈ d.Tb g → p ∈ d.Tb h → g = h)
      (aux : SourceOriginalProbeAuxIndex434 m ν → ℕ)
      (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν d.Tb))
      (N : ℕ) (Z0 : ℝ) (A B : ℤ) (hZ0 : 0 < Z0)
      (hLength : d.Z*((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ) ≤
        ((B-A:ℤ):ℝ))
      (hlo : Z0*((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ) ≤ (A:ℝ))
      (hhi : (B:ℝ) ≤ (Z0*(2:ℝ)^N)*
        ((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ)),
      (((B-A:ℤ):ℝ)/((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ))*
          ((1/4:ℝ)*Real.exp (((∑ g : G,
            sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp)) ≤
        sourceOriginalB558DyadicSelectorLiftEnergy434 d J ell m hmJ ν N Z0
          (∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z) A B := by
  filter_upwards [eventually_source_original_B554_selector_mean_energy_lower434 cfg ell m,
    eventually_gt_atTop (0:ℝ)] with L hLower hL
  intro ι G _ _ _ _ x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux N Z0 A B hZ0 hLength hlo hhi
  let D := ∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z
  have hD : 0 < D := by
    apply Finset.prod_pos
    intro z _
    have hzmem := Fintype.mem_piFinset.mp haux z
    cases z with
    | inl z => exact (d.hTbPrime z.val.1 _ hzmem).pos
    | inr z => exact (d.hTbPrime z.val.1 _ hzmem).pos
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hZ : 0 < d.Z := by
    apply lt_of_lt_of_le _ d.hZ
    rw [hx]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hL _)
  have hH : (0:ℝ) < ((B-A:ℤ):ℝ) := (mul_pos hZ hDR).trans_le hLength
  have hAB : A < B := sub_pos.mp (show (0:ℤ) < B-A by exact_mod_cast hH)
  have hA : 0 ≤ A := by
    have hh : (0:ℝ) < A := (mul_pos hZ0 hDR).trans_le hlo
    have hh' : (0:ℤ) < A := by exact_mod_cast hh
    exact hh'.le
  rw [source_original_B558_selector_dyadic_energy_exact434 d J ell m hmJ ν N Z0 D A B
    hZ0 hD hAB hlo hhi]
  exact mul_le_mul_of_nonneg_left
    (hLower x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux A B hA hLength)
    (div_nonneg hH.le hDR.le)


private theorem B558_eventually_scale_one434 (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ Real.exp L*L^(-CZ) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop
    (a := (1:ℝ)) (by norm_num) (-CZ)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop (0:ℝ),h] with L hL hs
  have hs' : Real.exp (-L) ≤ L^(-CZ) := by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg hL _),one_mul,neg_mul] using hs
  calc
    1 = Real.exp L*Real.exp (-L) := by rw [← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs' (Real.exp_pos _).le

/-- A concrete nonempty physical interval removes all extra plateau and
length hypotheses: A=ceil(ZD), B=floor(4ZD), with the original base Z.
For every original depth N>=2 the actual dyadic energy on this interval
is at least Z/4 times the full BIG product scale. No test nonvanishing
or arbitrary lower cutoff value is assumed. This remains the selector
energy, not the q/core/D20 energy. -/
theorem eventually_source_original_B558_canonical_dyadic_selector_lower434
    (cfg : SourceComparisonFixed434) (ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι G : Type}
      [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      (hx : x = Real.exp L)
      (J : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
      (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, (1:ℝ)/(p:ℝ))
      (hBIG : ∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hDisj : ∀ g h p, p ∈ d.Tb g → p ∈ d.Tb h → g = h)
      (aux : SourceOriginalProbeAuxIndex434 m ν → ℕ)
      (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν d.Tb))
      (N : ℕ) (hN : 2 ≤ N),
      let D := ∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z
      d.Z*((1/4:ℝ)*Real.exp (((∑ g : G,
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp)) ≤
        sourceOriginalB558DyadicSelectorLiftEnergy434 d J ell m hmJ ν N d.Z D
          ⌈d.Z*(D:ℝ)⌉ ⌊4*(d.Z*(D:ℝ))⌋ := by
  filter_upwards [eventually_source_original_B558_actual_dyadic_selector_lower434 cfg ell m,
    B558_eventually_scale_one434 cfg.CZ] with L hLower hScale
  intro ι G _ _ _ _ x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux N hN
  dsimp only
  let D := ∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z
  let R := d.Z*(D:ℝ)
  have hD : 0 < D := by
    apply Finset.prod_pos
    intro z _
    have hzmem := Fintype.mem_piFinset.mp haux z
    cases z with
    | inl z => exact (d.hTbPrime z.val.1 _ hzmem).pos
    | inr z => exact (d.hTbPrime z.val.1 _ hzmem).pos
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hZ1 : 1 ≤ d.Z := hScale.trans (by simpa only [hx] using d.hZ)
  have hZ : 0 < d.Z := lt_of_lt_of_le (by norm_num) hZ1
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    exact one_le_mul_of_one_le_of_one_le hZ1 hD1
  have hLen : R ≤ (((⌊4*R⌋:ℤ)-(⌈R⌉:ℤ):ℤ):ℝ) := by
    have ha := Int.ceil_lt_add_one R
    have hb := Int.lt_floor_add_one (4*R)
    push_cast
    linarith
  have hLo : R ≤ ((⌈R⌉:ℤ):ℝ) := Int.le_ceil R
  have hPow : (4:ℝ) ≤ (2:ℝ)^N := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN
    norm_num at hh ⊢
    exact hh
  have hHi : ((⌊4*R⌋:ℤ):ℝ) ≤ (d.Z*(2:ℝ)^N)*(D:ℝ) := by
    calc
      _ ≤ 4*R := Int.floor_le (4*R)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hPow (show 0 ≤ R by linarith)
        dsimp only [R] at hh ⊢
        nlinarith
  have hh := hLower x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux
    N d.Z ⌈R⌉ ⌊4*R⌋ hZ hLen hLo hHi
  have hzFactor : d.Z ≤ (((⌊4*R⌋:ℤ)-(⌈R⌉:ℤ):ℤ):ℝ)/(D:ℝ) :=
    (le_div_iff₀ hDR).mpr hLen
  have hFactor : 0 ≤ (1/4:ℝ)*Real.exp (((∑ g : G,
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp) := by positivity
  exact (mul_le_mul_of_nonneg_right hzFactor hFactor).trans hh
end Green64Analytic.CorrelationSquare

end

end

