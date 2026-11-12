module

public import Green64.Library.Weights.MarkedIntervalInverseLog
public import Green64.Library.Weights.Part092
public import Green64.Library.Weights.Part023

@[expose] public section

/-!
# Weights / OutsideAveragedMarkedLiftObstruction

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OutsideAveragedMarkedLiftObstruction -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

private theorem B554_product_injective_mass434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (value : (i : I) → P i → ℕ) (hinj : ∀ i, Function.Injective (value i))
    (mu : (i : I) → P i → ℝ) (hmu : ∀ i p, 0 ≤ mu i p)
    (hmass : ∀ i, ∑ p : P i, mu i p = 1)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : ∀ i p, mu i p ≤ eta) :
    1 - (Fintype.card I:ℝ)^2*eta ≤
      ∑ x : (i : I) → P i,
        if Function.Injective (fun i => value i (x i)) then ∏ i, mu i (x i) else 0 := by
  classical
  let l := (Finset.univ : Finset I).toList
  have hnodup (x : (i : I) → P i) :
      (l.map (fun i => value i (x i))).Nodup ↔
        Function.Injective (fun i => value i (x i)) := by
    rw [List.nodup_map_iff_inj_on (Finset.nodup_toList _)]
    simp only [Finset.mem_toList, Finset.mem_univ, true_implies]
    rfl
  have hbad := source_original_physical_list_collision434 P value hinj mu hmu hmass
    l (Finset.nodup_toList _) eta heta (fun i _ p => hcap i p)
  simp_rw [hnodup] at hbad
  have htotal : (∑ x : (i : I) → P i, ∏ i, mu i (x i)) = 1 := by
    calc
      _ = ∏ i, ∑ p : P i, mu i p := (Fintype.prod_sum mu).symm
      _ = 1 := by simp [hmass]
  have hsplit :
      (∑ x : (i : I) → P i,
        if Function.Injective (fun i => value i (x i)) then ∏ i, mu i (x i) else 0) +
      (∑ x : (i : I) → P i,
        if ¬ Function.Injective (fun i => value i (x i)) then ∏ i, mu i (x i) else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Function.Injective (fun i => value i (x i)) <;> simp [hx]
  linarith

section Actual
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (d : SourceComparisonData434 ι G cfg x L Y Hprime)
  (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
local notation "X" => SourceOriginalVariableBIGState434
  (fun g : G => {p : ℕ // p ∈ d.Tb g})
  (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)

/-- The true injective free-mark carrier has almost all of the genuine
harmonic mass. This uses the already proved independent physical-list
collision bound; no physical-position or core independence is inferred. -/
theorem source_original_B554_genuine_harmonic_mass_lower434
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, (1:ℝ)/(p:ℝ))
    (hBIG : ∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ)) :
    1 - (((∑ g : G, sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g : ℕ):ℝ)^2)*
        (Real.exp (-(L^cfg.cexp))/cfg.vmin) ≤
      ∑ a ∈ sourceOriginalB544GenuineFreeStates434 d J ell m hmJ ν,
        sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν a := by
  classical
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let I := Σ g : G, Fin (t g)
  let FP : I → Type := fun z => BP z.1
  let fmu : (z : I) → FP z → ℝ := fun z p => mu z.1 p
  let e := Equiv.piCurry (fun g (_ : Fin (t g)) => BP g)
  let eta := Real.exp (-(L^cfg.cexp))/cfg.vmin
  have hEq : ∀ g, d.Vbig g = ∑ p : BP g, (1:ℝ)/(p.val:ℝ) := by
    intro g
    exact (hVbig g).trans (Finset.sum_coe_sort (d.Tb g)
      (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  obtain ⟨hmu,hmass⟩ := source_original_joint_harmonic_normalized434
    BP (fun _ p => p.val) d.Vbig (fun g => cfg.hv.trans_le (d.hVbig g)) hEq
  have hcap (z : I) (p : FP z) : fmu z p ≤ eta := by
    have hp := hBIG z.1 p.val p.property
    have hp0 : (0:ℝ) < p.val := (Real.exp_pos _).trans_le hp
    change ((1:ℝ)/(p.val:ℝ))/d.Vbig z.1 ≤ Real.exp (-(L^cfg.cexp))/cfg.vmin
    calc
      _ ≤ ((1:ℝ)/Real.exp (L^cfg.cexp))/cfg.vmin := by
        apply div_le_div₀ (by positivity)
          (one_div_le_one_div_of_le (Real.exp_pos _) hp) cfg.hv (d.hVbig z.1)
      _ = _ := by rw [Real.exp_neg]; ring
  have hFlat := B554_product_injective_mass434 FP (fun _ p => p.val)
    (fun _ => Subtype.val_injective) fmu
    (fun z p => hmu z.1 p) (fun z => hmass z.1) eta
    (by dsimp [eta]; exact div_nonneg (Real.exp_pos _).le cfg.hv.le) hcap
  have hFlatMass (a : (z : I) → FP z) :
      (∏ z : I, fmu z (a z)) =
        sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν (e a) := by
    rw [Fintype.prod_sigma]
    rfl
  have hDom : (∑ a : (z : I) → FP z,
      if Function.Injective (fun z => (a z).val) then ∏ z, fmu z (a z) else 0) ≤
      ∑ a : (z : I) → FP z,
        if (∀ g, Function.Injective (fun i => ((e a) g i).val))
          then sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν (e a) else 0 := by
    apply Finset.sum_le_sum
    intro a _
    have hnonneg : 0 ≤ sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν (e a) :=
      source_original_variable_BIG_mass_nonneg434 BP t mu hmu (e a)
    by_cases hi : Function.Injective (fun z => (a z).val)
    · have hgood : ∀ g, Function.Injective (fun i => ((e a) g i).val) := by
        intro g i j hij
        have h := hi (show (a ⟨g,i⟩).val = (a ⟨g,j⟩).val from hij)
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      rw [ite_eq_left hi, ite_eq_left hgood, hFlatMass]
    · simp only [ite_eq_right hi]
      split_ifs <;> positivity
  have hCurry : (∑ a : (z : I) → FP z,
        if (∀ g, Function.Injective (fun i => ((e a) g i).val))
          then sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν (e a) else 0) =
      ∑ a ∈ sourceOriginalB544GenuineFreeStates434 d J ell m hmJ ν,
        sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν a := by
    simp only [sourceOriginalB544GenuineFreeStates434, Finset.sum_filter]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hCard : Fintype.card I = ∑ g : G, t g := by simp [I, Fintype.card_sigma]
  calc
    _ = 1 - (Fintype.card I:ℝ)^2*eta := by rw [hCard]
    _ ≤ _ := hFlat.trans (hDom.trans_eq hCurry)

/-- The literal original free-BIG divisibility and injectivity selector.
This contains no q damping, sourceCore, D20 coefficient, or extra test. -/
noncomputable def sourceOriginalB554MarkedSelector434 (w : ℤ)
    (eta : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ eta)) : ℂ :=
  if (fun g i => (a g i).val) ∈
    bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ eta) w.toNat
    then 1 else 0

/-- The original C191 harmonic endpoint energy of the unchanged full-P
lift of the literal marked selector, averaged over positive physical
positions. It is an operator-envelope test, not the actual q/core/D20
endpoint amplitude. Zero shift below is only the one-end norm diagonal. -/
noncomputable def sourceOriginalB554AveragedSelectorLiftEnergy434 (A B : ℤ) : ℝ :=
  (∑ w ∈ Finset.Ioc A B,
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun eta a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ eta a:ℂ) *
        sourceOriginalB554MarkedSelector434 d J ell m hmJ w eta a) ν) / ((B-A:ℤ):ℝ)

/-- Exact outside-position evaluation of the literal selector lift.
The B542 density is reused, and the only sampling count is the actual
B543 marked mask on the one-end diagonal. -/
theorem source_original_B554_selector_mean_energy_count434 (A B : ℤ) :
    sourceOriginalB554AveragedSelectorLiftEnergy434 d J ell m hmJ ν A B =
      ∑ a : X, sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν a *
        ((sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a)^2/((B-A:ℤ):ℝ)) *
        (sourceOriginalB543MarkedJointIntervalCount434 d J ell m hmJ ν a a A B 0 1:ℝ) := by
  classical
  let mu := sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν
  let P := sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν
  let test := sourceOriginalB554MarkedSelector434 d J ell m hmJ
  have hNorm (w : ℤ) (a : X) : ‖test w ν a‖^2 =
      if (fun g i => (a g i).val) ∈
        bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) w.toNat
      then (1:ℝ) else 0 := by
    dsimp only [test, sourceOriginalB554MarkedSelector434]
    split_ifs <;> simp
  have hW (w : ℤ) :
      sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
        (fun eta a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ eta a:ℂ) *
          test w eta a) ν =
      ∑ a : X, mu a * P a^2 *
        (if (fun g i => (a g i).val) ∈
          bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) w.toNat
        then (1:ℝ) else 0) := by
    rw [source_original_B542_true_C191_counting_pullback_energy434, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hNorm]
    have hDensity := source_original_B542_true_harmonic_counting_density434 d J ell m hmJ ν a
    change mu a*P a = sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν at hDensity
    rw [← hDensity]
    ring
  have hCount (a : X) :
      (∑ w ∈ Finset.Ioc A B, if (fun g i => (a g i).val) ∈
        bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) w.toNat
        then (1:ℝ) else 0) =
      (sourceOriginalB543MarkedJointIntervalCount434 d J ell m hmJ ν a a A B 0 1:ℝ) := by
    simp only [sourceOriginalB543MarkedJointIntervalCount434, zero_mul, add_zero, and_self]
    exact Finset.sum_boole _ _
  unfold sourceOriginalB554AveragedSelectorLiftEnergy434
  dsimp only [test] at hW
  simp_rw [hW]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, hCount]
  ring

end Actual

private theorem B554_eventually_genuine_mass_half434
    (cfg : SourceComparisonFixed434) (ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι G : Type}
      [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      (J : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m),
      (∀ g, d.Vbig g = ∑ p ∈ d.Tb g, (1:ℝ)/(p:ℝ)) →
      (∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ)) →
      (1/2:ℝ) ≤ ∑ a ∈ sourceOriginalB544GenuineFreeStates434 d J ell m hmJ ν,
        sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν a := by
  let C : ℝ := ((ell+m:ℕ):ℝ)*cfg.C0
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) cfg.hC0
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  have hDecay := eventually_source_fixed_poly_exp_saving cfg.cexp (C^2/cfg.vmin) 2 1 hc
  filter_upwards [hDecay, eventually_ge_atTop (2:ℝ)] with L hDecayL hLtwo
  intro ι G _ _ _ _ x Y Hprime d J hmJ ν hVbig hBIG
  have hL : 0 < L := by linarith
  let T := ∑ g : G, sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g
  have hT : (T:ℝ) ≤ C*L := by
    have ht : T ≤ (ell+m)*Fintype.card G := by
      calc
        _ ≤ ∑ _g : G, (ell+m) := Finset.sum_le_sum
          (fun g _ => source_original_probe_free_mark_cap434 J ell m hmJ ν g)
        _ = _ := by simp [Nat.mul_comm]
    calc
      (T:ℝ) ≤ ((ell+m:ℕ):ℝ)*(Fintype.card G:ℝ) := by exact_mod_cast ht
      _ ≤ ((ell+m:ℕ):ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left d.hBigGroups (Nat.cast_nonneg _)
      _ ≤ C*L := by
        dsimp only [C]
        have hlog : Real.log L ≤ L := le_trans (Real.log_le_sub_one_of_pos hL) (by linarith)
        have hh := mul_le_mul_of_nonneg_left hlog hC
        dsimp only [C] at hh
        simpa only [mul_assoc] using hh
  have hT2 : (T:ℝ)^2 ≤ (C*L)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hT
  have hSmall : (T:ℝ)^2*(Real.exp (-(L^cfg.cexp))/cfg.vmin) ≤ 1/2 := by
    calc
      _ ≤ (C*L)^2*(Real.exp (-(L^cfg.cexp))/cfg.vmin) :=
        mul_le_mul_of_nonneg_right hT2 (div_nonneg (Real.exp_pos _).le cfg.hv.le)
      _ = (C^2/cfg.vmin)*L^(2:ℝ)*Real.exp (-(L^cfg.cexp)) := by rw [Real.rpow_two]; ring
      _ ≤ 1/L := by simpa only [Real.rpow_one] using hDecayL.2
      _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hLtwo
  have hActual := source_original_B554_genuine_harmonic_mass_lower434 d J ell m hmJ ν hVbig hBIG
  change 1-(T:ℝ)^2*(Real.exp (-(L^cfg.cexp))/cfg.vmin) ≤ _ at hActual
  linarith

/-- Genuine uniform-interval mean energy of the original free-mark
selector with its unchanged full prime-product C191 lift. The outside
average cancels only one prime product, so the energy is exponentially
large on the BIG-prime scale. This is a selector/operator-envelope lower
bound: q damping, arithmetic cores and D20 coefficients are NOT asserted
to be nonzero, nor are they included in this lower-bound test. -/
theorem eventually_source_original_B554_selector_mean_energy_lower434
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
      (A B : ℤ) (hA : 0 ≤ A)
      (hLength : d.Z*((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ) ≤
        ((B-A:ℤ):ℝ)),
      (1/4:ℝ)*Real.exp (((∑ g : G,
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp) ≤
        sourceOriginalB554AveragedSelectorLiftEnergy434 d J ell m hmJ ν A B := by
  filter_upwards [B554_eventually_genuine_mass_half434 cfg ell m,
    eventually_source_original_B544_marked_joint_interval_inverse_log434 cfg ell m 1,
    eventually_ge_atTop (2:ℝ)] with L hMassHalf hSampling hLtwo
  intro ι G _ _ _ _ x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux A B hA hLength
  classical
  let X := SourceOriginalVariableBIGState434
    (fun g : G => {p : ℕ // p ∈ d.Tb g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
  let K := sourceOriginalB544GenuineFreeStates434 d J ell m hmJ ν
  let mu := sourceOriginalB544OriginalHarmonicMass434 d J ell m hmJ ν
  let P := sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν
  let H : ℝ := ((B-A:ℤ):ℝ)
  let DC := ∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z
  let Pmin := Real.exp (((∑ g : G,
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp)
  let count (a : X) := sourceOriginalB543MarkedJointIntervalCount434
    d J ell m hmJ ν a a A B 0 1
  have hL : 0 < L := by linarith
  have hZ : 0 < d.Z := by
    apply lt_of_lt_of_le _ d.hZ
    rw [hx]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hL _)
  have hDC : 0 < DC := by
    apply Finset.prod_pos
    intro z _
    have hzmem := Fintype.mem_piFinset.mp haux z
    cases z with
    | inl z => exact (d.hTbPrime z.val.1 _ hzmem).pos
    | inr z => exact (d.hTbPrime z.val.1 _ hzmem).pos
  have hH : 0 < H := lt_of_lt_of_le (mul_pos hZ (by exact_mod_cast hDC)) hLength
  have hmu : ∀ a : X, 0 ≤ mu a := by
    intro a
    apply source_original_variable_BIG_mass_nonneg434
    intro g p
    change 0 ≤ ((1:ℝ)/(p.val:ℝ))/d.Vbig g
    have hp : (0:ℝ) < p.val := by exact_mod_cast (d.hTbPrime g _ p.property).pos
    exact div_nonneg (by positivity) (cfg.hv.trans_le (d.hVbig g)).le
  have hPone (a : X) : 1 ≤ P a := by
    dsimp only [P]
    rw [← source_original_B543_prime_product_real434]
    exact_mod_cast source_original_B543_prime_product_positive434 d J ell m hmJ ν a
  have hPmin (a : X) : Pmin ≤ P a :=
    source_original_B542_true_BIG_prime_product_lower434 d J ell m hmJ ν hBIG a
  have hMhalf : (1/2:ℝ) ≤ ∑ a ∈ K, mu a :=
    hMassHalf x Y Hprime d J hmJ ν hVbig hBIG
  have hPoint (a : X) (haK : a ∈ K) : P a/2 ≤ (P a^2/H)*(count a:ℝ) := by
    have ha : ∀ g, Function.Injective (fun i => (a g i).val) := (Finset.mem_filter.mp haK).2
    have hs := hSampling x Y Hprime d hx J hmJ ν hDisj a a ha ha aux haux A B 0 hA
      (by simpa using hA) hLength
    have hCountDC : sourceOriginalB543MarkedJointIntervalCount434 d J ell m hmJ ν
        a a A B (2*0) DC = count a := by
      simp only [sourceOriginalB543MarkedJointIntervalCount434, count, mul_zero, zero_mul]
    have hs' : |(P a^2/H)*(count a:ℝ)-P a| ≤ 1/L := by
      dsimp only at hs
      rw [hCountDC] at hs
      simp only [Nat.gcd_self, mul_zero, zero_mul, dvd_zero, ite_true,
        Nat.cast_mul, source_original_B543_prime_product_real434,
        Real.rpow_neg_one] at hs
      change |(P a*P a/H)*(count a:ℝ)-P a| ≤ L⁻¹ at hs
      simpa only [pow_two, one_div] using hs
    have hlo := (abs_le.mp hs').1
    have hinv : 1/L ≤ (1/2:ℝ) := one_div_le_one_div_of_le (by norm_num) hLtwo
    linarith only [hlo, hinv, hPone a]
  have hBound : (Pmin/2)*(∑ a ∈ K, mu a) ≤
      ∑ a : X, mu a*(P a^2/H)*(count a:ℝ) := by
    calc
      _ = ∑ a ∈ K, mu a*(Pmin/2) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ ≤ ∑ a ∈ K, mu a*((P a^2/H)*(count a:ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_left _ (hmu a)
        exact (div_le_div_of_nonneg_right (hPmin a) (by norm_num)).trans (hPoint a ha)
      _ = ∑ a ∈ K, mu a*(P a^2/H)*(count a:ℝ) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a : X, mu a*(P a^2/H)*(count a:ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro a _ _
        exact mul_nonneg (mul_nonneg (hmu a) (div_nonneg (sq_nonneg _) hH.le)) (Nat.cast_nonneg _)
  have hMinPos : 0 < Pmin := Real.exp_pos _
  calc
    _ ≤ (Pmin/2)*(∑ a ∈ K, mu a) := by
      have hh := mul_le_mul_of_nonneg_left hMhalf (show 0 ≤ Pmin/2 by positivity)
      convert hh using 1
      ring
    _ ≤ ∑ a : X, mu a*(P a^2/H)*(count a:ℝ) := hBound
    _ = _ := (source_original_B554_selector_mean_energy_count434 d J ell m hmJ ν A B).symm

/-- With at least one genuine free label, the same original selector
mean energy exceeds every fixed logarithmic envelope. This excludes a
polynomial uniform selector-norm budget for the unchanged full-P lift;
it is not a lower bound for the full signed q/core/D20 amplitude. -/
theorem eventually_source_original_B554_selector_exceeds_fixed_log_power434
    (cfg : SourceComparisonFixed434) (ell m : ℕ) (K Bpower : ℝ) :
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
      (A B : ℤ) (hA : 0 ≤ A)
      (hLength : d.Z*((∏ z : SourceOriginalProbeAuxIndex434 m ν, aux z:ℕ):ℝ) ≤
        ((B-A:ℤ):ℝ)),
      0 < (∑ g : G, sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) →
      K*L^Bpower ≤ sourceOriginalB554AveragedSelectorLiftEnergy434 d J ell m hmJ ν A B := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B554_selector_mean_energy_lower434 cfg ell m,
    eventually_source_fixed_poly_exp_saving cfg.cexp (4*K) Bpower 0 hc]
    with L hLower hPoly
  intro ι G _ _ _ _ x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux A B hA hLength hFree
  have hActual := hLower x Y Hprime d hx J hmJ ν hVbig hBIG hDisj aux haux A B hA hLength
  have hScalar : K*L^Bpower ≤ (1/4:ℝ)*Real.exp (L^cfg.cexp) := by
    have hh : (4*K*L^Bpower)/Real.exp (L^cfg.cexp) ≤ 1 := by
      simpa only [Real.rpow_zero, div_one, Real.exp_neg, div_eq_mul_inv, inv_one, mul_one] using hPoly.2
    have hh' := (div_le_iff₀ (Real.exp_pos (L^cfg.cexp))).mp hh
    linarith only [hh']
  have hT : (1:ℝ) ≤ ((∑ g : G,
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ) := by exact_mod_cast hFree
  have hExp : Real.exp (L^cfg.cexp) ≤
      Real.exp (((∑ g : G, sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g:ℕ):ℝ)*L^cfg.cexp) := by
    apply Real.exp_le_exp.mpr
    exact le_mul_of_one_le_left (Real.rpow_nonneg (by linarith [hPoly.1]) _) hT
  exact hScalar.trans ((mul_le_mul_of_nonneg_left hExp (by norm_num : (0:ℝ) ≤ 1/4)).trans hActual)
end Green64Analytic.CorrelationSquare

end

end

