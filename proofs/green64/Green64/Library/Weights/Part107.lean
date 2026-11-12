module

public import Green64.Library.Sieve.Foundations.Part005

@[expose] public section

/-!
# Weights / Part107

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Conductor003 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 14. -/
noncomputable def sourceLogMellinKernel (Ψ : ℝ → ℝ) (L t : ℝ) : ℂ :=
  (𝓕 (sourceLogProfile Ψ)) t * Complex.exp (((-t * L : ℝ) : ℂ) * Complex.I)



/- Exact source owner: SourceShiftTwoWeightedFourier.lean; original line 41. -/
noncomputable def sourceMellinPhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 26. -/
theorem source_log_profile_compact (Ψ : ℝ → ℝ)
    (hΨ : Function.support Ψ ⊆ Set.Icc (1 : ℝ) 2) :
    HasCompactSupport (sourceLogProfile Ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.log 2 / (2 * Real.pi))))
  intro v hv
  have hn : Ψ (Real.exp (2 * Real.pi * v)) ≠ 0 := by
    intro hz
    exact hv (by simp [sourceLogProfile, hz])
  have hs := hΨ hn
  have ha : Real.exp 0 ≤ Real.exp (2 * Real.pi * v) := by simpa using hs.1
  have hb : Real.exp (2 * Real.pi * v) ≤ Real.exp (Real.log 2) := by
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hs.2
  have ha' := Real.exp_le_exp.mp ha
  have hb' := Real.exp_le_exp.mp hb
  constructor
  · nlinarith [Real.pi_pos]
  · exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 20. -/
theorem source_log_profile_smooth (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (sourceLogProfile Ψ) := by
  unfold sourceLogProfile
  exact Complex.ofRealCLM.contDiff.comp (hΨ.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 45. -/
theorem source_log_fourier_integrable (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨsupport : Function.support Ψ ⊆ Set.Icc (1 : ℝ) 2) :
    Integrable (𝓕 (sourceLogProfile Ψ)) := by
  let g := (source_log_profile_compact Ψ hΨsupport).toSchwartzMap
    (source_log_profile_smooth Ψ hΨ)
  have hi := (𝓕 g).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe] at hi
  exact hi



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 60. -/
theorem source_log_kernel_integrable (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨsupport : Function.support Ψ ⊆ Set.Icc (1 : ℝ) 2) (L : ℝ) :
    Integrable (sourceLogMellinKernel Ψ L) := by
  have hi := source_log_fourier_integrable Ψ hΨ hΨsupport
  apply hi.mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (((-t * L : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by simp [Complex.norm_exp, Complex.mul_re])



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 54. -/
theorem source_log_kernel_norm (Ψ : ℝ → ℝ) (L t : ℝ) :
    ‖sourceLogMellinKernel Ψ L t‖ = ‖(𝓕 (sourceLogProfile Ψ)) t‖ := by
  unfold sourceLogMellinKernel
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 69. -/
theorem source_log_kernel_uniform_mass (Ψ : ℝ → ℝ) (L : ℝ) :
    (∫ t, ‖sourceLogMellinKernel Ψ L t‖) = sourceLogMellinMass Ψ := by
  simp only [source_log_kernel_norm, sourceLogMellinMass]



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 78. -/
theorem source_log_mellin_inversion (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨsupport : Function.support Ψ ⊆ Set.Icc (1 : ℝ) 2)
    (L : ℝ) (p R : ℕ) (hp : 0 < p) (hR : 0 < R) :
    (Ψ (((p*R : ℕ) : ℝ) / Real.exp L) : ℂ) =
      ∫ t, sourceLogMellinKernel Ψ L t * sourceMellinPhase t p * sourceMellinPhase t R := by
  let z : ℝ := (Real.log (p : ℝ) + Real.log (R : ℝ) - L) / (2 * Real.pi)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hexp : Real.exp (2 * Real.pi * z) = ((p*R : ℕ) : ℝ) / Real.exp L := by
    dsimp [z]
    have hz : 2 * Real.pi * ((Real.log (p : ℝ) + Real.log (R : ℝ) - L) /
        (2 * Real.pi)) = Real.log (p : ℝ) + Real.log (R : ℝ) - L := by
      field_simp
    rw [hz, Real.exp_sub, Real.exp_add, Real.exp_log hp', Real.exp_log hR']
    simp only [Nat.cast_mul]
  let g := (source_log_profile_compact Ψ hΨsupport).toSchwartzMap
    (source_log_profile_smooth Ψ hΨ)
  have hi : Integrable (sourceLogProfile Ψ) := g.integrable (μ := volume)
  have hinv := hi.fourierInv_fourier_eq (source_log_fourier_integrable Ψ hΨ hΨsupport)
    ((source_log_profile_smooth Ψ hΨ).continuous.continuousAt (x := z))
  rw [Real.fourierInv_eq] at hinv
  calc
    _ = sourceLogProfile Ψ z := by simp only [sourceLogProfile, hexp]
    _ = ∫ t : ℝ, Real.fourierChar (inner ℝ t z) • (𝓕 (sourceLogProfile Ψ)) t := hinv.symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp only
      change (Real.fourierChar (inner ℝ t z) : ℂ) * (𝓕 (sourceLogProfile Ψ)) t = _
      rw [Real.fourierChar_apply]
      unfold sourceLogMellinKernel sourceMellinPhase
      conv_lhs => rw [mul_comm]
      simp only [mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [ Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_div]
      dsimp [z]
      push_cast
      field_simp
      <;> simp
      <;> ring



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 9. -/
noncomputable def sourceDeletedPrimePhase
    (r₀ : ℕ) (L : ℝ) (h : ℕ) (ζ : ℕ → ℂ) (p : ℕ) : ℂ :=
  if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0, by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h
  then ζ p else 0



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 15. -/
noncomputable def sourceDeletedResidualPhase
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (h : ℕ) (ζ : ℕ → ℂ) (R : ℕ) : ℂ :=
  if R.Coprime h then
    (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) * ζ R else 0



/- Exact source owner: SourceShiftTwoFourierBox.lean; original line 48. -/
noncomputable def sourceDeletedMellinBoxProduct
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (h M₁ N₁ M₂ N₂ d : ℕ)
    (χ : DirichletCharacter ℂ d) (t : ℝ) : ℂ :=
  (∑ p ∈ Finset.Ioc M₁ (M₁+N₁),
    sourceDeletedPrimePhase r₀ L h (sourceMellinPhase t) p * χ p) *
  (∑ R ∈ Finset.Ioc M₂ (M₂+N₂),
    sourceDeletedResidualPhase r₀ hr₀ L h (sourceMellinPhase t) R * χ R)



/- Exact source owner: SourceShiftTwoPrimitiveBilinear.lean; original line 13. -/
noncomputable def sourcePrimitiveBilinear (S : Finset ℕ) (M₁ N₁ M₂ N₂ : ℕ)
    (a b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ S, (q.totient : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
      ‖(∑ n ∈ Finset.Ioc M₁ (M₁+N₁), a n * χ n) *
        (∑ n ∈ Finset.Ioc M₂ (M₂+N₂), b n * χ n)‖ else 0



/- Exact source owner: SourceShiftTwoWeightedFourier.lean; original line 44. -/
theorem source_mellin_phase_norm (t : ℝ) (n : ℕ) :
    ‖sourceMellinPhase t n‖ = 1 := by
  rw [sourceMellinPhase, Complex.norm_exp]
  have hz : ((((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hz, Real.exp_zero]



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 20. -/
theorem source_deleted_prime_phase_energy
    (r₀ : ℕ) (L : ℝ) (h M N : ℕ) (ζ : ℕ → ℂ) (hζ : ∀ n, ‖ζ n‖ = 1) :
    (∑ p ∈ Finset.Ioc M (M+N), ‖sourceDeletedPrimePhase r₀ L h ζ p‖^2) ≤ N := by
  calc
    _ ≤ ∑ _p ∈ Finset.Ioc M (M+N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      unfold sourceDeletedPrimePhase
      split_ifs <;> simp [hζ]
    _ = _ := by simp



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 31. -/
theorem source_deleted_residual_phase_energy
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (h M N : ℕ) (ζ : ℕ → ℂ)
    (hζ : ∀ n, ‖ζ n‖ = 1) (H : ℝ)
    (hb : ∀ R, 0 ≤ sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ∧
      sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ≤ H) (hH : 0 ≤ H) :
    (∑ R ∈ Finset.Ioc M (M+N), ‖sourceDeletedResidualPhase r₀ hr₀ L h ζ R‖^2) ≤
      (N : ℝ)*H^2 := by
  calc
    _ ≤ ∑ _R ∈ Finset.Ioc M (M+N), H^2 := by
      apply Finset.sum_le_sum
      intro R hR
      unfold sourceDeletedResidualPhase
      split_ifs with hcop
      · simp only [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hb R).1]
        exact pow_le_pow_left₀ (hb R).1 (hb R).2 2
      · simp only [norm_zero, zero_pow (by omega : 2 ≠ 0)]
        positivity
    _ = _ := by simp

/- The actual source residual coefficient, both induced-character masks, and
arbitrary unit phases obey the primitive dyadic bilinear large-sieve estimate.
This is the Fourier-integrand bound, not the unproved global Echi saving. -/



/- Exact source owner: SourceShiftTwoDeletedSlotConvolution.lean; original line 16. -/
theorem source_deleted_Q_nonneg
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) (v : ℕ) :
    0 ≤ sourceDeletedQCoefficient r Q b i v := by
  unfold sourceDeletedQCoefficient
  apply Finset.sum_nonneg
  intro rest hrest
  split_ifs <;> positivity

/- Literal a(v), including its off-support value, as full tuple count. -/



/- Exact source owner: SourceShiftTwoMacroDrop.lean; original line 8. -/
theorem source_factorial_inverse_bounds (n : ℕ) :
    0 ≤ (((n.factorial:ℕ):ℝ)⁻¹) ∧
    (((n.factorial:ℕ):ℝ)⁻¹) ≤ 1 := by
  have hp : (0:ℝ) < (n.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have h1 : (1:ℝ) ≤ (n.factorial:ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos n)
  constructor
  · exact inv_nonneg.mpr hp.le
  · exact (inv_le_one₀ hp).mpr h1

/- The literal source factorial product over an entire Q band
equals the orbit-stabilizer product over the actual prime multiset.
Missing Q primes have exponent zero (0! = 1). -/



/- Exact source owner: SourceShiftTwoDeletedSlotBound.lean; original line 7. -/
theorem source_original_ordinary_le_one
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ) :
    sourceOriginalOrdinaryCoefficient r Q v ≤ 1 := by
  unfold sourceOriginalOrdinaryCoefficient
  split_ifs
  · apply Finset.prod_le_one₀
    · intro b hb
      apply Finset.prod_nonneg
      intro p hp
      exact (source_factorial_inverse_bounds _).1
    · intro b hb
      apply Finset.prod_le_one₀
      · intro p hp
        exact (source_factorial_inverse_bounds _).1
      · intro p hp
        exact (source_factorial_inverse_bounds _).2
  · norm_num

/- A direct bound for the source06 residual integer coefficient.
Nonemptiness of the designated prime band is the only local requirement;
it is supplied by the actual band PNT in an eventual source specialization. -/



/- Exact source owner: SourceShiftTwoDeletedSlotBound.lean; original line 29. -/
theorem source_deleted_Q_le_one
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) (v : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hne : (Q b).Nonempty) :
    sourceDeletedQCoefficient r Q b i v ≤ 1 := by
  obtain ⟨p, hp⟩ := hne
  have hp0 := (hPrime b p hp).pos
  have h := source_original_Q_deleted_slot_convolution r Q b i (p*v) hPrime hDisjoint
  have hterm : (if p ∣ p*v then sourceDeletedQCoefficient r Q b i (p*v/p) else 0) ≤
      ∑ q ∈ Q b, if q ∣ p*v then sourceDeletedQCoefficient r Q b i (p*v/q) else 0 := by
    apply Finset.single_le_sum (f := fun q : ℕ =>
      if q ∣ p*v then sourceDeletedQCoefficient r Q b i (p*v/q) else 0)
    · intro q hq
      split_ifs
      · exact source_deleted_Q_nonneg r Q b i _
      · exact le_refl 0
    · exact hp
  rw [if_pos (dvd_mul_right p v), Nat.mul_div_cancel_left _ hp0, ← h] at hterm
  exact hterm.trans (source_original_ordinary_le_one r Q (p*v))



/- Exact source owner: SourceShiftTwoDeletedCoefficientPolylog.lean; original line 9. -/
theorem source_half_mark_le_two (k : ℕ) :
    (k:ℝ)*(1/2:ℝ)^(k-1) ≤ 2 := by
  cases k with
  | zero => norm_num
  | succ k =>
    have hk : ((k+1:ℕ):ℝ) ≤ (2:ℝ)^(k+1) := by
      exact_mod_cast (Nat.le_of_lt (k+1).lt_two_pow_self)
    have h := mul_le_mul_of_nonneg_right hk
      (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k)
    have he : (2:ℝ)^(k+1)*(1/2:ℝ)^k = 2 := by
      rw [pow_succ]
      calc
        (2:ℝ)^k*2*(1/2:ℝ)^k = 2*((2:ℝ)*(1/2))^k := by rw [mul_pow]; ring
        _ = 2 := by norm_num
    simpa only [Nat.add_sub_cancel, he] using h

/- Source06 b(r) has an explicit pointwise majorant in terms of the
actual reciprocal band masses. This is not a majorant for a surrogate A. -/



/- Exact source owner: SourceShiftTwoDeletedCoefficientPolylog.lean; original line 27. -/
theorem source_deleted_weight_le_group_product
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (R : ℕ) (ν : ℝ) (hν : 0 < ν)
    (hQ : ∀ b p, p ∈ Q b → p.Prime)
    (hDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hQn : (Q b).Nonempty)
    (hV : ∀ g, ν ≤ ∑ p ∈ P g, (p:ℝ)⁻¹) :
    0 ≤ sourceDeletedWeight r Q P b i R ∧
      sourceDeletedWeight r Q P b i R ≤ (2/ν)^(Fintype.card G) := by
  have hd0 := source_deleted_Q_nonneg r Q b i
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) R)
  have hd1 := source_deleted_Q_le_one r Q b i
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) R) hQ hDisj hQn
  have hW0 := source_original_W1_nonneg P R
  have hW : sourceOriginalW1 P R ≤ (2/ν)^(Fintype.card G) := by
    unfold sourceOriginalW1
    calc
      _ ≤ ∏ _g : G, (2/ν) := by
        apply Finset.prod_le_prod₀
        · intro g hg
          unfold shiftTwoOriginalGroupFactor
          positivity
        · intro g hg
          unfold shiftTwoOriginalGroupFactor
          have hv := hV g
          have hvp : 0 < ∑ p ∈ P g, (p:ℝ)⁻¹ := hν.trans_le hv
          calc
            _ ≤ 2/(∑ p ∈ P g, (p:ℝ)⁻¹) :=
              div_le_div_of_nonneg_right (source_half_mark_le_two _) hvp.le
            _ ≤ 2/ν := div_le_div_of_nonneg_left (by norm_num) hν hv
      _ = _ := by simp [div_pow]
  rcases source_original_parity_projection_zero_or_one (Finset.univ.biUnion P) R with h | h
  · simp [sourceDeletedWeight, h]
    positivity
  · simp only [sourceDeletedWeight, h, mul_one]
    exact ⟨mul_nonneg hW0 hd0,
      (mul_le_mul_of_nonneg_left hd1 hW0).trans (by simpa using hW)⟩

/- Actual closed P bands have a fixed positive reciprocal mass uniformly
in ALL original moving groups. The floor is derived from native PNT. -/



/- Exact source owner: SourceShiftTwoDeletedCoefficientPolylog.lean; original line 68. -/
theorem source_original_P_all_reciprocal_floor_eventually (r₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ g : sourceOriginalPAllGroupType r₀ L,
      Real.log (12/11:ℝ)/4 ≤
        ∑ p ∈ sourceOriginalPAllActualBands r₀ L g, (p:ℝ)⁻¹ := by
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.1 source_P_group_two_half_prime_mass
  have hPow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually
    (eventually_ge_atTop (max T 0))
  filter_upwards [hPow,eventually_ge_atTop (1:ℝ)] with L hLarge hL
  intro g
  let t : ℝ := (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val
  have ht : max T 0 ≤ t := hLarge.trans
    (source_original_P_all_actual_band_lower r₀ L hL g)
  have hfloor := (hT t ((le_max_left T 0).trans ht)).1
  have hs := source_original_P_short_band_subset t 1 (11/10)
    ((le_max_right T 0).trans ht) (by norm_num) (by norm_num) (by norm_num)
  exact hfloor.trans (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p)))

/- A fixed exponent, independent of the source depth and later precision. -/



/- Exact source owner: SourceShiftTwoClosedMacroBands.lean; original line 32. -/
theorem source_closed_prime_log_band_floor_unconditional
    (a M u v : ℝ) (ha : 0 < a)
    (hau : a ≤ u) (huv : u ≤ v) (hvM : v ≤ M)
    (hratio : (6/5:ℝ)*u ≤ v) :
    ∀ᶠ L : ℝ in atTop,
      Real.log (6/5:ℝ)/2 ≤
        ∑ p ∈ sourceClosedPrimeLogBand L u v, (p:ℝ)⁻¹ := by
  filter_upwards [source_prime_log_band_floor_unconditional
    a M u v ha hau huv hvM hratio] with L hLower
  have hSubset := source_prime_log_band_subset_closed L u v
  have hCompare :
      (∑ p ∈ sourcePrimeLogBand L u v, (p:ℝ)⁻¹) ≤
        ∑ p ∈ sourceClosedPrimeLogBand L u v, (p:ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun p hp hnot => inv_nonneg.mpr (Nat.cast_nonneg p))
  exact hLower.trans hCompare

/- Exact source Q_j closed macro bands; remaining micro bands
are unchanged, including factorial multiplicities. -/



/- Exact source owner: SourceOriginalActualHarmonicControl.lean; original line 46. -/
theorem source_original_admissible_all_scales
    (r₀ d j : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 ≤ L)
    (hd : sourceOriginalDepthAdmissible r₀ d L) (hj : j ≤ d) :
    20*Real.log L ≤ sourceOriginalQActualExponent r₀ j * L := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast (by omega : 0 < r₀)
  have hs : 0 ≤ sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    positivity
  have hp : (2:ℝ)^j ≤ (2:ℝ)^d := by
    exact pow_le_pow_right₀ (by norm_num) hj
  have hdiv : sourceOriginalQ0Scale r₀/(2:ℝ)^d ≤
      sourceOriginalQ0Scale r₀/(2:ℝ)^j :=
    div_le_div_of_nonneg_left hs (by positivity) hp
  have hh := mul_le_mul_of_nonneg_right hdiv hL
  exact hd.trans hh

/- The source minimum scale tends to infinity. Consequently actual
moving Q bands all inherit the same native PNT floor. -/



/- Exact source owner: SourceOriginalActualHarmonicControl.lean; original line 64. -/
theorem source_original_admissible_all_band_floors_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ d,
      sourceOriginalDepthAdmissible r₀ d L → ∀ j, j ≤ d →
      Real.log (6/5:ℝ)/2 ≤
        ∑ p ∈ sourceClosedPrimeLogBand L (sourceOriginalQActualExponent r₀ j)
          ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j), (p:ℝ)⁻¹ := by
  have hPNT := source_closed_prime_log_band_floor_unconditional
    1 (6/5) 1 (6/5) (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hPNT
  have hScale : ∀ᶠ L : ℝ in atTop, t₀ ≤ 20*Real.log L := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (t₀/20)] with L h
    linarith
  filter_upwards [hScale, eventually_ge_atTop (0:ℝ)] with L hScaleL hL
  intro d hd j hj
  let t := sourceOriginalQActualExponent r₀ j * L
  have ht : t₀ ≤ t :=
    hScaleL.trans (source_original_admissible_all_scales r₀ d j L hr₀ hL hd hj)
  have hh := ht₀ t ht
  have hBand : sourceClosedPrimeLogBand t 1 (6/5) =
      sourceClosedPrimeLogBand L (sourceOriginalQActualExponent r₀ j)
        ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j) := by
    unfold sourceClosedPrimeLogBand
    dsimp [t]
    congr 4 <;> ring
  simpa only [hBand] using hh

/- Both positivity of moving HQ and the fixed macro/micro comparison
are derived from the source admissibility and native PNT. -/



/- Exact source owner: SourceShiftTwoDeletedCoefficientPolylog.lean; original line 93. -/
theorem source_original_deleted_coefficient_polylog_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ R : ℕ,
      0 ≤ sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ∧
      sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ≤ L^sourceDeletedCoefficientExponent := by
  let ν : ℝ := Real.log (12/11:ℝ)/4
  let A : ℝ := max (2/ν) 2
  let C : ℝ := 3 + (Real.log 2)⁻¹
  have hν : 0 < ν := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hA : 0 < A := (by norm_num : (0:ℝ)<2).trans_le (le_max_right _ _)
  have hAlog : 0 ≤ Real.log A := Real.log_nonneg ((by norm_num : (1:ℝ)≤2).trans (le_max_right _ _))
  have hQfloor := source_original_admissible_all_band_floors_eventually r₀ hr₀
  filter_upwards [source_original_P_all_reciprocal_floor_eventually r₀,
    source_original_literal_depth_properties_eventually r₀ hr₀,
    hQfloor, eventually_ge_atTop (Real.exp 1)] with L hPfloor hdepth hQfloors hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  let d := sourceOriginalLiteralDepth r₀ L
  let Q := sourceOriginalQActualBands r₀ d L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (d+1) := ⟨0,by omega⟩
  let i : Fin r₀ := ⟨0,by omega⟩
  have hQn : (Q b).Nonempty := by
    have hh := hQfloors d hdepth.1 0 (Nat.zero_le d)
    have hlog : 0 < Real.log (6/5:ℝ)/2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
    by_contra hn
    have hz : Q b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change Real.log (6/5:ℝ)/2 ≤ ∑ p ∈ Q b, (p:ℝ)⁻¹ at hh
    rw [hz, Finset.sum_empty] at hh
    linarith
  have hcard : (Fintype.card (sourceOriginalPAllGroupType r₀ L):ℝ) ≤ C*Real.log L := by
    rw [Fintype.card_coe]
    exact source_original_P_all_group_card_log r₀ L hr₀ hL
  have hpoly : A^(Fintype.card (sourceOriginalPAllGroupType r₀ L)) ≤ L^sourceDeletedCoefficientExponent := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hcard hAlog
    dsimp [sourceDeletedCoefficientExponent, A, C, ν] at *
    nlinarith
  intro R
  have hbound := source_deleted_weight_le_group_product r₀ Q P b i R ν hν
    (fun j p hp => source_original_Q_actual_prime r₀ d L j p hp)
    (source_original_Q_actual_all_disjoint r₀ d L hr₀ hLp) hQn hPfloor
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  exact (pow_le_pow_left₀ (by positivity : (0:ℝ)≤2/ν) (le_max_left _ _) _).trans hpoly



/- Exact source owner: SourceShiftTwoPrimitiveBilinear.lean; original line 7. -/
noncomputable def sourcePrimitiveMoment (S : Finset ℕ) (M N : ℕ)
    (a : ℕ → ℂ) : ℝ :=
  ∑ q ∈ S, (q.totient : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
      ‖∑ n ∈ Finset.Ioc M (M+N), a n * χ n‖^2 else 0



/- Exact source owner: SourceShiftTwoPrimitiveBilinear.lean; original line 20. -/
theorem source_primitive_bilinear_cauchy (S : Finset ℕ)
    (M₁ N₁ M₂ N₂ : ℕ) (a b : ℕ → ℂ) :
    sourcePrimitiveBilinear S M₁ N₁ M₂ N₂ a b ≤
      Real.sqrt (sourcePrimitiveMoment S M₁ N₁ a) *
      Real.sqrt (sourcePrimitiveMoment S M₂ N₂ b) := by
  classical
  let T := S.sigma (fun q => (Finset.univ : Finset (DirichletCharacter ℂ q)))
  let A : (q : ℕ) × DirichletCharacter ℂ q → ℝ := fun c =>
    if c.2.IsPrimitive then Real.sqrt ((c.1.totient : ℝ)⁻¹) *
      ‖∑ n ∈ Finset.Ioc M₁ (M₁+N₁), a n * c.2 n‖ else 0
  let B : (q : ℕ) × DirichletCharacter ℂ q → ℝ := fun c =>
    if c.2.IsPrimitive then Real.sqrt ((c.1.totient : ℝ)⁻¹) *
      ‖∑ n ∈ Finset.Ioc M₂ (M₂+N₂), b n * c.2 n‖ else 0
  have heA : (∑ c ∈ T, A c ^ 2) = sourcePrimitiveMoment S M₁ N₁ a := by
    rw [Finset.sum_sigma]
    unfold sourcePrimitiveMoment
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hp : χ.IsPrimitive
    · simp [A, hp, mul_pow, Real.sq_sqrt (show 0 ≤ (q.totient : ℝ)⁻¹ by positivity)]
    · simp [A, hp]
  have heB : (∑ c ∈ T, B c ^ 2) = sourcePrimitiveMoment S M₂ N₂ b := by
    rw [Finset.sum_sigma]
    unfold sourcePrimitiveMoment
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hp : χ.IsPrimitive
    · simp [B, hp, mul_pow, Real.sq_sqrt (show 0 ≤ (q.totient : ℝ)⁻¹ by positivity)]
    · simp [B, hp]
  have heAB : (∑ c ∈ T, A c * B c) = sourcePrimitiveBilinear S M₁ N₁ M₂ N₂ a b := by
    rw [Finset.sum_sigma]
    unfold sourcePrimitiveBilinear
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hp : χ.IsPrimitive
    · simp only [A, B, hp, if_true, norm_mul]
      have hs := Real.sq_sqrt (show 0 ≤ (q.totient : ℝ)⁻¹ by positivity)
      calc
        _ = Real.sqrt ((q.totient : ℝ)⁻¹)^2 * (‖∑ n ∈ Finset.Ioc M₁ (M₁+N₁), a n * χ n‖ * ‖∑ n ∈ Finset.Ioc M₂ (M₂+N₂), b n * χ n‖) := by ring
        _ = _ := by rw [hs]
    · simp [A, B, hp]
  have hc := Real.sum_mul_le_sqrt_mul_sqrt T A B
  rw [heA, heB, heAB] at hc
  exact hc



/- Exact source owner: SourceShiftTwoPrimitiveBilinear.lean; original line 74. -/
theorem source_primitive_dyadic_moment (F M N : ℕ) (hF : 1 ≤ F) (a : ℕ → ℂ) :
    sourcePrimitiveMoment (Finset.Ioc F (2*F)) M N a ≤
      (((2*F : ℕ) : ℝ)^2 + Real.pi * N) / (F : ℝ) *
        ∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2 := by
  classical
  have hFp : (0 : ℝ) < F := by exact_mod_cast (by omega : 0 < F)
  let E : ℕ → ℝ := fun q =>
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
      ‖∑ n ∈ Finset.Ioc M (M+N), a n * χ n‖^2 else 0
  have hE (q : ℕ) : 0 ≤ E q := by
    apply Finset.sum_nonneg
    intro χ hχ
    split_ifs <;> positivity
  have hterm (q : ℕ) (hq : q ∈ Finset.Ioc F (2*F)) :
      (q.totient : ℝ)⁻¹ * E q ≤ (F : ℝ)⁻¹ * ((q : ℝ)/(q.totient : ℝ) * E q) := by
    have hq' := (Finset.mem_Ioc.mp hq).1
    have hqF : (F : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt hq')
    have htot : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
    calc
      _ ≤ ((q : ℝ)/(F : ℝ)) * ((q.totient : ℝ)⁻¹ * E q) :=
        le_mul_of_one_le_left (mul_nonneg (by positivity) (hE q)) ((le_div_iff₀ hFp).mpr (by simpa using hqF))
      _ = _ := by ring
  unfold sourcePrimitiveMoment
  calc
    _ ≤ (F : ℝ)⁻¹ * ∑ q ∈ Finset.Ioc F (2*F), (q : ℝ)/(q.totient : ℝ) * E q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (F : ℝ)⁻¹ * ∑ q ∈ Finset.Icc 1 (2*F), (q : ℝ)/(q.totient : ℝ) * E q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have h := Finset.mem_Ioc.mp hq
        exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
      · intro q hq hnq
        exact mul_nonneg (by positivity) (hE q)
    _ ≤ (F : ℝ)⁻¹ * ((((2*F : ℕ) : ℝ)^2 + Real.pi*N) *
        ∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Chen.LargeSieve.large_sieve_character (2*F) M N a
    _ = _ := by ring


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Conductor004 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoPrimitiveBilinear.lean; original line 116. -/
theorem source_primitive_dyadic_bilinear (F M₁ N₁ M₂ N₂ : ℕ) (hF : 1 ≤ F)
    (a b : ℕ → ℂ) :
    sourcePrimitiveBilinear (Finset.Ioc F (2*F)) M₁ N₁ M₂ N₂ a b ≤
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) *
        ∑ n ∈ Finset.Ioc M₁ (M₁+N₁), ‖a n‖^2) *
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
        ∑ n ∈ Finset.Ioc M₂ (M₂+N₂), ‖b n‖^2) := by
  apply (source_primitive_bilinear_cauchy _ _ _ _ _ _ _).trans
  exact mul_le_mul (Real.sqrt_le_sqrt (source_primitive_dyadic_moment F M₁ N₁ hF a))
    (Real.sqrt_le_sqrt (source_primitive_dyadic_moment F M₂ N₂ hF b))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 54. -/
theorem source_original_deleted_bilinear_bound_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (F M₁ N₁ M₂ N₂ h : ℕ) (hF : 1 ≤ F)
      (ζ : ℕ → ℂ) (hζ : ∀ n, ‖ζ n‖ = 1),
      sourcePrimitiveBilinear (Finset.Ioc F (2*F)) M₁ N₁ M₂ N₂
        (sourceDeletedPrimePhase r₀ L h ζ)
        (sourceDeletedResidualPhase r₀ hr₀ L h ζ) ≤
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) * N₁) *
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
        ((N₂ : ℝ)*(L^sourceDeletedCoefficientExponent)^2)) := by
  filter_upwards [source_original_deleted_coefficient_polylog_eventually r₀ hr₀,
    eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro F M₁ N₁ M₂ N₂ h hF ζ hζ
  have hH : 0 ≤ L^sourceDeletedCoefficientExponent := Real.rpow_nonneg (by linarith) _
  apply (source_primitive_dyadic_bilinear F M₁ N₁ M₂ N₂ hF _ _).trans
  apply mul_le_mul
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (source_deleted_prime_phase_energy r₀ L h M₁ N₁ ζ hζ) (by positivity)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left
      (source_deleted_residual_phase_energy r₀ hr₀ L h M₂ N₂ ζ hζ _ hb hH) (by positivity)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

/- Expand a separated prime/residual Fourier integrand exactly. -/



/- Exact source owner: SourceShiftTwoWeightedFourier.lean; original line 59. -/
theorem source_original_deleted_mellin_bilinear_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (F M₁ N₁ M₂ N₂ h : ℕ) (hF : 1 ≤ F) (t : ℝ),
      sourcePrimitiveBilinear (Finset.Ioc F (2*F)) M₁ N₁ M₂ N₂
        (sourceDeletedPrimePhase r₀ L h (sourceMellinPhase t))
        (sourceDeletedResidualPhase r₀ hr₀ L h (sourceMellinPhase t)) ≤
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) * N₁) *
      Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
        ((N₂ : ℝ)*(L^sourceDeletedCoefficientExponent)^2)) := by
  filter_upwards [source_original_deleted_bilinear_bound_eventually r₀ hr₀] with L hL
  intro F M₁ N₁ M₂ N₂ h hF t
  exact hL F M₁ N₁ M₂ N₂ h hF (sourceMellinPhase t) (source_mellin_phase_norm t)



/- Exact source owner: SourceShiftTwoDeletedBilinearBound.lean; original line 79. -/
theorem source_deleted_phase_box_factorization
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (h M₁ N₁ M₂ N₂ d : ℕ)
    (ζ : ℕ → ℂ) (χ : DirichletCharacter ℂ d) :
    (∑ p ∈ Finset.Ioc M₁ (M₁+N₁), sourceDeletedPrimePhase r₀ L h ζ p * χ p) *
      (∑ R ∈ Finset.Ioc M₂ (M₂+N₂), sourceDeletedResidualPhase r₀ hr₀ L h ζ R * χ R) =
    ∑ p ∈ Finset.Ioc M₁ (M₁+N₁), ∑ R ∈ Finset.Ioc M₂ (M₂+N₂),
      if (p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h) ∧ R.Coprime h
      then (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
        ζ p * ζ R * χ p * χ R else 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  unfold sourceDeletedPrimePhase sourceDeletedResidualPhase
  split_ifs <;> simp_all <;> ring



/- Exact source owner: SourceShiftTwoWeightedFourier.lean; original line 53. -/
theorem source_mellin_phase_continuous (n : ℕ) :
    Continuous (fun t => sourceMellinPhase t n) := by
  unfold sourceMellinPhase
  fun_prop

/- The actual source box integrand uniform estimate in genuine Mellin frequency. -/



/- Exact source owner: SourceShiftTwoSmoothBoxSaving.lean; original line 7. -/
theorem source_finite_mellin_box_integrable
    (P R : Finset ℕ) (c : ℕ → ℕ → ℂ) (k : ℝ → ℂ) (hk : Integrable k) :
    Integrable (fun t => k t * (∑ p ∈ P, ∑ r ∈ R,
      c p r * sourceMellinPhase t p * sourceMellinPhase t r)) := by
  have hi (p r : ℕ) : Integrable (fun t =>
      k t * (c p r * sourceMellinPhase t p * sourceMellinPhase t r)) := by
    apply hk.mul_bdd (c := ‖c p r‖)
    · exact ((continuous_const.mul (source_mellin_phase_continuous p)).mul
        (source_mellin_phase_continuous r)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by
        simp only [norm_mul, source_mellin_phase_norm, mul_one, le_refl])
  have hs := integrable_finset_sum P (fun p hp =>
    integrable_finset_sum R (fun r hr => hi p r))
  simpa only [← Finset.mul_sum] using hs



/- Exact source owner: SourceShiftTwoSmoothBoxSaving.lean; original line 22. -/
theorem source_original_mellin_box_product_integrable
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ)
    (h M₁ N₁ M₂ N₂ d : ℕ) (χ : DirichletCharacter ℂ d) (k : ℝ → ℂ)
    (hk : Integrable k) :
    Integrable (fun t => k t *
      sourceDeletedMellinBoxProduct r₀ hr₀ L h M₁ N₁ M₂ N₂ d χ t) := by
  let c : ℕ → ℕ → ℂ := fun p R =>
    if (p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h) ∧ R.Coprime h
    then (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) * χ p * χ R else 0
  have hc := source_finite_mellin_box_integrable (Finset.Ioc M₁ (M₁+N₁))
    (Finset.Ioc M₂ (M₂+N₂)) c k hk
  convert hc using 1
  funext t
  unfold sourceDeletedMellinBoxProduct
  rw [source_deleted_phase_box_factorization r₀ hr₀ L h M₁ N₁ M₂ N₂ d (sourceMellinPhase t) χ]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro R hR
  dsimp only [c]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero]
  <;> congr 1
  <;> ring

/- Full primitive conductor block saving for the ORIGINAL smooth source box,
conditional only on explicit ordinary Mellin inversion of Ψ with integrable kernel.
No terminal Echi estimate, TypeII or prime mass is a premise. -/



/- Exact source owner: SourceShiftTwoFourierBox.lean; original line 9. -/
theorem source_finite_mellin_box_inversion
    (P R : Finset ℕ) (c : ℕ → ℕ → ℂ) (ψ : ℕ → ℕ → ℂ) (k : ℝ → ℂ)
    (hk : Integrable k)
    (hrep : ∀ p ∈ P, ∀ r ∈ R,
      ψ p r = ∫ t, k t * sourceMellinPhase t p * sourceMellinPhase t r) :
    (∑ p ∈ P, ∑ r ∈ R, c p r * ψ p r) =
      ∫ t, k t * (∑ p ∈ P, ∑ r ∈ R,
        c p r * sourceMellinPhase t p * sourceMellinPhase t r) := by
  have hi (p r : ℕ) : Integrable (fun t =>
      k t * (c p r * sourceMellinPhase t p * sourceMellinPhase t r)) := by
    apply hk.mul_bdd (c := ‖c p r‖)
    · have hcont : Continuous (fun t =>
        c p r * sourceMellinPhase t p * sourceMellinPhase t r) :=
        (continuous_const.mul (source_mellin_phase_continuous p)).mul (source_mellin_phase_continuous r)
      exact hcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by
        simp only [norm_mul, source_mellin_phase_norm, mul_one, le_refl])
  calc
    _ = ∑ p ∈ P, ∑ r ∈ R, ∫ t,
        k t * (c p r * sourceMellinPhase t p * sourceMellinPhase t r) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      rw [hrep p hp r hr]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by ring)
    _ = ∫ t, ∑ p ∈ P, ∑ r ∈ R,
        k t * (c p r * sourceMellinPhase t p * sourceMellinPhase t r) := by
      rw [integral_finset_sum P (fun p hp =>
        integrable_finset_sum R (fun r hr => hi p r))]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_finset_sum R (fun r hr => hi p r)]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by simp_rw [Finset.mul_sum])



/- Exact source owner: SourceShiftTwoFourierBox.lean; original line 67. -/
theorem source_original_smooth_box_mellin_inversion
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ)
    (h M₁ N₁ M₂ N₂ d : ℕ) (χ : DirichletCharacter ℂ d) (k : ℝ → ℂ)
    (hk : Integrable k)
    (hrep : ∀ p ∈ Finset.Ioc M₁ (M₁+N₁), ∀ R ∈ Finset.Ioc M₂ (M₂+N₂),
      (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ) =
        ∫ t, k t * sourceMellinPhase t p * sourceMellinPhase t R) :
    sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ d χ =
      ∫ t, k t * sourceDeletedMellinBoxProduct r₀ hr₀ L h M₁ N₁ M₂ N₂ d χ t := by
  let c : ℕ → ℕ → ℂ := fun p R =>
    if (p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h) ∧ R.Coprime h
    then (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) * χ p * χ R else 0
  have hinv := source_finite_mellin_box_inversion (Finset.Ioc M₁ (M₁+N₁))
    (Finset.Ioc M₂ (M₂+N₂)) c
    (fun p R => (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ)) k hk hrep
  calc
    _ = ∑ p ∈ Finset.Ioc M₁ (M₁+N₁), ∑ R ∈ Finset.Ioc M₂ (M₂+N₂),
      c p R * (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro R hR
        dsimp only [c, sourceDeletedSmoothBoxCharacter]
        simp only [ite_mul,mul_ite,zero_mul,mul_zero]
        <;> congr 1
        <;> ring
    _ = _ := hinv.trans (by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      unfold sourceDeletedMellinBoxProduct
      dsimp only
      rw [source_deleted_phase_box_factorization r₀ hr₀ L h M₁ N₁ M₂ N₂ d (sourceMellinPhase t) χ]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro R hR
      dsimp only [c]
      simp only [ite_mul,mul_ite,zero_mul,mul_zero]
      <;> congr 1
      <;> ring)



/- Exact source owner: SourceShiftTwoWeightedFourier.lean; original line 9. -/
theorem source_weighted_integral_norm_sum
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (k : ℝ → ℂ) (z : ι → ℝ → ℂ) (hk : Integrable k)
    (hi : ∀ i ∈ s, Integrable (fun t => k t * z i t))
    (B : ℝ) (hB : ∀ t, (∑ i ∈ s, w i * ‖z i t‖) ≤ B) :
    (∑ i ∈ s, w i * ‖∫ t, k t * z i t‖) ≤ B * ∫ t, ‖k t‖ := by
  calc
    _ ≤ ∑ i ∈ s, w i * ∫ t, ‖k t * z i t‖ := by
      apply Finset.sum_le_sum
      intro i his
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hw i his)
    _ = ∫ t, ∑ i ∈ s, w i * ‖k t * z i t‖ := by
      rw [integral_finset_sum s (fun i his => (hi i his).norm.const_mul (w i))]
      apply Finset.sum_congr rfl
      intro i his
      rw [integral_const_mul]
    _ ≤ ∫ t, ‖k t‖ * B := by
      apply integral_mono
      · exact integrable_finset_sum s (fun i his => (hi i his).norm.const_mul (w i))
      · exact hk.norm.mul_const B
      · intro t
        simp_rw [norm_mul]
        calc
          _ = ‖k t‖ * (∑ i ∈ s, w i * ‖z i t‖) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i his
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/- Mellin phase is well-defined even at 0 and has modulus 1 at every frequency. -/



/- Exact source owner: SourceShiftTwoSmoothBoxSaving.lean; original line 49. -/
theorem source_original_smooth_primitive_box_bound_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Ψ : ℝ → ℝ) (F M₁ N₁ M₂ N₂ h : ℕ)
      (hF : 1 ≤ F) (k : ℝ → ℂ) (hk : Integrable k),
      (∀ p ∈ Finset.Ioc M₁ (M₁+N₁), ∀ R ∈ Finset.Ioc M₂ (M₂+N₂),
        (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ) =
          ∫ t, k t * sourceMellinPhase t p * sourceMellinPhase t R) →
      (∑ d ∈ Finset.Ioc F (2*F), (d.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
          ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ d χ‖ else 0) ≤
      (Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) * N₁) *
        Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
          ((N₂ : ℝ)*(L^sourceDeletedCoefficientExponent)^2))) *
        ∫ t, ‖k t‖ := by
  filter_upwards [source_original_deleted_mellin_bilinear_eventually r₀ hr₀] with L hL
  intro Ψ F M₁ N₁ M₂ N₂ h hF k hk hrep
  let S := (Finset.Ioc F (2*F)).sigma (fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d)))
  let w : (d : ℕ) × DirichletCharacter ℂ d → ℝ := fun c =>
    if c.2.IsPrimitive then (c.1.totient : ℝ)⁻¹ else 0
  let z : (d : ℕ) × DirichletCharacter ℂ d → ℝ → ℂ := fun c =>
    sourceDeletedMellinBoxProduct r₀ hr₀ L h M₁ N₁ M₂ N₂ c.1 c.2
  have hw : ∀ c ∈ S, 0 ≤ w c := by intro c hc; dsimp [w]; split_ifs <;> positivity
  have hi : ∀ c ∈ S, Integrable (fun t => k t * z c t) := by
    intro c hc
    exact source_original_mellin_box_product_integrable r₀ hr₀ L h M₁ N₁ M₂ N₂ c.1 c.2 k hk
  have hb (t : ℝ) :
      (∑ c ∈ S, w c * ‖z c t‖) ≤
        Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) * N₁) *
        Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
          ((N₂ : ℝ)*(L^sourceDeletedCoefficientExponent)^2)) := by
    have hh := hL F M₁ N₁ M₂ N₂ h hF t
    convert hh using 1
    rw [Finset.sum_sigma]
    unfold sourcePrimitiveBilinear
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    dsimp [w, z, sourceDeletedMellinBoxProduct]
    split_ifs <;> simp
  have hnorm := source_weighted_integral_norm_sum S w hw k z hk hi _ hb
  convert hnorm using 1
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  dsimp [w,z]
  rw [← source_original_smooth_box_mellin_inversion r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ d χ k hk hrep]
  split_ifs <;> simp



/- Exact source owner: SourceShiftTwoSmoothBoxMellinDischarged.lean; original line 9. -/
theorem source_original_smooth_primitive_box_mellin_discharged
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
      (hΨsupport : Function.support Ψ ⊆ Set.Icc (1 : ℝ) 2)
      (F M₁ N₁ M₂ N₂ h : ℕ) (hF : 1 ≤ F),
      (∑ d ∈ Finset.Ioc F (2*F), (d.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
          ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ d χ‖ else 0) ≤
      (Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₁)/(F : ℝ)) * N₁) *
        Real.sqrt (((((2*F : ℕ) : ℝ)^2 + Real.pi*N₂)/(F : ℝ)) *
          ((N₂ : ℝ)*(L^sourceDeletedCoefficientExponent)^2))) * sourceLogMellinMass Ψ := by
  filter_upwards [source_original_smooth_primitive_box_bound_eventually r₀ hr₀] with L hL
  intro Ψ hΨ hΨsupport F M₁ N₁ M₂ N₂ h hF
  have hrep : ∀ p ∈ Finset.Ioc M₁ (M₁+N₁), ∀ R ∈ Finset.Ioc M₂ (M₂+N₂),
      (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ) =
        ∫ t, sourceLogMellinKernel Ψ L t * sourceMellinPhase t p * sourceMellinPhase t R := by
    intro p hp R hR
    exact source_log_mellin_inversion Ψ hΨ hΨsupport L p R
      (by have := (Finset.mem_Ioc.mp hp).1; omega)
      (by have := (Finset.mem_Ioc.mp hR).1; omega)
  have hb := hL Ψ F M₁ N₁ M₂ N₂ h hF (sourceLogMellinKernel Ψ L)
    (source_log_kernel_integrable Ψ hΨ hΨsupport L) hrep
  simpa only [source_log_kernel_uniform_mass] using hb



/- Exact source owner: SourceShiftTwoGlobalConductorBudget.lean; original line 37. -/
theorem source_original_primitive_box_dyadic_budget_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Ψ : ℝ → ℝ)
      (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
      (s h : ℕ) (a : ℕ×ℕ),
      (∑ f ∈ Finset.Ioc (2^s) (2*2^s),
        sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L f h a) ≤
          sourceEchiLargeBoxBudget Ψ L s a := by
  filter_upwards [source_original_smooth_primitive_box_mellin_discharged r₀ hr₀] with L hL
  intro Ψ hΨ hs s h a
  have hb := hL Ψ hΨ hs (2^s) (sourceEchiDyadLower a.1) (2^a.1)
    (sourceEchiDyadLower a.2) (2^a.2) h Nat.one_le_two_pow
  apply (Finset.sum_le_sum (fun f hf => ?_)).trans hb
  have hfp := (Finset.mem_Ioc.mp hf).1
  have hf0 : f ≠ 0 := by have := Nat.two_pow_pos s; omega
  have hf1 : f ≠ 1 := by have := Nat.one_le_two_pow (n := s); omega
  simp only [sourceOriginalPrimitiveBoxMass,dif_neg hf0,if_neg hf1]
  exact le_refl _

/- Finite conductor assembly to a true terminal Echi budget. The ONLY
cancellation premises are local small-conductor source-box bounds. All large
conductors use the already proved original Ψ primitive large sieve.

K is selected before the small-conductor accuracy; 2^K is the genuine conductor
cutoff, and S need only cover Q. No Echi or congruence conclusion is a premise. -/



/- Exact source owner: SourceShiftTwoGlobalSourceBoxMajorant.lean; original line 20. -/
theorem source_original_primitive_box_mass_nonneg
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (f h : ℕ) (a : ℕ×ℕ) :
    0 ≤ sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L f h a := by
  unfold sourceOriginalPrimitiveBoxMass
  split_ifs <;> positivity



/- Exact source owner: SourceShiftTwoGlobalSourceBoxMajorant.lean; original line 96. -/
theorem source_original_primitive_box_uniform_bound
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (f h : ℕ)
    (a : ℕ×ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ χ : DirichletCharacter ℂ f, χ.IsPrimitive →
      ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
        (sourceEchiDyadLower a.1) (2^a.1)
        (sourceEchiDyadLower a.2) (2^a.2) f χ‖ ≤ B) :
    sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L f h a ≤ B := by
  by_cases hf0 : f = 0
  · simpa [sourceOriginalPrimitiveBoxMass,hf0] using hB
  letI : NeZero f := ⟨hf0⟩
  by_cases hf1 : f = 1
  · simpa [sourceOriginalPrimitiveBoxMass,hf0,hf1] using hB
  simp only [sourceOriginalPrimitiveBoxMass,dif_neg hf0,if_neg hf1]
  have hcard : Fintype.card (DirichletCharacter ℂ f) = f.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f
  have htot : (f.totient:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0))
  calc
    _ ≤ (f.totient:ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ f, B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      split_ifs with hp
      · exact hbound χ hp
      · exact hB
    _ = B := by simp [hcard,htot]



/- Exact source owner: SourceShiftTwoGlobalConductorBudget.lean; original line 62. -/
theorem source_original_Echi_finite_small_large_budget_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Ψ : ℝ → ℝ)
      (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
      (hL : 0 < L) (Q J K S : ℕ) (hKS : K ≤ S) (hQ : Q ≤ 2^S)
      (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1)
      (small : ℕ×ℕ → ℝ) (hsmall0 : ∀ a, 0 ≤ small a),
      (∀ h ∈ (Finset.Icc 1 Q).filter Squarefree, ∀ a ∈ sourceEchiSourceBoxes r₀ L J,
        ∀ f ∈ Finset.Ioc 1 (2^K), ∀ χ : DirichletCharacter ℂ f,
          χ.IsPrimitive →
          ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
            (sourceEchiDyadLower a.1) (2^a.1)
            (sourceEchiDyadLower a.2) (2^a.2) f χ‖ ≤ small a) →
      (∑ d ∈ (Finset.range (Q+1)).filter (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
        sourceSquarefreeTotientSum Q *
          ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
            (((2^K:ℕ):ℝ)*small a +
              ∑ s ∈ Finset.Ico K S, sourceEchiLargeBoxBudget Ψ L s a) := by
  filter_upwards [source_original_primitive_box_dyadic_budget_eventually r₀ hr₀] with L hlarge
  intro Ψ hΨ hs hL Q J K S hKS hQ hN small hsmall0 hsmall
  let H := (Finset.Icc 1 Q).filter Squarefree
  let A := sourceEchiSourceBoxes r₀ L J
  let G : ℕ → ℕ → ℕ×ℕ → ℝ := sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L
  have hbound (h : ℕ) (hh : h ∈ H) (a : ℕ×ℕ) (ha : a ∈ A) :
      (∑ f ∈ Finset.Icc 1 Q, G f h a) ≤
        ((2^K:ℕ):ℝ)*small a + ∑ s ∈ Finset.Ico K S, sourceEchiLargeBoxBudget Ψ L s a := by
    have hf1 : G 1 h a = 0 := by simp [G,sourceOriginalPrimitiveBoxMass]
    have hsub : Finset.Icc 1 Q ⊆ insert 1 (Finset.Ioc 1 (2^S)) := by
      intro f hf
      have hm := Finset.mem_Icc.mp hf
      simp only [Finset.mem_insert,Finset.mem_Ioc]
      omega
    have hstart : (∑ f ∈ Finset.Icc 1 Q, G f h a) ≤ ∑ f ∈ Finset.Ioc 1 (2^S), G f h a := by
      have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun f hf hn => source_original_primitive_box_mass_nonneg r₀ hr₀ Ψ L f h a)
      change (∑ f ∈ Finset.Icc 1 Q, G f h a) ≤ ∑ f ∈ insert 1 (Finset.Ioc 1 (2^S)), G f h a at hb
      have hnot : 1 ∉ Finset.Ioc 1 (2^S) := by
        intro hi
        have hi' := Finset.mem_Ioc.mp hi
        omega
      rw [Finset.sum_insert hnot,hf1,zero_add] at hb
      exact hb
    have hsplit : Finset.Ioc 1 (2^S) = Finset.Ioc 1 (2^K) ∪ Finset.Ioc (2^K) (2^S) := by
      symm
      exact Finset.Ioc_union_Ioc_eq_Ioc Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) hKS)
    have hd : Disjoint (Finset.Ioc 1 (2^K)) (Finset.Ioc (2^K) (2^S)) := by
      apply Finset.disjoint_left.mpr
      intro f hf hg
      have := Finset.mem_Ioc.mp hf
      have := Finset.mem_Ioc.mp hg
      omega
    have hsmallB : (∑ f ∈ Finset.Ioc 1 (2^K), G f h a) ≤ ((2^K:ℕ):ℝ)*small a := by
      calc
        _ ≤ ∑ _f ∈ Finset.Ioc 1 (2^K), small a := by
          apply Finset.sum_le_sum
          intro f hf
          exact source_original_primitive_box_uniform_bound r₀ hr₀ Ψ L f h a (small a)
            (hsmall0 a) (hsmall h hh a ha f hf)
        _ ≤ ((2^K:ℕ):ℝ)*small a := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (hsmall0 a)
          have hcard : (Finset.Ioc 1 (2^K)).card ≤ 2^K := by simp
          exact_mod_cast hcard
    have hdyad : (∑ f ∈ Finset.Ioc (2^K) (2^S), G f h a) =
        ∑ s ∈ Finset.Ico K S, ∑ f ∈ Finset.Ioc (2^s) (2*2^s), G f h a := by
      have he := source_conductor_dyadic_sum S (fun f => G f h a)
      have hk := source_conductor_dyadic_sum K (fun f => G f h a)
      rw [hsplit,Finset.sum_union hd,hk] at he
      have hrange : Finset.range S = Finset.range K ∪ Finset.Ico K S := by
        ext s
        simp only [Finset.mem_union,Finset.mem_range,Finset.mem_Ico]
        omega
      have hd' : Disjoint (Finset.range K) (Finset.Ico K S) := by
        apply Finset.disjoint_left.mpr
        intro s hs ht
        have := Finset.mem_range.mp hs
        have := Finset.mem_Ico.mp ht
        omega
      rw [hrange,Finset.sum_union hd'] at he
      linarith
    rw [hsplit,Finset.sum_union hd] at hstart
    exact hstart.trans (add_le_add hsmallB (by
      rw [hdyad]
      exact Finset.sum_le_sum (fun s hs' => hlarge Ψ hΨ hs s h a)))
  have hb := source_original_Echi_source_box_majorant r₀ hr₀ Ψ hs L hL Q J hN
  calc
    _ ≤ ∑ h ∈ H, (h.totient:ℝ)⁻¹ * ∑ a ∈ A,
        (((2^K:ℕ):ℝ)*small a + ∑ s ∈ Finset.Ico K S, sourceEchiLargeBoxBudget Ψ L s a) := by
      apply hb.trans
      dsimp only [H,A]
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun a ha => hbound h hh a ha)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [H,A,sourceSquarefreeTotientSum,Finset.sum_filter]



/- Exact source owner: SourceShiftTwoQ0MaskCount.lean; original line 7. -/
theorem prime_set_product_dvd (s : Finset ℕ) (h : ℕ)
    (hp : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p ∣ h) : (∏ p ∈ s, p) ∣ h := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hn ih =>
    have hpr := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hpr.coprime_iff_not_dvd.mpr
      intro hdq
      have he := (Nat.prime_dvd_prime_iff_eq hpr (hs q hq)).mp hdq
      exact hn (he ▸ hq)
    rw [Finset.prod_insert hn]
    exact hc.mul_dvd_of_dvd_of_dvd (hd p (Finset.mem_insert_self _ _))
      (ih hs (fun q hq => hd q (Finset.mem_insert_of_mem hq)))

/- The actual original Q0 h-mask deletes only O(1) primes. The stronger
constant θ/α uses α=sourceOriginalQ0Scale=5/(11 r₀), with no dyadic floor loss. -/



/- Exact source owner: SourceShiftTwoQ0MaskCount.lean; original line 27. -/
theorem source_original_Q0_exceptional_prime_count
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L θ : ℝ) (hL : 0 < L) (h : ℕ)
    (hh : 0 < h) (hsize : (h : ℝ) ≤ Real.exp (θ*L)) :
    (( (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))).filter
        (fun p => ¬p.Coprime h)).card : ℝ) ≤ θ / sourceOriginalQ0Scale r₀ := by
  let Q := sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
  let s := Q.filter (fun p => ¬p.Coprime h)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    source_original_Q_actual_prime r₀ _ L _ p (Finset.mem_filter.mp hp).1
  have hdiv : (∏ p ∈ s, p) ∣ h := by
    apply prime_set_product_dvd s h hprime
    intro p hp
    exact not_not.mp ((hprime p hp).coprime_iff_not_dvd.not.mp (Finset.mem_filter.mp hp).2)
  have hlower (p : ℕ) (hp : p ∈ s) :
      Real.exp (sourceOriginalQ0Scale r₀ * L) ≤ (p : ℝ) := by
    have hb := (source_original_Q_actual_prime_range r₀ _ L hr₀ _ p
      (Finset.mem_filter.mp hp).1).1
    rw [← source_original_Q_actual_scale_eq_P_scale r₀ 0 L hr₀] at hb
    simpa only [sourceOriginalQActualExponent, pow_zero, div_one] using hb
  have hprod : Real.exp ((s.card : ℝ) * (sourceOriginalQ0Scale r₀ * L)) ≤ (h : ℝ) := by
    rw [Real.exp_nat_mul, ← Finset.prod_const]
    calc
      _ ≤ ∏ p ∈ s, (p : ℝ) := Finset.prod_le_prod₀ (fun p hp => by positivity) hlower
      _ = ((∏ p ∈ s, p : ℕ) : ℝ) := by simp
      _ ≤ h := by exact_mod_cast Nat.le_of_dvd hh hdiv
  have hexp := Real.exp_le_exp.mp (hprod.trans hsize)
  have hr : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
  have hα : 0 < sourceOriginalQ0Scale r₀ := by unfold sourceOriginalQ0Scale; positivity
  apply (le_div_iff₀ hα).mpr
  have he : (s.card : ℝ) * sourceOriginalQ0Scale r₀ ≤ θ := by nlinarith
  exact he

/- Uniform original Q0 prime-mask removal bound, now with a certified
constant rather than the unestimated number of deleted primes. -/



/- Exact source owner: SourceShiftTwoAbelBound.lean; original line 35. -/
theorem source_prime_mask_removal_bound
    (P : Finset ℕ) (h : ℕ) (a : ℕ → ℂ) (B : ℝ) (hB : ∀ p ∈ P, ‖a p‖ ≤ B) :
    ‖(∑ p ∈ P, if p.Coprime h then a p else 0) - (∑ p ∈ P, a p)‖ ≤
      ((P.filter (fun p => ¬p.Coprime h)).card : ℝ) * B := by
  have he : (∑ p ∈ P, if p.Coprime h then a p else 0) - (∑ p ∈ P, a p) =
      -(∑ p ∈ P.filter (fun p => ¬p.Coprime h), a p) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_filter, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : p.Coprime h
    · rw [if_pos hc, if_neg (not_not_intro hc)]
      simp
    · rw [if_neg hc, if_pos hc]
      simp
  rw [he, norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ P.filter (fun p => ¬p.Coprime h), B :=
      Finset.sum_le_sum (fun p hp => hB p (Finset.mem_filter.mp hp).1)
    _ = _ := by simp



/- Exact source owner: SourceShiftTwoSWSourcePrefixes.lean; original line 79. -/
theorem source_original_dyad_Q0_mask_bound
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L θ : ℝ) (hL : 0 < L)
    (h f j R : ℕ) [NeZero f] (hh : 0 < h) (hsize : (h:ℝ) ≤ Real.exp (θ*L))
    (χ : DirichletCharacter ℂ f) (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hΨ : ∀ t, |Ψ t| ≤ S) :
    ‖(∑ p ∈ sourceEchiDyad j,
      if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h
      then (Ψ (((p*R:ℕ):ℝ)/Real.exp L):ℂ)*χ p else 0) -
      (∑ p ∈ sourceEchiDyad j,
      if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
      then (Ψ (((p*R:ℕ):ℝ)/Real.exp L):ℂ)*χ p else 0)‖ ≤
        (θ/sourceOriginalQ0Scale r₀)*S := by
  let Q := sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
  let P := (sourceEchiDyad j).filter (fun p => p ∈ Q)
  let z : ℕ → ℂ := fun p => (Ψ (((p*R:ℕ):ℝ)/Real.exp L):ℂ)*χ p
  have hz : ∀ p ∈ P, ‖z p‖ ≤ S := by
    intro p hp
    dsimp [z]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (abs_nonneg _)).trans
      (by simpa using hΨ (((p*R:ℕ):ℝ)/Real.exp L))
  have hb := source_prime_mask_removal_bound P h z S hz
  have hs : P.filter (fun p => ¬p.Coprime h) ⊆ Q.filter (fun p => ¬p.Coprime h) := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).2,hm.2⟩
  have hc : ((P.filter (fun p => ¬p.Coprime h)).card:ℝ) ≤ θ/sourceOriginalQ0Scale r₀ := by
    have hcard : ((P.filter (fun p => ¬p.Coprime h)).card:ℝ) ≤
        ((Q.filter (fun p => ¬p.Coprime h)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hs
    exact hcard.trans (source_original_Q0_exceptional_prime_count r₀ hr₀ L θ hL h hh hsize)
  have he1 : (∑ p ∈ P, if p.Coprime h then z p else 0) =
      ∑ p ∈ sourceEchiDyad j, if p ∈ Q ∧ p.Coprime h then z p else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp_all
  have he2 : (∑ p ∈ P, z p) = ∑ p ∈ sourceEchiDyad j, if p ∈ Q then z p else 0 :=
    Finset.sum_filter _ _
  rw [he1,he2] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hc hS)



/- Exact source owner: SourceShiftTwoSmallConductorAbel.lean; original line 19. -/
theorem source_Ioc_sum_range {V : Type} [AddCommMonoid V]
    (M N : ℕ) (g : ℕ → V) :
    (∑ p ∈ Finset.Ioc M (M+N), g p) =
      ∑ i ∈ Finset.range N, g (M+i+1) := by
  symm
  apply Finset.sum_bij (fun i _ => M+i+1)
  · intro i hi
    apply Finset.mem_Ioc.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i hi j hj he
    omega
  · intro p hp
    have hh := Finset.mem_Ioc.mp hp
    refine ⟨p-M-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl



/- Exact source owner: SourceShiftTwoSmallConductorAbel.lean; original line 54. -/
theorem source_Q0_prime_abel_bound
    (r₀ : ℕ) (L : ℝ) (Ψ : ℝ → ℝ) (M N R f : ℕ)
    (χ : DirichletCharacter ℂ f) (H : ℝ) (hH : 0 ≤ H)
    (hpref : ∀ n, n ≤ N →
      ‖∑ p ∈ Finset.Ioc M (M+n),
        if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
          (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
        then χ p else 0‖ ≤ H) :
    ‖∑ p ∈ Finset.Ioc M (M+N),
      if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
      then (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ)*χ p else 0‖ ≤
        H*sourcePsiDiscreteVariation Ψ L M N R := by
  let Q := sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
  let w : ℕ → ℂ := fun i => (Ψ (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ)
  let g : ℕ → ℂ := fun i => if M+i+1 ∈ Q then χ ((M+i+1:ℕ):ZMod f) else 0
  have hg : ∀ n, n ≤ N → ‖∑ i ∈ Finset.range n, g i‖ ≤ H := by
    intro n hn
    have hb := hpref n hn
    rw [source_Ioc_sum_range] at hb
    simpa only [g,Q] using hb
  have hb := source_abel_norm_bound w g N H hH hg
  rw [source_Ioc_sum_range]
  convert hb using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w,g,Q]
    simp only [Nat.cast_mul,mul_zero,Nat.cast_add,Nat.cast_one,mul_ite]
  · rfl

/- A finite-box small-conductor estimate retaining both h masks.
Smoothing variation is explicit, so it cannot be silently assumed bounded. -/



/- Exact source owner: SourceShiftTwoSmallConductorAbel.lean; original line 88. -/
theorem source_original_small_conductor_box_bound
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ)
    (h M₁ N₁ M₂ N₂ f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f)
    (H V B E : ℝ) (hH : 0 ≤ H) (hV : 0 ≤ V) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hb : ∀ R, 0 ≤ sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ∧
      sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R ≤ B)
    (hpref : ∀ n, n ≤ N₁ →
      ‖∑ p ∈ Finset.Ioc M₁ (M₁+n),
        if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
          (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
        then χ p else 0‖ ≤ H)
    (hvar : ∀ R ∈ Finset.Ioc M₂ (M₂+N₂),
      sourcePsiDiscreteVariation Ψ L M₁ N₁ R ≤ V)
    (hmask : ∀ R ∈ Finset.Ioc M₂ (M₂+N₂),
      ‖(∑ p ∈ Finset.Ioc M₁ (M₁+N₁),
        if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
          (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h
        then (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ)*χ p else 0) -
      (∑ p ∈ Finset.Ioc M₁ (M₁+N₁),
        if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
          (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
        then (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ)*χ p else 0)‖ ≤ E) :
    ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ f χ‖ ≤
      (N₂:ℝ)*B*(H*V+E) := by
  let S : ℕ → ℂ := fun R => ∑ p ∈ Finset.Ioc M₁ (M₁+N₁),
    if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h
    then (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ)*χ p else 0
  have hS (R : ℕ) (hR : R ∈ Finset.Ioc M₂ (M₂+N₂)) : ‖S R‖ ≤ H*V+E := by
    have ha := source_Q0_prime_abel_bound r₀ L Ψ M₁ N₁ R f χ H hH hpref
    have hv := mul_le_mul_of_nonneg_left (hvar R hR) hH
    have hm := hmask R hR
    let U : ℂ := ∑ p ∈ Finset.Ioc M₁ (M₁+N₁),
      if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
      then (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ)*χ p else 0
    change ‖U‖ ≤ _ at ha
    change ‖S R-U‖ ≤ E at hm
    have ht := norm_add_le (S R-U) U
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith)
  have he : sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h M₁ N₁ M₂ N₂ f χ =
      ∑ R ∈ Finset.Ioc M₂ (M₂+N₂), if R.Coprime h then
        (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ)*χ R*S R else 0 := by
    unfold sourceDeletedSmoothBoxCharacter
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R hR
    dsimp only [S]
    by_cases hc : R.Coprime h
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [hc,and_true,mul_ite,mul_zero]
      congr 1
      · apply propext
        constructor
        · exact And.left
        · intro hq
          exact ⟨hq,hc⟩
      · ring
    · simp [hc]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _R ∈ Finset.Ioc M₂ (M₂+N₂), B*(H*V+E) := by
      apply Finset.sum_le_sum
      intro R hR
      split_ifs
      · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hb R).1]
        have hc := χ.norm_le_one (R : ZMod f)
        have hbc : sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R * ‖χ (R : ZMod f)‖ ≤ B :=
          (mul_le_mul_of_nonneg_left hc (hb R).1).trans (by simpa using (hb R).2)
        exact mul_le_mul hbc (hS R hR) (norm_nonneg _) hB
      · simp only [norm_zero]
        positivity
    _ = _ := by simp; ring



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 10. -/
noncomputable def sourceReciprocalAF : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹, by simp⟩



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 7. -/
noncomputable def sourceTotientAux : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then (n : ℝ)⁻¹ * (n.totient : ℝ)⁻¹ else 0,
    by simp⟩



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 58. -/
lemma source_reciprocal_af_nonneg (n : ℕ) : 0 ≤ sourceReciprocalAF n := by
  dsimp [sourceReciprocalAF]
  positivity



/- Exact source owner: SourceShiftTwoCongruenceSieve.lean; original line 62. -/
theorem shift_two_totient_prime_product (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) :
    ((∏ p ∈ s, p).totient : ℝ) = ∏ p ∈ s, ((p:ℝ)-1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hn ih =>
    have hps : p.Prime := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hps.coprime_iff_not_dvd.mpr
      intro hdiv
      have he : p = q := (Nat.dvd_prime (hs q hq)).mp hdiv |>.resolve_left hps.ne_one
      exact hn (he ▸ hq)
    rw [Finset.prod_insert hn, Nat.totient_mul hc, Nat.cast_mul,
      Finset.prod_insert hn, ih hs, Nat.totient_prime hps,
      Nat.cast_sub hps.one_le, Nat.cast_one]



/- Exact source owner: SourceShiftTwoNonunitEuler.lean; original line 10. -/
lemma shift_two_squarefree_totient_inverse (d : ℕ) (hd : Squarefree d) :
    (d.totient : ℝ)⁻¹ = ∏ p ∈ d.primeFactors, ((p : ℝ)-1)⁻¹ := by
  have hp : ∀ p ∈ d.primeFactors, p.Prime := fun p h => (Nat.mem_primeFactors.mp h).1
  have he := shift_two_totient_prime_product d.primeFactors hp
  rw [Nat.prod_primeFactors_of_squarefree hd] at he
  rw [he, Finset.prod_inv_distrib]



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 28. -/
lemma source_reciprocal_af_multiplicative : sourceReciprocalAF.IsMultiplicative := by
  constructor
  · simp [sourceReciprocalAF]
  · intro m n hc
    simp [sourceReciprocalAF, mul_comm]

/- Elementary squarefree convolution, independent of prime distribution. -/



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 15. -/
lemma source_totient_aux_multiplicative : sourceTotientAux.IsMultiplicative := by
  constructor
  · simp [sourceTotientAux, squarefree_one]
  · intro m n hc
    by_cases hm : Squarefree m <;> by_cases hn : Squarefree n
    · simp only [sourceTotientAux, ArithmeticFunction.coe_mk, if_pos hm, if_pos hn,
        if_pos ((Nat.squarefree_mul hc).mpr ⟨hm,hn⟩), Nat.totient_mul hc,
        Nat.cast_mul, mul_inv_rev]
      ring
    · simp [sourceTotientAux, Nat.squarefree_mul hc, hm, hn]
    · simp [sourceTotientAux, Nat.squarefree_mul hc, hm, hn]
    · simp [sourceTotientAux, Nat.squarefree_mul hc, hm, hn]


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Conductor005 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 35. -/
lemma source_totient_aux_convolution (n : ℕ) (hn : Squarefree n) :
    (sourceTotientAux * sourceReciprocalAF) n = (n.totient : ℝ)⁻¹ := by
  have hh := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
    source_totient_aux_multiplicative source_reciprocal_af_multiplicative hn
  rw [ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero] at hh
  rw [← hh, shift_two_squarefree_totient_inverse n hn]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hsf : Squarefree p := (Nat.prime_iff.mp hprime).squarefree
  change sourceTotientAux p + sourceReciprocalAF p = _
  simp only [ArithmeticFunction.add_apply, sourceTotientAux, sourceReciprocalAF,
    ArithmeticFunction.coe_mk, if_pos hsf, Nat.totient_prime hprime,
    Nat.cast_sub hprime.one_le, Nat.cast_one]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    linarith
  field_simp
  ring



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 55. -/
lemma source_totient_aux_nonneg (n : ℕ) : 0 ≤ sourceTotientAux n := by
  dsimp [sourceTotientAux]
  split_ifs <;> positivity



/- Exact source owner: SourceShiftTwoNonunitEuler.lean; original line 17. -/
lemma shift_two_primeFactors_injective_squarefree (M : Finset ℕ)
    (hM : ∀ d ∈ M, Squarefree d) :
    Set.InjOn Nat.primeFactors (↑M : Set ℕ) := by
  intro d hd e he h
  rw [← Nat.prod_primeFactors_of_squarefree (hM d hd),
      ← Nat.prod_primeFactors_of_squarefree (hM e he), h]

/- Genuine full-modulus moment at one prime, with no modulus-count loss. -/



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 67. -/
lemma source_reciprocal_telescope (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 : ℝ) / (((k+1 : ℕ) : ℝ) * ((k+2 : ℕ) : ℝ))) =
      1 - 1 / ((N+1 : ℕ) : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+2 ≠ 0 := by positivity
    field_simp
    <;> ring



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 80. -/
lemma source_prime_totient_aux_sum_le_one (N : ℕ) :
    (∑ p ∈ (Finset.range (N+1)).filter Nat.Prime,
      (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹) ≤ 1 := by
  let P := (Finset.range (N+1)).filter Nat.Prime
  let T := (Finset.range N).image (fun k => k+2)
  have hs : P ⊆ T := by
    intro p hp
    have hpm := Finset.mem_filter.mp hp
    have hle := Finset.mem_range.mp hpm.1
    have hge := hpm.2.two_le
    exact Finset.mem_image.mpr ⟨p-2, Finset.mem_range.mpr (by omega), by omega⟩
  have he : (∑ p ∈ T, (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹) =
      ∑ k ∈ Finset.range N, (1 : ℝ) / (((k+1 : ℕ) : ℝ) * ((k+2 : ℕ) : ℝ)) := by
    rw [Finset.sum_image (by intro a ha b hb h; dsimp at h; omega)]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    simp only [one_div, ← mul_inv_rev]
    congr 1
    ring
  calc
    _ ≤ ∑ p ∈ T, (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro p hp hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      have h0 : (0 : ℝ) ≤ ((k+2 : ℕ) : ℝ) := by positivity
      have h1 : (0 : ℝ) ≤ ((k+2 : ℕ) : ℝ)-1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      exact mul_nonneg (inv_nonneg.mpr h0) (inv_nonneg.mpr h1)
    _ = _ := he
    _ ≤ 1 := by
      rw [source_reciprocal_telescope]
      have : (0 : ℝ) ≤ 1 / ((N+1 : ℕ) : ℝ) := by positivity
      linarith



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 114. -/
lemma source_totient_aux_euler_cap (N : ℕ) :
    (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime,
      (1 + (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹)) ≤ Real.exp 1 := by
  calc
    _ ≤ ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime,
        Real.exp ((p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hprime := (Finset.mem_filter.mp hp).2
        have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp
          ((p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹)
    _ = Real.exp (∑ p ∈ (Finset.range (N+1)).filter Nat.Prime,
        (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (source_prime_totient_aux_sum_le_one N)



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 133. -/
lemma source_totient_aux_squarefree_product (d : ℕ) (hd : Squarefree d) :
    sourceTotientAux d = ∏ p ∈ d.primeFactors,
      (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹ := by
  simp only [sourceTotientAux, ArithmeticFunction.coe_mk, if_pos hd]
  rw [shift_two_squarefree_totient_inverse d hd,
    ← Nat.prod_primeFactors_of_squarefree hd]
  -- Freeze the prime-factor set before rewriting the numeric product.
  have he : (d : ℝ)⁻¹ = ∏ p ∈ d.primeFactors, (p : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [Nat.prod_primeFactors_of_squarefree hd, he, ← Finset.prod_mul_distrib]



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 144. -/
lemma source_totient_aux_sum_cap (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, sourceTotientAux d) ≤ Real.exp 1 := by
  let M := (Finset.Icc 1 N).filter Squarefree
  let P := (Finset.range (N+1)).filter Nat.Prime
  have hM : ∀ d ∈ M, Squarefree d := fun d hd => (Finset.mem_filter.mp hd).2
  have hs : M.image Nat.primeFactors ⊆ P.powerset := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    apply Finset.mem_powerset.mpr
    intro p hp
    have hm := Nat.mem_primeFactors.mp hp
    have hdpos : 0 < d := Nat.pos_of_ne_zero (hM d hd).ne_zero
    have hle : p ≤ N := (Nat.le_of_dvd hdpos hm.2.1).trans
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm.1⟩
  have he : (∑ d ∈ Finset.Icc 1 N, sourceTotientAux d) =
      ∑ s ∈ M.image Nat.primeFactors, ∏ p ∈ s, (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹ := by
    rw [Finset.sum_image (shift_two_primeFactors_injective_squarefree M hM)]
    trans ∑ d ∈ M, sourceTotientAux d
    · simp only [M, Finset.sum_filter, sourceTotientAux, ArithmeticFunction.coe_mk]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro d hd
      exact source_totient_aux_squarefree_product d (hM d hd)
  rw [he]
  calc
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro s hs hn
      apply Finset.prod_nonneg
      intro p hp
      have hprime := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hs) hp)).2
      have h1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      positivity
    _ = ∏ p ∈ P, (1 + (p : ℝ)⁻¹ * ((p : ℝ)-1)⁻¹) := (Finset.prod_one_add P).symm
    _ ≤ Real.exp 1 := source_totient_aux_euler_cap N

/- Explicit elementary totient bound. No Mertens/PNT assumption or import. -/



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 61. -/
lemma source_totient_convolution_nonneg (n : ℕ) :
    0 ≤ (sourceTotientAux * sourceReciprocalAF) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun ab hab => mul_nonneg
    (source_totient_aux_nonneg _) (source_reciprocal_af_nonneg _))



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 184. -/
theorem source_squarefree_totient_sum_harmonic (N : ℕ) :
    sourceSquarefreeTotientSum N ≤ Real.exp 1 * (harmonic N : ℝ) := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp; omega
  unfold sourceSquarefreeTotientSum
  rw [hI]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (sourceTotientAux * sourceReciprocalAF) d := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hsf : Squarefree d
      · rw [if_pos hsf, source_totient_aux_convolution d hsf]
      · rw [if_neg hsf]
        exact source_totient_convolution_nonneg d
    _ = ∑ ab ∈ ((Finset.Ioc 0 N) ×ˢ (Finset.Ioc 0 N)).filter
        (fun ab : ℕ × ℕ => ab.1*ab.2 ≤ N),
        sourceTotientAux ab.1 * sourceReciprocalAF ab.2 :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter _ _ N
    _ ≤ ∑ ab ∈ (Finset.Ioc 0 N) ×ˢ (Finset.Ioc 0 N),
        sourceTotientAux ab.1 * sourceReciprocalAF ab.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ab hab hn
      exact mul_nonneg (source_totient_aux_nonneg _) (source_reciprocal_af_nonneg _)
    _ = (∑ d ∈ Finset.Ioc 0 N, sourceTotientAux d) *
        (∑ d ∈ Finset.Ioc 0 N, sourceReciprocalAF d) := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ ≤ Real.exp 1 * (∑ d ∈ Finset.Ioc 0 N, sourceReciprocalAF d) := by
      apply mul_le_mul_of_nonneg_right
      · rw [← hI]
        exact source_totient_aux_sum_cap N
      · exact Finset.sum_nonneg (fun d hd => source_reciprocal_af_nonneg d)
    _ = Real.exp 1 * (harmonic N : ℝ) := by
      congr 1
      rw [harmonic_eq_sum_Icc, ← hI]
      push_cast
      rfl



/- Exact source owner: SourceShiftTwoNonunitHarmonic.lean; original line 90. -/
lemma source_squarefree_totient_sum_power_cutoff
    (L θ : ℝ) (hL : 2 ≤ L) (hθ : 0 < θ) (hθupper : θ ≤ 1/2) :
    sourceSquarefreeTotientSum ⌊(Real.exp L)^θ⌋₊ ≤ Real.exp 1 * L := by
  let N := ⌊(Real.exp L)^θ⌋₊
  have hpow : (Real.exp L)^θ = Real.exp (L*θ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    rw [hpow]
    norm_num only [Nat.cast_one]
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (L*θ) := Real.exp_le_exp.mpr (mul_nonneg (by linarith) hθ.le)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log N ≤ L*θ := by
    have hh := Real.log_le_log hN0 (Nat.floor_le (by positivity : 0 ≤ (Real.exp L)^θ))
    rw [hpow, Real.log_exp] at hh
    exact hh
  have hH := harmonic_le_one_add_log N
  have hsmall : (harmonic N : ℝ) ≤ L := by
    have := mul_le_mul_of_nonneg_left hθupper (by linarith : 0 ≤ L)
    linarith
  exact (source_squarefree_totient_sum_harmonic N).trans
    (mul_le_mul_of_nonneg_left hsmall (Real.exp_pos 1).le)



/- Exact source owner: SourceShiftTwoConditionalEchiTerminal.lean; original line 13. -/
theorem source_original_Echi_prefix_terminal_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
      (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
      (θ : ℝ) (hθ : 0 < θ) (hθu : θ < 1/2) (hL : 2 ≤ L)
      (J K S : ℕ) (hKS : K ≤ S)
      (hQ : ⌊(Real.exp L)^θ⌋₊ ≤ 2^S)
      (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1)
      (H : ℕ×ℕ → ℝ) (hH : ∀ a, 0 ≤ H a)
      (V BΨ : ℝ) (hV : 0 ≤ V) (hBΨ : 0 ≤ BΨ) (hΨbound : ∀ t, |Ψ t| ≤ BΨ),
      (∀ a ∈ sourceEchiSourceBoxes r₀ L J, ∀ R ∈ sourceEchiDyad a.2,
        sourcePsiDiscreteVariation Ψ L (sourceEchiDyadLower a.1) (2^a.1) R ≤ V) →
      (∀ a ∈ sourceEchiSourceBoxes r₀ L J, ∀ f ∈ Finset.Ioc 1 (2^K),
        ∀ χ : DirichletCharacter ℂ f, χ.IsPrimitive → ∀ n, n ≤ 2^a.1 →
          ‖∑ p ∈ Finset.Ioc (sourceEchiDyadLower a.1) (sourceEchiDyadLower a.1+n),
            if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
              (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
            then χ p else 0‖ ≤ H a) →
      (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
          (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
        Real.exp 1 * L * ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
          (((2^K:ℕ):ℝ)*((2^a.2:ℕ):ℝ)*L^sourceDeletedCoefficientExponent *
            (H a*V+(θ/sourceOriginalQ0Scale r₀)*BΨ) +
            ∑ s ∈ Finset.Ico K S, sourceEchiLargeBoxBudget Ψ L s a) := by
  filter_upwards [source_original_Echi_finite_small_large_budget_eventually r₀ hr₀,
    source_original_deleted_coefficient_polylog_eventually r₀ hr₀] with L hbudget hb
  intro Ψ hΨ hs θ hθ hθu hL J K S hKS hQ hN H hH V BΨ hV hBΨ hΨbound hvar hpref
  let Q := ⌊(Real.exp L)^θ⌋₊
  let A := sourceEchiSourceBoxes r₀ L J
  let small : ℕ×ℕ → ℝ := fun a =>
    ((2^a.2:ℕ):ℝ)*L^sourceDeletedCoefficientExponent *
      (H a*V+(θ/sourceOriginalQ0Scale r₀)*BΨ)
  have hLp : 0 < L := by linarith
  have hα : 0 < sourceOriginalQ0Scale r₀ := by
    have hr : (0:ℝ) < r₀ := by exact_mod_cast hr₀
    unfold sourceOriginalQ0Scale
    positivity
  have hsmall0 (a : ℕ×ℕ) : 0 ≤ small a := by
    dsimp [small]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hLp.le _))
      (add_nonneg (mul_nonneg (hH a) hV) (mul_nonneg (div_nonneg hθ.le hα.le) hBΨ))
  have hsmall : ∀ h ∈ (Finset.Icc 1 Q).filter Squarefree, ∀ a ∈ A,
      ∀ f ∈ Finset.Ioc 1 (2^K), ∀ χ : DirichletCharacter ℂ f, χ.IsPrimitive →
        ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
          (sourceEchiDyadLower a.1) (2^a.1)
          (sourceEchiDyadLower a.2) (2^a.2) f χ‖ ≤ small a := by
    intro h hh a ha f hf χ hprim
    have hm := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
    have hf0 : f ≠ 0 := by have := (Finset.mem_Ioc.mp hf).1; omega
    letI : NeZero f := ⟨hf0⟩
    have hsize : (h:ℝ) ≤ Real.exp (θ*L) := by
      have hx : (Real.exp L)^θ = Real.exp (θ*L) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
      have hnat : (h:ℝ) ≤ Q := by exact_mod_cast hm.2
      exact hnat.trans (by simpa only [Q,hx] using Nat.floor_le (by positivity : 0 ≤ (Real.exp L)^θ))
    exact source_original_small_conductor_box_bound r₀ hr₀ Ψ L h
      (sourceEchiDyadLower a.1) (2^a.1) (sourceEchiDyadLower a.2) (2^a.2) f χ
      (H a) V (L^sourceDeletedCoefficientExponent) ((θ/sourceOriginalQ0Scale r₀)*BΨ)
      (hH a) hV (Real.rpow_nonneg hLp.le _) (mul_nonneg (div_nonneg hθ.le hα.le) hBΨ)
      hb (hpref a ha f hf χ hprim) (hvar a ha)
      (fun R hR => source_original_dyad_Q0_mask_bound r₀ hr₀ L θ hLp h f a.1 R
        (by omega) hsize χ Ψ BΨ hBΨ hΨbound)
  have ht := hbudget Ψ hΨ hs hLp Q J K S hKS hQ hN small hsmall0 hsmall
  have hsum0 : 0 ≤ ∑ a ∈ A,
      (((2^K:ℕ):ℝ)*small a+∑ s ∈ Finset.Ico K S,sourceEchiLargeBoxBudget Ψ L s a) := by
    apply Finset.sum_nonneg
    intro a ha
    apply add_nonneg (mul_nonneg (by positivity) (hsmall0 a))
    apply Finset.sum_nonneg
    intro s hs'
    unfold sourceEchiLargeBoxBudget
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (source_log_mellin_mass_nonneg Ψ)
  have hharm := source_squarefree_totient_sum_power_cutoff L θ hL hθ hθu.le
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right hharm hsum0)
  simpa only [small,mul_assoc] using hfinal



/- Exact source owner: SourceShiftTwoSmallConductorAbel.lean; original line 37. -/
theorem source_closed_prime_interval_intersection (a b M N : ℕ) (ha : 1 ≤ a) :
    (Finset.Ioc M (M+N)).filter (fun p => p ∈ (Finset.Icc a b).filter Nat.Prime) =
      (Finset.Ioc (max M (a-1)) (min (M+N) b)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
    max_lt_iff, le_min_iff]
  constructor <;> intro h <;> aesop (add safe tactic (by omega))



/- Exact source owner: SourceShiftTwoSWSourcePrefixes.lean; original line 10. -/
theorem source_SW_original_Q0_prefixes (hSW : SourcePrimeSiegelWalfisz)
    (C A : ℝ) (hC : 0 < C) (hA : 0 < A) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ (r₀ : ℕ) (L : ℝ) (j f : ℕ) [NeZero f]
      (χ : DirichletCharacter ℂ f), Y ≤ (2:ℝ)^j → χ.IsPrimitive → χ ≠ 1 →
      (f:ℝ) ≤ (Real.log ((2:ℝ)^j))^C →
      ∀ n, n ≤ 2^j →
        ‖∑ p ∈ Finset.Ioc (sourceEchiDyadLower j) (sourceEchiDyadLower j+n),
          if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
            (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
          then χ p else 0‖ ≤
            K*(2:ℝ)^j*(Real.log ((2:ℝ)^j))^(-A) := by
  obtain ⟨K,hK,hbound⟩ := hSW C A hC hA
  obtain ⟨Y,hY⟩ := Filter.eventually_atTop.1 hbound
  refine ⟨K,Y,hK,?_⟩
  intro r₀ L j f inst χ hj hprim hnonprincipal hf n hn
  let a₀ : ℕ := ⌈Real.exp (sourceOriginalQ0Scale r₀*L)⌉₊
  let b₀ : ℕ := ⌊Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L)⌋₊
  have ha₀ : 1 ≤ a₀ := by
    have he := Nat.le_ceil (Real.exp (sourceOriginalQ0Scale r₀*L))
    have hpos := Real.exp_pos (sourceOriginalQ0Scale r₀*L)
    by_contra hz
    have ha0 : a₀ = 0 := by omega
    change Real.exp (sourceOriginalQ0Scale r₀*L) ≤ (a₀:ℝ) at he
    rw [ha0] at he
    norm_num at he
    linarith
  have hQ : sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) =
        (Finset.Icc a₀ b₀).filter Nat.Prime := by
    simp only [sourceOriginalQActualBands,sourceOriginalQActualExponent,
      pow_zero,div_one,sourceClosedPrimeLogBand]
    rfl
  let a : ℕ := max (sourceEchiDyadLower j) (a₀-1)
  let b : ℕ := min (sourceEchiDyadLower j+n) b₀
  have he : (∑ p ∈ Finset.Ioc (sourceEchiDyadLower j) (sourceEchiDyadLower j+n),
      if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
      then χ p else 0) =
      ∑ p ∈ Finset.Ioc a b, if p.Prime then χ p else 0 := by
    rw [hQ,← Finset.sum_filter,
      source_closed_prime_interval_intersection a₀ b₀ _ n ha₀,Finset.sum_filter]
  rw [he]
  by_cases hab : a ≤ b
  · have hal : (2:ℝ)^j ≤ (a:ℝ)+1 := by
      have hmax : sourceEchiDyadLower j ≤ a := le_max_left _ _
      have hp := Nat.two_pow_pos j
      have hnat : 2^j ≤ a+1 := by dsimp [sourceEchiDyadLower] at hmax; omega
      exact_mod_cast hnat
    have hbu : (b:ℝ) ≤ 2*(2:ℝ)^j := by
      have hb : b ≤ sourceEchiDyadLower j+n := min_le_left _ _
      have hnat : b ≤ 2*2^j := by
        dsimp [sourceEchiDyadLower] at hb
        omega
      exact_mod_cast hnat
    exact hY ((2:ℝ)^j) hj f a b χ hprim hnonprincipal hf hal hab hbu
  · have hz : Finset.Ioc a b = ∅ := by
      ext p
      have hemp : p ∉ Finset.Ioc a b := by
        intro hp
        have hp' := Finset.mem_Ioc.mp hp
        omega
      simp [hemp]
    rw [hz]
    simp only [Finset.sum_empty,norm_zero]
    have hlog : 0 ≤ Real.log ((2:ℝ)^j) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.rpow_nonneg hlog _)

/- The already checked actual Q0 deletion count localizes to every dyad.
The cost uses Ψ's uniform bound, never the number of all moduli. -/


end Green64Analytic.SourceBlockSieve

end

end

