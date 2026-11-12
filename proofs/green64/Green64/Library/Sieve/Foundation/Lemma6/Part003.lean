module

public import Green64.Library.Sieve.Foundation.Lemma6.Part002
public import Green64.Library.Sieve.Foundation.Analysis.Part001
public import Green64.Library.Sieve.Foundation.Lemma6.Part001
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.BiquadraticTruncation -/

section

namespace Chen

noncomputable def siegelTruncationConstant : ℝ := Real.exp (4 * Real.log 7112448 + 2)

theorem siegelTruncationConstant_pos : 0 < siegelTruncationConstant := Real.exp_pos _

/-- A logarithmic truncation length controls the Taylor tail and the retained power,
uniformly for every real argument between 7/8 and one. -/
theorem exists_biquadratic_truncation (q : ℕ) (hq : 2 ≤ q) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ β : ℝ, 7 / 8 < β → β < 1 →
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * ((2 / 3 : ℝ) * (2 - β)) ^ k /
        (1 - (2 / 3 : ℝ) * (2 - β)) ≤ 1 / 2 ∧
      (2 - β) ^ k ≤ siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpow : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ q)
  have hbase : (1 : ℝ) ≤ 42 * (q : ℝ) ^ 3 := by linarith
  have hM : (1 : ℝ) ≤ 12 * (42 * (q : ℝ) ^ 3) ^ 3 := by
    have h := one_le_pow₀ hbase (n := 3)
    linarith
  obtain ⟨k, hk, hkbound, htail⟩ := exists_geometric_truncation hM
  have hlog : Real.log (8 * (12 * (42 * (q : ℝ) ^ 3) ^ 3)) =
      Real.log 7112448 + 9 * Real.log q := by
    rw [show 8 * (12 * (42 * (q : ℝ) ^ 3) ^ 3) = 7112448 * (q : ℝ) ^ 9 by ring,
      Real.log_mul (by norm_num) (pow_ne_zero 9 hq0.ne'), Real.log_pow]
    norm_num
  rw [hlog] at hkbound
  have hD : 0 ≤ 4 * Real.log (7112448 : ℝ) + 2 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7112448)
    linarith
  refine ⟨k, hk, ?_⟩
  intro β hβ hβ'
  refine ⟨htail _ (by linarith) (by linarith), ?_⟩
  have hp := one_add_pow_le_exp_of_nat_le (by linarith : 0 ≤ 1 - β) k hkbound
  have he : (4 * (Real.log 7112448 + 9 * Real.log q) + 2) * (1 - β) ≤
      (4 * Real.log 7112448 + 2) + Real.log q * (36 * (1 - β)) := by
    have h := mul_le_mul_of_nonneg_left (show 1 - β ≤ 1 by linarith) hD
    nlinarith
  calc
    (2 - β) ^ k = (1 + (1 - β)) ^ k := by congr 1; ring
    _ ≤ _ := hp
    _ ≤ Real.exp ((4 * Real.log 7112448 + 2) + Real.log q * (36 * (1 - β))) :=
      Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, ← Real.rpow_def_of_pos hq0]; rfl

theorem biquadraticResidue_lower_of_nonpos {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ) (hβ : 7 / 8 < β) (hβ' : β < 1)
    (hF : (biquadraticLFunction χ ψ (β : ℂ)).re ≤ 0) :
    (1 - β) / (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β))) ≤
      (biquadraticResidue χ ψ).re := by
  obtain ⟨k, hk, htailpow⟩ := exists_biquadratic_truncation q hq
  obtain ⟨htail, hpow⟩ := htailpow β hβ hβ'
  have hlower := biquadraticLFunction_taylor_lower_bound χ ψ hχ hψ hχψ hχsq hψsq β hβ hβ' k hk
  have hgap : 0 < 1 - β := by linarith
  have hP : 0 < (2 - β) ^ k := pow_pos (by linarith) k
  have hhalf : (1 / 2 : ℝ) ≤ (biquadraticResidue χ ψ).re * (2 - β) ^ k / (1 - β) := by linarith
  have hprod := (le_div_iff₀ hgap).mp hhalf
  have hρ : 0 < (biquadraticResidue χ ψ).re := by
    by_contra h
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hP.le
    linarith
  have hprod' := mul_le_mul_of_nonneg_left hpow hρ.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc := siegelTruncationConstant_pos
  apply (div_le_iff₀ (by positivity : 0 < 2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β)))).mpr
  nlinarith

theorem biquadraticResidue_lower_of_real_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ) (hβ : 7 / 8 < β) (hβ' : β < 1)
    (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (1 - β) / (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β))) ≤
      (biquadraticResidue χ ψ).re := by
  apply biquadraticResidue_lower_of_nonpos hq χ ψ hχ hψ hχψ hχsq hψsq β hβ hβ'
  simp [biquadraticLFunction, hz]

end Chen

end

/-! ## ChenTheorem.Lemma6.RealZeroRepulsion -/

section

namespace Chen

/-- Quantitative repulsion between zeros belonging to two distinct real characters
of a common level. The radius and constant depend only on the chosen exponent. -/
theorem exists_real_zero_repulsion_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r A : ℝ, 0 < r ∧ 0 < A ∧ ∀ (q : ℕ) [NeZero q]
      (χ ψ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 → ψ ≠ 1 → χ * ψ ≠ 1 →
      χ ^ 2 = 1 → ψ ^ 2 = 1 → ∀ β₁ β₂ : ℝ,
      7 / 8 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 →
      1 - r ≤ β₂ → β₂ ≤ 1 → DirichletCharacter.LFunction ψ (β₂ : ℂ) = 0 →
      (1 - β₁) / (A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε)) ≤ 1 - β₂ := by
  obtain ⟨K, hK, hOne⟩ := exists_nonprincipal_LFunction_one_small_power hε
  obtain ⟨r, D, hr, hD, hZero⟩ := exists_nonprincipal_one_bound_of_real_zero hε
  let A : ℝ := 2 * siegelTruncationConstant * K ^ 2 * D
  have hC := siegelTruncationConstant_pos
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨r, A, hr, hA, ?_⟩
  intro q inst χ ψ hq hχ hψ hχψ hχsq hψsq β₁ β₂ hβ₁ hβ₁' hz₁ hβ₂ hβ₂' hz₂
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hgap₂ : 0 ≤ 1 - β₂ := sub_nonneg.mpr hβ₂'
  have h1 := hOne q χ hq hχ
  have h2 := hZero q ψ hq hψ β₂ hβ₂ hβ₂' hz₂
  have h3 := hOne q (χ * ψ) hq hχψ
  have hres : ‖biquadraticResidue χ ψ‖ ≤ K ^ 2 * D * (q : ℝ) ^ (3 * ε) * (1 - β₂) := by
    simp only [biquadraticResidue, biquadraticHolomorphicFactor, norm_mul]
    calc
      _ ≤ (K * (q : ℝ) ^ ε) * (D * (q : ℝ) ^ ε * (1 - β₂)) * (K * (q : ℝ) ^ ε) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = K ^ 2 * D * ((q : ℝ) ^ ε) ^ 3 * (1 - β₂) := by ring
      _ = _ := by simp only [← Real.rpow_mul_natCast hq0.le, Nat.cast_ofNat, mul_comm ε (3 : ℝ)]
  have hlower := biquadraticResidue_lower_of_real_zero hq χ ψ hχ hψ hχψ hχsq hψsq β₁ hβ₁ hβ₁' hz₁
  have hresre := (Complex.re_le_norm (biquadraticResidue χ ψ)).trans hres
  have hpos : 0 < 2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β₁)) := by positivity
  have hprod := (div_le_iff₀ hpos).mp (hlower.trans hresre)
  have hid : (K ^ 2 * D * (q : ℝ) ^ (3 * ε) * (1 - β₂)) *
      (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β₁))) =
      (1 - β₂) * (A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε)) := by
    rw [Real.rpow_add hq0]
    dsimp [A]
    ring
  rw [hid] at hprod
  exact (div_le_iff₀ (by positivity : 0 < A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε))).mpr hprod

end Chen

end

/-! ## ChenTheorem.Lemma6.RealCharacterSiegel -/

section

namespace Chen

/-- Siegel's ineffective real zero-free region. The choice of a fixed possible
exceptional character accounts for the non-effective constant. -/
theorem exists_real_character_siegel_region {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ ≠ 1 → χ ^ 2 = 1 → ∀ β : ℝ,
      1 - c * (q : ℝ) ^ (-ε) < β → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  classical
  let δ : ℝ := min (1 / 16) (ε / 144)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 16 := min_le_left _ _
  have hδ₂ : δ ≤ ε / 144 := min_le_right _ _
  by_cases H : ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q ∧ χ ≠ 1 ∧ χ ^ 2 = 1 ∧ ∃ β : ℝ,
        1 - δ < β ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0
  · obtain ⟨q₁, inst₁, χ₁, hq₁, hχ₁, hsq₁, β₁, hβ₁, hz₁⟩ := H
    letI : NeZero q₁ := inst₁
    have hq₁R : (1 : ℝ) ≤ q₁ := by exact_mod_cast (by omega : 1 ≤ q₁)
    have hq₁pos : (0 : ℝ) < q₁ := by linarith
    have hβ₁' : β₁ < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₁ (Or.inl hχ₁)
        (by simpa using le_of_not_gt hn) hz₁
    have hβ₁lower : 7 / 8 < β₁ := by linarith
    obtain ⟨r, A, hr, hA, hrep⟩ := exists_real_zero_repulsion_bound (by positivity : 0 < ε / 12)
    obtain ⟨η, hη, hnonzero⟩ := exists_nonprincipal_one_nonvanishing_ball χ₁ hχ₁
    let c₀ : ℝ := (1 - β₁) / (A * (q₁ : ℝ) ^ ε)
    have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
    let c : ℝ := min (min r η) (min (1 / 2) c₀)
    have hc : 0 < c := lt_min (lt_min hr hη) (lt_min (by norm_num) hc₀)
    have hcr : c ≤ r := (min_le_left _ _).trans (min_le_left _ _)
    have hcη : c ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have hchalf : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hcc₀ : c ≤ c₀ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨c, hc, ?_⟩
    intro q₂ inst₂ χ₂ hq₂ hχ₂ hsq₂ β₂ hβ₂ hz₂
    have hq₂R : (1 : ℝ) ≤ q₂ := by exact_mod_cast (by omega : 1 ≤ q₂)
    have hq₂pos : (0 : ℝ) < q₂ := by linarith
    have hpow : (q₂ : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq₂R (by linarith)
    have hgap : 1 - β₂ < c := by
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    have hβ₂' : β₂ < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₂ (Or.inl hχ₂)
        (by simpa using le_of_not_gt hn) hz₂
    have hβ₂pos : 0 < β₂ := by linarith
    let Q : ℕ := q₁ * q₂
    have hQ : 2 ≤ Q := by dsimp [Q]; nlinarith
    letI : NeZero Q := ⟨by omega⟩
    have hd₁ : q₁ ∣ Q := Nat.dvd_mul_right _ _
    have hd₂ : q₂ ∣ Q := Nat.dvd_mul_left _ _
    let χ := χ₁.changeLevel hd₁
    let ψ := χ₂.changeLevel hd₂
    have hχ : χ ≠ 1 := hχ₁ ∘ (DirichletCharacter.changeLevel_eq_one_iff hd₁).mp
    have hψ : ψ ≠ 1 := hχ₂ ∘ (DirichletCharacter.changeLevel_eq_one_iff hd₂).mp
    have hχsq : χ ^ 2 = 1 := real_character_changeLevel hd₁ χ₁ hsq₁
    have hψsq : ψ ^ 2 = 1 := real_character_changeLevel hd₂ χ₂ hsq₂
    have hzχ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 :=
      (LFunction_changeLevel_zero_iff hd₁ χ₁ hχ₁ _ (by simpa using (show 0 < β₁ by linarith))).mpr hz₁
    have hzψ : DirichletCharacter.LFunction ψ (β₂ : ℂ) = 0 :=
      (LFunction_changeLevel_zero_iff hd₂ χ₂ hχ₂ _ hβ₂pos).mpr hz₂
    by_cases hprod : χ * ψ = 1
    · have heq : ψ = χ := real_character_eq_of_mul_eq_one χ ψ hχsq hprod
      rw [heq] at hzψ
      have hz := (LFunction_changeLevel_zero_iff hd₁ χ₁ hχ₁ _ hβ₂pos).mp hzψ
      apply hnonzero (β₂ : ℂ) _ hz
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith : β₂ - 1 < 0)]
      linarith
    · have hbound := hrep Q χ ψ hQ hχ hψ hprod hχsq hψsq β₁ β₂
        hβ₁lower hβ₁' hzχ (by linarith) hβ₂'.le hzψ
      have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
      have hQpos : (0 : ℝ) < Q := by linarith
      have hexp : 36 * (1 - β₁) + 3 * (ε / 12) ≤ ε := by linarith
      have hQpow := Real.rpow_le_rpow_of_exponent_le hQR hexp
      have hlower : (1 - β₁) / (A * (Q : ℝ) ^ ε) ≤ 1 - β₂ := by
        apply le_trans _ hbound
        exact div_le_div_of_nonneg_left (by linarith) (by positivity)
          (mul_le_mul_of_nonneg_left hQpow hA.le)
      have hid : c₀ * (q₂ : ℝ) ^ (-ε) = (1 - β₁) / (A * (Q : ℝ) ^ ε) := by
        dsimp [c₀, Q]
        rw [Nat.cast_mul, Real.mul_rpow hq₁pos.le hq₂pos.le, Real.rpow_neg hq₂pos.le]
        ring
      rw [← hid] at hlower
      have := mul_le_mul_of_nonneg_right hcc₀ (Real.rpow_nonneg hq₂pos.le (-ε))
      linarith
  · refine ⟨δ, hδ, ?_⟩
    intro q inst χ hq hχ hsq β hβ hz
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hqR (by linarith : -ε ≤ 0)
    have hmul := mul_le_mul_of_nonneg_left hpow hδ.le
    exact H ⟨q, inst, χ, hq, hχ, hsq, β, by linarith, hz⟩

end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaLocalZeroLogDerivative -/

section

open Set Metric

namespace Chen

theorem high_centered_zeta_ne_pole (t : ℝ) (ht : 1 ≤ |t|) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    dirichletZeroDiskCenter t + w ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  simp [dirichletZeroDiskCenter] at him
  have hwim := (Complex.abs_im_le_norm w).trans hw
  have ht' : |t| = |w.im| := by rw [show t = -w.im by linarith, abs_neg]
  rw [← ht'] at hwim
  linarith
theorem analyticOnNhd_high_centered_zeta (t : ℝ) (ht : 1 ≤ |t|) :
    AnalyticOnNhd ℂ (fun w => riemannZeta (dirichletZeroDiskCenter t + w))
      (closedBall 0 (1 / 2)) := by
  intro w hw
  have hne := high_centered_zeta_ne_pole t ht (by simpa only [mem_closedBall_zero_iff] using hw)
  exact (analyticOn_riemannZeta _ hne).comp (by fun_prop)
theorem norm_riemannZeta_zero_disk_center_ge (t : ℝ) :
    (1 / 5 : ℝ) ≤ ‖riemannZeta (dirichletZeroDiskCenter t)‖ := by
  simpa only [DirichletCharacter.LFunction_modOne_eq]
    using norm_LFunction_zero_disk_center_ge (1 : DirichletCharacter ℂ 1) t
theorem norm_riemannZeta_logDeriv_sub_local_zero_poles_le (t : ℝ) (ht : 1 ≤ |t|)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32) (hne : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s - diskZeroPoleSum
      (fun w => riemannZeta (dirichletZeroDiskCenter t + w)) (3 / 8)
      (s - dirichletZeroDiskCenter t)‖ ≤
      640 * (Real.log (20 * (‖dirichletZeroDiskCenter t‖ + 1)) + 1) := by
  let c := dirichletZeroDiskCenter t
  let F := fun w => riemannZeta (c + w)
  let M := 4 * (‖c‖ + 1)
  have hM : 1 ≤ M := by dsimp [M]; have := norm_nonneg c; linarith
  have hf : AnalyticOnNhd ℂ F (closedBall 0 (4 * (3 / 8) / 3)) := by
    convert analyticOnNhd_high_centered_zeta t ht using 1
    norm_num
  have hanchor : (1 / 5 : ℝ) ≤ ‖F 0‖ := by
    simpa only [F, add_zero] using norm_riemannZeta_zero_disk_center_ge t
  have hnorm0 : 0 < ‖F 0‖ := by linarith
  have hb : ∀ w ∈ sphere (0 : ℂ) (4 * (3 / 8) / 3), ‖F w‖ ≤ M := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 / 2 := by norm_num [mem_sphere] at hw; exact hw.le
    exact norm_riemannZeta_high_centered_disk_le t ht hw'
  have he : c + (s - c) = s := by ring
  have hmain := norm_logDeriv_sub_zero_poles_le_of_outer_bound (by norm_num : (0 : ℝ) < 3 / 8)
    hM hf (norm_pos_iff.mp hnorm0) hb
    (show ‖s - c‖ ≤ 3 * (3 / 8) / 4 by norm_num; exact hs)
    (show F (s - c) ≠ 0 by simpa only [F, he] using hne)
  have hd : deriv F (s - c) = deriv riemannZeta s := by dsimp [F]; rw [deriv_comp_const_add, he]
  rw [hd, show F (s - c) = riemannZeta s by dsimp [F]; rw [he]] at hmain
  have hratio : M / ‖F 0‖ ≤ 5 * M := (div_le_iff₀ hnorm0).mpr (by nlinarith)
  have hlogs := Real.log_le_log (div_pos (by linarith : 0 < M) hnorm0) hratio
  change ‖deriv riemannZeta s / riemannZeta s - diskZeroPoleSum F (3 / 8) (s - c)‖ ≤ _
  have heM : 5 * M = 20 * (‖c‖ + 1) := by dsimp [M]; ring
  rw [heM] at hlogs
  apply hmain.trans
  change 240 * (Real.log (M / ‖F 0‖) + 1) / (3 / 8) ≤ 640 * (Real.log (20 * (‖c‖ + 1)) + 1)
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaHighLogDerivativeBound -/

section

namespace Chen

theorem height_log_ge_half (t : ℝ) : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) := by
  have hA : 0 < |t| + 2 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hA
  have hi : (|t| + 2)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ |t| + 2 by linarith [abs_nonneg t])
  linarith
theorem zeta_zero_disk_log_bound_le (t : ℝ) :
    Real.log (20 * (‖dirichletZeroDiskCenter t‖ + 1)) + 1 ≤ 93 * Real.log (|t| + 2) := by
  have hc : ‖dirichletZeroDiskCenter t‖ ≤ |t| + 5 / 4 := by
    have h := norm_add_le (5 / 4 : ℂ) ((t : ℂ) * Complex.I)
    norm_num [dirichletZeroDiskCenter, norm_mul] at h ⊢
    linarith
  have hA : 0 < |t| + 2 := by positivity
  have harg : 20 * (‖dirichletZeroDiskCenter t‖ + 1) ≤ 45 * (|t| + 2) := by
    nlinarith [abs_nonneg t]
  have hl := Real.log_le_log (by positivity : 0 < 20 * (‖dirichletZeroDiskCenter t‖ + 1)) harg
  rw [Real.log_mul (by norm_num : (45 : ℝ) ≠ 0) hA.ne'] at hl
  have h45 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 45)
  have hL := height_log_ge_half t
  linarith
theorem norm_riemannZeta_logDeriv_sub_local_zero_poles_le_log (t : ℝ) (ht : 1 ≤ |t|)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32) (hne : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s - diskZeroPoleSum
      (fun w => riemannZeta (dirichletZeroDiskCenter t + w)) (3 / 8)
      (s - dirichletZeroDiskCenter t)‖ ≤ 60000 * Real.log (|t| + 2) := by
  apply (norm_riemannZeta_logDeriv_sub_local_zero_poles_le t ht s hs hne).trans
  have h := zeta_zero_disk_log_bound_le t
  have hp := height_log_ge_half t
  linarith
theorem riemannZeta_logDeriv_re_ge_high (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (ht : 1 ≤ |t|) :
    -(60000 * Real.log (|t| + 2)) ≤
      (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hne : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hb := norm_riemannZeta_logDeriv_sub_local_zero_poles_le_log t ht _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hf : AnalyticOnNhd ℂ (fun w => riemannZeta (dirichletZeroDiskCenter t + w))
      (Metric.closedBall 0 (3 / 8)) :=
    (analyticOnNhd_high_centered_zeta t ht).mono (Metric.closedBall_subset_closedBall (by norm_num))
  have hp := diskZeroPoleSum_re_nonneg (κ := -(1 / 4 : ℝ)) hf
    (fun w _ hw => by
      have h := centered_LFunction_ne_zero_of_re_gt_neg_quarter
        (1 : DirichletCharacter ℂ 1) t w hw
      simpa only [DirichletCharacter.LFunction_modOne_eq] using h)
    (z := (σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  linarith
end Chen

end

/-! ## ChenTheorem.Lemma6.ZetaAwayPoleLogDerivative -/

section

open Set Metric

namespace Chen
theorem exists_zeta_logDeriv_compact_bound (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 / 2 → ρ ≤ |t| → |t| ≤ 1 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  let K : Set ℂ := closedBall 0 3 ∩ ({s | 1 ≤ s.re} ∩ {s | ρ ≤ |s.im|})
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 3).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le continuous_const Complex.continuous_im.abs))
  have hcont : ContinuousOn (logDeriv riemannZeta) K := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro he
      have h := hs.2.2
      rw [he] at h
      norm_num at h
      linarith
    have ha := analyticOn_riemannZeta s hsne
    change ContinuousWithinAt (fun z => deriv riemannZeta z / riemannZeta z) K s
    exact (ha.deriv.continuousAt.div ha.continuousAt
      (riemannZeta_ne_zero_of_one_le_re hs.2.1)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.norm
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro σ t hσ hσ' ht ht'
  have hsK : (σ : ℂ) + (t : ℂ) * Complex.I ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      have h := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
        abs_of_pos (by linarith : 0 < σ)] at h
      linarith
    · simpa using hσ
    · simpa using ht
  exact (hB (mem_image_of_mem _ hsK)).trans (le_max_left _ _)
theorem exists_zeta_logDeriv_re_ge_away_pole (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 3 / 2 → ρ ≤ |t| →
      -(C * Real.log (|t| + 2)) ≤
        (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨B, hB, hb⟩ := exists_zeta_logDeriv_compact_bound ρ hρ
  refine ⟨60000 + 2 * B, by positivity, ?_⟩
  intro σ t hσ hσ' ht
  have hL := height_log_ge_half t
  by_cases ht' : 1 ≤ |t|
  · have h := riemannZeta_logDeriv_re_ge_high σ t hσ hσ' ht'
    nlinarith
  · have hnorm := hb σ t hσ.le hσ' ht (le_of_not_ge ht')
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    nlinarith
theorem exists_principal_logDeriv_re_ge_away_pole (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ σ t : ℝ,
      1 < σ → σ ≤ 3 / 2 → ρ ≤ |t| →
      -(C * Real.log ((q : ℝ) * (|t| + 2))) ≤
        (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨C, hC, hz⟩ := exists_zeta_logDeriv_re_ge_away_pole ρ hρ
  refine ⟨C + 1, by positivity, ?_⟩
  intro q inst hq σ t hσ hσ' ht
  have h1 := hz σ t hσ hσ' ht
  have h2 := norm_principal_logDeriv_sub_zeta_le (q := q)
    ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
  rw [Complex.sub_re] at hr
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 0 < |t| + 2 := by positivity
  have hlogt : Real.log (|t| + 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log hA
    nlinarith
  have hlogq : Real.log q ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < q)
    nlinarith [abs_nonneg t]
  nlinarith
end Chen

end

/-! ## ChenTheorem.Lemma6.RealHighHeightRegion -/

section

namespace Chen
theorem primitive_real_zero_inequality_away_pole {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t Cz Cp : ℝ) (hCp : 0 < Cp) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : -(Cp * Real.log ((q : ℝ) * (|2 * t| + 2))) ≤
      (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) :
    4 / (σ - β) ≤ 3 / (σ - 1) + 3 * Cz +
      (240000 + 2 * Cp) * Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  rw [hsq] at h3
  simp only [logDeriv_apply] at h2
  have hd := mul_le_mul_of_nonneg_left (conductor_height_log_double_le hq t) hCp.le
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h1 h2 hd ⊢
  simp only [div_eq_mul_inv] at h1 h2 h3 hzeta ⊢
  nlinarith
theorem exists_primitive_real_zero_free_away_axis (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ, ρ ≤ |s.im| →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨Cp, hCp, hprincipal⟩ := exists_principal_logDeriv_re_ge_away_pole ρ hρ
  obtain ⟨δ, Cz, hδ, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  let B : ℝ := 4 * Cz + 240000 + 2 * Cp
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq s ht hs hzero
  let L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : 3 / 4 ≤ L := conductor_height_log_ge_threeQuarters q hq s.im
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y : ℝ := σ - s.re
  let D : ℝ := 3 * Cz + (240000 + 2 * Cp) * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < s.re at hs
  rw [hquot] at hs
  have hβ : s.re ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; rw [he] at hh; norm_num at hh)) hh.le) hzero
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have ht2 : ρ ≤ |2 * s.im| := by rw [abs_mul]; norm_num; linarith
  have hp := hprincipal q hq σ (2 * s.im) hσ hσ' ht2
  have hz : DirichletCharacter.LFunction χ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
    rw [Complex.re_add_im]; exact hzero
  have hi := primitive_real_zero_inequality_away_pole hq hχ hsq σ s.re s.im Cz Cp
    hCp hσ hσ' (by linarith) hz (hzeta σ hσ hσδ) hp
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hσx : σ - 1 = x := by dsimp [σ]; ring
  rw [hσx] at hi
  have hi' : 4 / y ≤ 3 / x + D := by dsimp [y, D]; linarith
  exact four_div_gap_contradiction hx (by dsimp [y]; linarith)
    (by dsimp [y, σ]; linarith) hDx hi'
end Chen

end

/-! ## ChenTheorem.Lemma6.RealNonexceptionalRegion -/

section

namespace Chen

theorem zero_height_log_le_conductor_height_log {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  apply Real.log_le_log (by positivity)
  nlinarith [abs_nonneg t]

theorem exists_primitive_real_nonreal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ, s.im ≠ 0 →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨r, cL, hr, hcL, hlow⟩ := exists_primitive_real_low_height_zero_im_eq_zero
  obtain ⟨cH, hcH, hhigh⟩ := exists_primitive_real_zero_free_away_axis r hr
  refine ⟨min cL cH, lt_min hcL hcH, ?_⟩
  intro q inst χ hq hχ hsq s him hs hz
  have hL := primitiveZeroFreeHeightLog_pos hq s.im
  by_cases ht : |s.im| ≤ r
  · have hL0 : 0 < Real.log ((q : ℝ) * 2) := by
      have h := conductor_height_log_ge_threeQuarters q hq 0
      simp only [abs_zero, zero_add] at h
      linarith
    have hw : min cL cH / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ cL / Real.log ((q : ℝ) * 2) := by
      calc
        _ ≤ cL / Real.log ((q : ℝ) * (|s.im| + 2)) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hL.le
        _ ≤ _ := div_le_div_of_nonneg_left hcL.le hL0 (zero_height_log_le_conductor_height_log hq s.im)
    exact him (hlow q χ hq hχ hsq s (by linarith) ht hz)
  · have hw := div_le_div_of_nonneg_right (min_le_right cL cH) hL.le
    exact hhigh q χ hq hχ hsq s (le_of_not_ge ht) (by linarith) hz

/-- The full logarithmic region for a primitive real character contains at most
one zero. Any such exceptional zero is real and simple. -/
theorem exists_primitive_real_exceptional_zero_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re ∧
        DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s = 0 →
        s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_nonreal_zero_free_region
  obtain ⟨cU, hcU, hU⟩ := exists_primitive_real_zero_unique
  obtain ⟨cS, hcS, hS⟩ := exists_primitive_real_zero_deriv_ne_zero
  let c := min cR (min cU cS)
  have hc : 0 < c := lt_min hcR (lt_min hcU hcS)
  have hcR' : c ≤ cR := min_le_left _ _
  have hcU' : c ≤ cU := (min_le_right _ _).trans (min_le_left _ _)
  have hcS' : c ≤ cS := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq
  have hreal : ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
      DirichletCharacter.LFunction χ s = 0 → s.im = 0 := by
    intro s hs hz
    by_contra him
    have hw := div_le_div_of_nonneg_right hcR' (primitiveZeroFreeHeightLog_pos hq s.im).le
    exact hR q χ hq hχ hsq s him (by linarith) hz
  have hL0 : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hUdiv := div_le_div_of_nonneg_right hcU' hL0.le
  have hSdiv := div_le_div_of_nonneg_right hcS' hL0.le
  constructor
  · intro s hs t ht
    have hsi := hreal s hs.1 hs.2
    have hti := hreal t ht.1 ht.2
    have heS : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
    have heT : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
    have hs' := hs.1
    have ht' := ht.1
    simp only [hsi, hti, abs_zero, zero_add] at hs' ht'
    have he := hU q χ hq hχ hsq s.re t.re (by linarith) (by linarith)
      (by rw [heS]; exact hs.2) (by rw [heT]; exact ht.2)
    apply Complex.ext
    · exact he
    · rw [hsi, hti]
  · intro s hs hz
    have him := hreal s hs hz
    refine ⟨him, ?_⟩
    have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [him]
    simp only [him, abs_zero, zero_add] at hs
    have h := hS q χ hq hχ hsq s.re (by linarith) (by rw [he]; exact hz)
    simpa only [he] using h

end Chen

end

/-! ## ChenTheorem.Lemma6.PrimitiveExceptionalRegion -/

section

namespace Chen

/-- A uniform logarithmic region for every primitive character contains at most
one zero. Any zero there belongs to a real character and is real and simple. -/
theorem exists_primitive_exceptional_zero_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re ∧
        DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s = 0 →
        χ ^ 2 = 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cN, hcN, hN⟩ := exists_primitive_nonreal_zero_free_region
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_exceptional_zero_region
  refine ⟨min cN cR, lt_min hcN hcR, ?_⟩
  intro q inst χ hq hχ
  by_cases hsq : χ ^ 2 = 1
  · have hreal := hR q χ hq hχ hsq
    have hwidth : ∀ t : ℝ,
        min cN cR / Real.log ((q : ℝ) * (|t| + 2)) ≤
          cR / Real.log ((q : ℝ) * (|t| + 2)) := by
      intro t
      exact div_le_div_of_nonneg_right (min_le_right _ _) (primitiveZeroFreeHeightLog_pos hq t).le
    constructor
    · intro s hs t ht
      exact hreal.1 ⟨by linarith [hwidth s.im, hs.1], hs.2⟩
        ⟨by linarith [hwidth t.im, ht.1], ht.2⟩
    · intro s hs hz
      have h := hreal.2 s (by linarith [hwidth s.im]) hz
      exact ⟨hsq, h⟩
  · have hne : ∀ s : ℂ, 1 - min cN cR / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
      intro s hs
      have hw := div_le_div_of_nonneg_right (min_le_left cN cR)
        (primitiveZeroFreeHeightLog_pos hq s.im).le
      exact hN q χ hq hχ hsq s (by linarith)
    constructor
    · intro s hs t ht
      exact False.elim (hne s hs.1 hs.2)
    · intro s hs hz
      exact False.elim (hne s hs hz)

end Chen

end

/-! ## ChenTheorem.Lemma6.RealSiegelReduction -/

section

namespace Chen

/-- The full mixed zero-free-region package now requires only the ineffective
Siegel bound for real primitive characters on the real axis. The logarithmic
nonexceptional region and its derivative bounds are already proved. -/
theorem primitiveZeroFreeRegion_of_real_siegel
    (h : ∀ N : ℕ, 1 ≤ N → ∃ cS : ℝ, 0 < cS ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ,
          1 - cS * (q : ℝ) ^ ((-1 : ℝ) / N) < β →
            DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) : PrimitiveZeroFreeRegion := by
  obtain ⟨cH, hcH, hregion⟩ := exists_primitive_exceptional_zero_region
  apply primitiveZeroFreeRegion_of_nonvanishing
  intro N hN
  obtain ⟨cS, hcS, hsiegel⟩ := h N hN
  refine ⟨cH, cS, hcH, hcS, ?_⟩
  intro q inst χ hq hχ s hs hz
  have hheight : primitiveZeroFreeWidthAt N cH cS q s.im ≤
      cH / Real.log ((q : ℝ) * (|s.im| + 2)) := min_le_left _ _
  have h := (hregion q χ hq hχ).2 s (by linarith) hz
  have hwidth : primitiveZeroFreeWidthAt N cH cS q s.im ≤
      cS * (q : ℝ) ^ ((-1 : ℝ) / N) := min_le_right _ _
  have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [h.2.1]
  have hne := hsiegel q inst χ hq hχ h.1 s.re (by linarith)
  rw [he] at hne
  exact hne hz

end Chen

end

/-! ## ChenTheorem.Lemma6.ZeroFreeRegion -/

section

/-
The zero-free-region interface for equation (21) in Lemma 6.

Chen moves the logarithmic-derivative contour from his `alpha`-line to
`Re s = 1 - 1 / sqrt(log x)`.  The classical input behind this step is not
a fixed-width strip uniform in the imaginary part.  Its width has two
independent restrictions:

* the de la Vallee-Poussin region shrinks like
  `1 / log(q (|Im s| + 2))` with the height;
* a possible exceptional real zero is excluded only by an ineffective
  Siegel bound.  For every fixed positive denominator `N`, this contributes
  a width of the shape `q^(-1/N)`; Chen's equation (21) uses `N = 300`.

The uniform region valid for every primitive character is therefore the
minimum of these two widths.  The logarithmic derivative is requested only
in the region with half that width, leaving quantitative distance from all
zeros.  Its deliberately generous bound includes the possible
`q^(1/300)` cost of a nearby exceptional zero.

The classical package is proved locally from mathlib: the logarithmic
nonexceptional region, the ineffective real Siegel bound, and the companion
logarithmic-derivative estimate. The contour argument consuming it uses a
finite height; no height-uniform fixed-width nonvanishing is asserted.
-/

namespace Chen

/-- The mixed Dirichlet zero-free region and its half-width logarithmic
derivative bound, including Siegel's ineffective exceptional-zero estimate. -/
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  apply primitiveZeroFreeRegion_of_real_siegel
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨c, hc, hsiegel⟩ := exists_real_character_siegel_region (by positivity : 0 < 1 / (N : ℝ))
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq β hβ
  apply hsiegel q χ hq (by
    intro he
    rw [he, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hχ
    omega) hsq β
  simpa only [neg_div] using hβ

end Chen

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.Basic -/

section

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Bombieri--Vinogradov: definitions

This file fixes the exact level-of-distribution statement used by the
Richert sieve.  Later files reduce it to a mean-value estimate for primitive
Dirichlet characters and prove that estimate from Vaughan's identity and the
character large sieve already available in `ChenTheorem.LargeSieve`.
-/

/-- Chebyshev's `ψ` function restricted to the residue class `a mod q`. -/
noncomputable def progressionPsi (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n ≡ a [MOD q] then ArithmeticFunction.vonMangoldt n else 0

/-- The error in the expected main term `x / φ(q)` for one reduced residue
class. -/
noncomputable def progressionError (x q a : ℕ) : ℝ :=
  |progressionPsi x q a - (x : ℝ) / (Nat.totient q : ℝ)|

/-- The error attached to `a` when `a` is a reduced residue, and zero for the
other representatives in `0, ..., q-1`. -/
noncomputable def reducedProgressionError (x q a : ℕ) : ℝ :=
  if a.Coprime q then progressionError x q a else 0

/-- Maximum progression error over reduced residue classes modulo `q`.
The `q = 0` branch makes the definition total; Bombieri--Vinogradov only sums
over positive moduli. -/
noncomputable def maxProgressionError (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0
  else
    (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
      (reducedProgressionError x q)

/-- The von-Mangoldt sum twisted by a Dirichlet character. -/
noncomputable def twistedPsi {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n

/-- Classical Bombieri--Vinogradov at level `1/2`, in an eventual form.

For every logarithmic saving `A`, one may choose a logarithmic loss `B` in
the level `Q ≤ √x / (log x)^B`, uniformly for every such `Q`. -/
def Statement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ Q : ℕ,
          (Q : ℝ) ≤
              Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B →
            ∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q ≤
              C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

theorem progressionPsi_nonneg (x q a : ℕ) :
    0 ≤ progressionPsi x q a := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem progressionError_nonneg (x q a : ℕ) :
    0 ≤ progressionError x q a :=
  abs_nonneg _

theorem reducedProgressionError_nonneg (x q a : ℕ) :
    0 ≤ reducedProgressionError x q a := by
  rw [reducedProgressionError]
  split_ifs
  · exact progressionError_nonneg x q a
  · exact le_rfl

theorem maxProgressionError_nonneg (x q : ℕ) :
    0 ≤ maxProgressionError x q := by
  by_cases hq : q = 0
  · simp [maxProgressionError, hq]
  · rw [maxProgressionError, dif_neg hq]
    calc
      0 ≤ reducedProgressionError x q 0 :=
        reducedProgressionError_nonneg x q 0
      _ ≤ (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
          (reducedProgressionError x q) :=
        Finset.le_sup' _ (Finset.mem_range.2 (Nat.pos_of_ne_zero hq))

theorem progressionError_le_maxProgressionError
    {x q a : ℕ} (hq : q ≠ 0) (ha : a < q) (hac : a.Coprime q) :
    progressionError x q a ≤ maxProgressionError x q := by
  rw [maxProgressionError, dif_neg hq]
  calc
    progressionError x q a = reducedProgressionError x q a := by
      simp only [reducedProgressionError, if_pos hac]
    _ ≤ (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
        (reducedProgressionError x q) :=
      Finset.le_sup' _ (Finset.mem_range.2 ha)

theorem sum_maxProgressionError_nonneg (x Q : ℕ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q := by
  exact Finset.sum_nonneg fun q _ => maxProgressionError_nonneg x q

end Chen.BombieriVinogradov

end

/-! ## SourceTwistedPsiPrimePowers -/

section

open Real Filter
open scoped Classical

namespace Green64Analytic.SourceSW

noncomputable def twistedTheta {q : ℕ} (x : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n.Prime then (Real.log n : ℂ) * χ n else 0

/-- Prime-power removal for an actual complex twisted von Mangoldt prefix. -/
theorem norm_twistedPsi_sub_twistedTheta_le {q x : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖Chen.BombieriVinogradov.twistedPsi x χ - twistedTheta x χ‖ ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hglobal : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 1 x,
        if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
      Finset.sum_filter]
    congr 1
  rw [hglobal]
  unfold Chen.BombieriVinogradov.twistedPsi twistedTheta
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Icc 1 x,
        ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          if n.Prime then (Real.log n : ℂ) * χ n else 0)‖ ≤
      ∑ n ∈ Finset.Icc 1 x,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          if n.Prime then (Real.log n : ℂ) * χ n else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 x,
        if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp only [hp, if_false, not_false_eq_true, if_true, sub_zero,
          norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_right
          ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one (n : ZMod q))

/-- The standard Chebyshev bound makes the character power error uniform. -/
theorem norm_twistedPsi_sub_twistedTheta_le_sqrt_log {q x : ℕ}
    (hx : 1 ≤ x) (χ : DirichletCharacter ℂ q) :
    ‖Chen.BombieriVinogradov.twistedPsi x χ - twistedTheta x χ‖ ≤
      2 * Real.sqrt x * Real.log x :=
  (norm_twistedPsi_sub_twistedTheta_le χ).trans
    (Chebyshev.psi_sub_theta_le (by exact_mod_cast hx))
end Green64Analytic.SourceSW

end

