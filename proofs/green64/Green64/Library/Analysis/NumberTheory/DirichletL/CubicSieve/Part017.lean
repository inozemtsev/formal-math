module

public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicDyadicDecay.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.DualCoefficients -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicDualCoefficient {n : Type*} (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (j : n) : ℂ :=
  star (a j * gaussTwo (cols j) (hc j).2) / (‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ)

lemma cubicDualCoefficient_norm_sq {n : Type*}
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (j : n) :
    ‖cubicDualCoefficient cols hc a j‖ ^ 2 = ‖a j‖ ^ 2 / (Ideal.absNorm (cols j) : ℝ) := by
  simp only [cubicDualCoefficient, norm_div, norm_star, norm_mul, gaussTwo_norm_one _ (hc j),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_pow,
    primaryGenerator_norm_sq _ (hc j).2]

lemma cubicDualCoefficient_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (N : ℝ) (hN : 0 < N) (hcols : ∀ j, N / 2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    (∑ j, ‖cubicDualCoefficient cols hc a j‖ ^ 2) ≤ (2 / N) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cubicDualCoefficient_norm_sq]
  calc
    _ ≤ ‖a j‖ ^ 2 / (N / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hcols j)
    _ = _ := by field_simp

def cubicDualRow {n : Type*} [Fintype n] (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
      ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
      (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0

lemma cubicDualRow_eq_gram {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) :
    cubicDualRow cols hc a W M h =
      ∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) h * cubicDualCoefficient cols hc a j) *
          (cubicRow (cols k) h * cubicDualCoefficient cols hc a k) else 0) *
        paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
          ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) := by
  unfold cubicDualRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [isCoprime_comm (x := cols k) (y := cols j)]
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop]
    have hscale : (Ideal.absNorm (cols k) : ℝ) * (Ideal.absNorm (cols j) : ℝ) =
        (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) := mul_comm _ _
    rw [hscale]
    congr 1
    simp only [cubicDualCoefficient, star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [ite_eq_right hcop, zero_mul]

lemma cubicRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    cubicRow I 0 = 0 := by
  have hI_top : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hcop : ¬ IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, sup_bot_eq] using hI_top
  have h := idealSymbol_cube_mask I 0 hI.2
  rw [ite_eq_right hcop] at h
  exact eq_zero_of_pow_eq_zero h

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.DualShell -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicDualRow_zero {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hunit : ∀ j, cols j ≠ 1) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicDualRow cols hc a W M 0 = 0 := by
  unfold cubicDualRow
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  rw [cubicRow_zero_of_ne_one _ (hc j) (hunit j)]
  simp

theorem cubic_dual_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖cubicDualRow cols (fun j => (hcols j).1) a W M (rows i)‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) *
              ((2 / N) * ∑ j, ‖a j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := cubic_frequency_shell_bound W A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a
  have he := cubicDualCoefficient_energy cols (fun j => (hcols j).1) a N hN
    (fun j => (hcols j).2.1)
  have h := hb ε hε M K N hM hK hN rows cols hr hc hrows hcols
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    ((2 / N) * ∑ j, ‖a j‖ ^ 2) (by positivity) he he
  simpa only [cubicDualRow_eq_gram] using h

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FrequencyDyads -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyDyad (j : ℕ) : Finset O :=
  (elementRange ((2 : ℝ)^j)).filter (fun h => Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j)

lemma mem_frequencyDyad (h : O) (j : ℕ) :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_elementRange]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hh, hj⟩
    refine ⟨⟨hh, ?_⟩, hj⟩
    have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
    rw [hj] at hu
    exact_mod_cast hu

lemma frequencyDyad_bounds (j : ℕ) (h : O) (hh : h ∈ frequencyDyad j) :
    h ≠ 0 ∧ (2 : ℝ)^j / 2 ≤ (Ideal.absNorm (Ideal.span {h}) : ℝ) ∧
      (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ (2 : ℝ)^j := by
  obtain ⟨hn, hj⟩ := (mem_frequencyDyad h j).mp hh
  have hnorm : Ideal.absNorm (Ideal.span {h}) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
  have hl := two_pow_clog_le_double _ (Nat.one_le_iff_ne_zero.mpr hnorm)
  rw [hj] at hu hl
  refine ⟨hn, ?_, by exact_mod_cast hu⟩
  have hr : (2 : ℝ)^j ≤ 2 * (Ideal.absNorm (Ideal.span {h}) : ℝ) := by exact_mod_cast hl
  linarith

def frequencyDyadicEquiv : {h : O // h ≠ 0} ≃ Σ j : ℕ, frequencyDyad j where
  toFun h := ⟨Nat.clog 2 (Ideal.absNorm (Ideal.span {h.val})),
    ⟨h.val, (mem_frequencyDyad _ _).mpr ⟨h.property, rfl⟩⟩⟩
  invFun h := ⟨h.2.val, ((mem_frequencyDyad _ _).mp h.2.property).1⟩
  left_inv h := by cases h; rfl
  right_inv h := by
    rcases h with ⟨j, h, hh⟩
    have hj := ((mem_frequencyDyad h j).mp hh).2
    dsimp only
    subst j
    rfl

theorem tsum_frequencyDyads (f : O → ℂ) (hf : Summable f) (hzero : f 0 = 0) :
    (∑' h : O, f h) = ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
    symm
    exact tsum_subtype_eq_of_support_subset (fun h hh => by
      change h ≠ 0
      intro hz
      exact hh (hz ▸ hzero))
  rw [he]
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

theorem tsum_frequencyDyads_with_zero (f : O → ℂ) (hf : Summable f) :
    (∑' h : O, f h) = f 0 + ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = f 0 + ∑' h : {h : O // h ≠ 0}, f h.val := by
    have hs := (hf.sum_add_tsum_compl (s := {0})).symm
    have hset : ((↑({0} : Finset O) : Set O)ᶜ) = {h : O | h ≠ 0} := by
      ext h
      simp
    rw [hset] at hs
    simpa only [Finset.sum_singleton, Set.coe_ofPred] using hs
  rw [he]
  congr 1
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Majorant -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def frequencyMajorant (M N : ℝ) (j : ℕ) : ℝ :=
  elementSieveNorm ((2 : ℝ)^j) N / (1 + M * (2 : ℝ)^j / N^2)^3

lemma frequencyMajorant_nonneg (M N : ℝ) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ frequencyMajorant M N j := by
  unfold frequencyMajorant
  exact div_nonneg (elementSieveNorm_nonneg _ _) (by positivity)

lemma frequencyMajorant_geometric (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (j : ℕ) :
    frequencyMajorant M N j ≤
      (QuadraticInitialBound.initialSieveConstant * (1 + (⌈N⌉₊ : ℝ)^2) /
        (M / N^2)^3) * ((1 / 4 : ℝ)^j) := by
  let K : ℝ := (2 : ℝ)^j
  let c : ℝ := M / N^2
  let Q : ℝ := (⌈N⌉₊ : ℝ)^2
  let C : ℝ := QuadraticInitialBound.initialSieveConstant
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hK0 : 0 < K := by positivity
  have hN0 : 0 < N := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := sq_nonneg _
  have hC : 0 ≤ C := QuadraticInitialBound.initialSieveConstant_pos.le
  have hi : elementSieveNorm K N ≤ C * (1 + Q) * K := by
    apply (elementSieveNorm_initial K N hK hN).trans
    dsimp only [C, Q]
    nlinarith [mul_nonneg hC (mul_nonneg hQ (sub_nonneg.mpr hK))]
  have hden : (c*K)^3 ≤ (1+c*K)^3 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hgeom : (K^2)⁻¹ = (1/4 : ℝ)^j := by
    dsimp only [K]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← inv_pow]
    norm_num
  change elementSieveNorm K N / (1 + M*K/N^2)^3 ≤ _
  rw [show M*K/N^2 = c*K by dsimp [c]; ring]
  calc
    _ ≤ (C*(1+Q)*K) / (1+c*K)^3 := div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ (C*(1+Q)*K) / (c*K)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (C*(1+Q)/c^3) * (K^2)⁻¹ := by field_simp
    _ = _ := by rw [hgeom]

theorem frequencyMajorant_summable (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) :
    Summable (frequencyMajorant M N) := by
  have hg : Summable (fun j : ℕ => (1/4 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (hg.mul_left _).of_nonneg_of_le
    (frequencyMajorant_nonneg M N hM.le) (frequencyMajorant_geometric M N hM hN)

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Smoothed -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖eisEmbedding z‖ ^ 2 / M) else 0

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryGenerator_norm_sq I hI.2, primaryGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    convert hs using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  · simp only [ite_eq_right hcop]
    exact summable_zero

lemma cubicDualRow_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    convert cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CompactDescent -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma majorant_radial_summable (P : O → ℂ) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖^2 / M) * P z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall M) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside M hM z hz, zero_mul]

lemma majorant_rescale (d z : O) (_hd : d ≠ 0) (M : ℝ) :
    rowMajorant (‖eisEmbedding (d*z)‖^2 / M) =
      rowMajorant (‖eisEmbedding z‖^2 / (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) := by
  rw [map_mul, norm_mul, mul_pow, eisEmbedding_norm_sq_eq_absNorm_span d]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma dividedMajorant_tsum (P : O → ℂ) (d : O) (hd : d ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ dividedRows (rowMajorantBall M) d,
      rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      ∑' z : O, rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z := by
  symm
  rw [← show (fun z : O => rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      (fun z : O => rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z) by
          funext z; rw [majorant_rescale d z hd M]]
  apply tsum_eq_sum
  intro z hz
  have hout : d*z ∉ rowMajorantBall M := by
    intro hin
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨d*z, Finset.mem_filter.mpr ⟨hin, dvd_mul_right d z⟩, ?_⟩
    apply mul_left_cancel₀ hd
    exact elementQuotient_mul d (d*z) (dvd_mul_right d z)
  rw [rowMajorant_zero_outside M hM (d*z) hout, zero_mul]

lemma majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) =
      cubicSmoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hs j k))]
  unfold cubicSmoothedCoprime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => hs j k)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero, tsum_zero]

lemma compact_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ) *
        cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ)) := by
  rw [cubic_gcd_mobius_descent D hD cols hc a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors (primaryGenerator_ne_zero_ideal D hD)).mp hE
    rw [he, zero_dvd_iff] at hh
    exact primaryGenerator_ne_zero_ideal D hD hh
  have hgen := idealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM, span_idealGenerator]
  apply majorant_coprime_tsum
  have hNE : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  exact div_pos hM hNE

lemma gcdPool_cubic_admissible {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact cubic_admissible_of_dvd (hc j) (gcd_dvd_left _ _)

lemma gcdPool_subset_columnDivisorPool {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) :
    gcdPool cols ⊆ columnDivisorPool cols := by
  intro D hD
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact mem_columnDivisorPool_of_dvd cols hc j _ (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant
    (fun z => ∑ j, cubicRow (cols j) z * a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,
    cubic_weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  have he (D : Ideal O) (hD : D ∈ gcdPool cols) :=
    compact_gcd_mobius_descent D (gcdPool_cubic_admissible cols hc D hD).2 cols hc a M hM
  calc
    _ ≤ ∑ D ∈ gcdPool cols,
        ‖∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
          ∑ j, ∑ k, cubicGcdTerm D cols a z j k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D hD
      rw [he D hD]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (QuadraticInitialBound.norm_ideal_moebius_le_one E)
        (norm_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.QuotientColumns -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_sum_restrict p _ (by
    intro k hk
    simp [ha k hk])

def quotientColumn {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (j : {j // D ∣ cols j}) : Ideal O := idealQuotient D (cols j.val)

def quotientCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : {j // D ∣ cols j}) : ℂ :=
  cubicRow (quotientColumn D cols j) d * a j.val

lemma quotientColumn_injective {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (idealQuotient_injective_on D j.property k.property he))

lemma quotientColumn_admissible {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ)
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, idealQuotient_mul j.property]
  refine ⟨?_, idealQuotient_norm_le hD0 j.property N (hcols j.val).2⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert hh using 1; ring

lemma compact_descendant_restrict {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    funext j
    simp only [totalQuotient, ite_eq_left j.property, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    funext j
    simp only [descendedCoefficient, totalQuotient, ite_eq_left j.property, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O) :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient, ite_eq_left j.property]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ColumnShells -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicColumnLabel {n : Type*} (cols : n → Ideal O) (N : ℝ) (j : n) :
    Fin (columnDyadicLength N + 1) := divisorDyadicLabel N (cols j)

abbrev CubicColumnShell {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (l : Fin (columnDyadicLength N + 1)) := {j : n // cubicColumnLabel cols N j = l}

lemma cubicColumnShell_bounds {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val/2 ≤ (Ideal.absNorm (cols j.val) : ℝ) ∧
      (Ideal.absNorm (cols j.val) : ℝ) ≤ (2 : ℝ)^l.val := by
  have hp : 1 ≤ (Ideal.absNorm (cols j.val) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryGenerator_ne_zero_ideal _ (hc j.val).2))
  have hb := divisorDyadicLabel_bounds N (cols j.val) hp (hn j.val)
  have hj := j.property
  change divisorDyadicLabel N (cols j.val) = l at hj
  rw [hj] at hb
  exact ⟨hb.1.le,hb.2⟩

lemma cubicColumnShell_scale_le {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val ≤ 2*N := by
  have hh := (cubicColumnShell_bounds cols N hc hn l j).1
  linarith [hn j.val]

lemma cubicColumnShell_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) :
    (∑ l : Fin (columnDyadicLength N + 1), ∑ j : CubicColumnShell cols N l, ‖a j.val‖^2) =
      ∑ j, ‖a j‖^2 := Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => ‖a j‖^2)

theorem cubic_energy_column_shells {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) (R : Finset O) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      (columnDyadicLength N + 1 : ℝ) *
        ∑ l : Fin (columnDyadicLength N + 1), ∑ z ∈ R,
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z * a j.val‖^2 := by
  have hp (z : O) : ‖∑ j, cubicRow (cols j) z*a j‖^2 ≤
      (columnDyadicLength N + 1 : ℝ)*∑ l : Fin (columnDyadicLength N + 1),
        ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 := by
    rw [← Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => cubicRow (cols j) z*a j)]
    calc
      _ ≤ (∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
            (fun l : Fin (columnDyadicLength N + 1) =>
              ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖))
  calc
    _ ≤ ∑ z ∈ R, (columnDyadicLength N + 1 : ℝ)*
        ∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 :=
      Finset.sum_le_sum (fun z hz => hp z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ZeroMode -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

@[simp] lemma cubicRow_one (z : O) : cubicRow 1 z = 1 := by
  simp only [cubicRow, CubicJacobiGlobal.idealSymbol_one, map_one]

theorem cubicDualRow_zero_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hinj : Function.Injective cols) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hN : 0 < N) (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    ‖cubicDualRow cols hc a W M 0‖ ≤
      ((2/N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ := by
  by_cases hu : ∃ j, cols j = 1
  · obtain ⟨j₀, hj₀⟩ := hu
    have ho (j : n) (hj : j ≠ j₀) : cols j ≠ 1 := by
      intro he
      exact hj (hinj (he.trans hj₀.symm))
    have he : cubicDualRow cols hc a W M 0 =
        (star (cubicDualCoefficient cols hc a j₀) * cubicDualCoefficient cols hc a j₀) *
          paperRadialFourier W 0 := by
      rw [cubicDualRow_eq_gram]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single j₀]
        · simp only [hj₀, cubicRow_one, one_mul, Ideal.span_singleton_zero,
            Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div, ite_eq_left isCoprime_one_left]
        · intro k hk hkj
          rw [cubicRow_zero_of_ne_one _ (hc k) (ho k hkj)]
          simp
        · simp
      · intro j hj hjj
        rw [cubicRow_zero_of_ne_one _ (hc j) (ho j hjj)]
        simp
      · simp
    rw [he, norm_mul, norm_mul, norm_star, ← pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Finset.single_le_sum (fun j hj => sq_nonneg ‖cubicDualCoefficient cols hc a j‖)
      (Finset.mem_univ j₀)).trans (cubicDualCoefficient_energy cols hc a N hN hcols)
  · have hz : ∀ j, cols j ≠ 1 := fun j hj => hu ⟨j,hj⟩
    rw [cubicDualRow_zero cols hc hz a W M, norm_zero]
    positivity

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Recurrence -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_smoothed_frequency_recurrence (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (_hunit : ∀ j, cols j ≠ 1) (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols hunit a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hf0 : f 0 = 0 := cubicDualRow_zero cols (fun j => (hcols j).1) hunit a W M
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads f hf hf0]
  exact mul_le_mul_of_nonneg_left hb hM.le

theorem cubic_smoothed_frequency_recurrence_all (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads_with_zero f hf]
  apply mul_le_mul_of_nonneg_left _ hM.le
  exact (norm_add_le _ _).trans (add_le_add
    (cubicDualRow_zero_bound cols (fun j => (hcols j).1) hc a W M N hN0
      (fun j => (hcols j).2.1)) hb)

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CommonFactorBound -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyCost (C ε : ℝ) (hε : 0 < ε) (M N : ℝ) : ℝ :=
  M * (2/N) * (‖paperRadialFourier rowMajorant 0‖ +
    C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
      ∑' l : ℕ, frequencyMajorant M N l)

theorem cubic_common_factor_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M)
        (cols : n → Ideal O) (_hinj : Function.Injective cols)
        (_hc : ∀ j, Admissible (cols j))
        (_hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ) (R : Finset O)
        (_hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M),
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
          ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
            frequencyCost C ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ)) *
              ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
  obtain ⟨C,hC,hrec⟩ := cubic_smoothed_frequency_recurrence_all rowMajorant
  refine ⟨C,hC,?_⟩
  intro n _ _ ε hε M N hM cols hinj hc hcols a R hR
  apply (finite_energy_le_compact_descendants cols hc a R M hM hR).trans
  apply Finset.sum_le_sum
  intro D hD
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  have hDcol := gcdPool_subset_columnDivisorPool cols hc0 hD
  have hDN := columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D hDcol
  have hD0 := gcdPool_ne_zero cols hc0 D hD
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith [hDN.1]
  have hNshort : 1 ≤ N / (Ideal.absNorm D : ℝ) := (one_le_div hDN0).mpr hDN.2
  apply Finset.sum_le_sum
  intro E hE
  have hEdiv := (mem_idealDivisors hD0).mp hE
  have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hEdiv
  have hEN : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  rw [compact_descendant_restrict]
  have hh := hrec ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ))
    (div_pos hM hEN) hNshort (quotientColumn D cols) (quotientColumn_injective D cols hinj)
    (fun j => ⟨quotientColumn_admissible D cols hc j, cubic_quotient_in_shell D cols hc N hcols j⟩)
    (quotientCoefficient D cols a (idealGenerator E))
  rw [quotientCoefficient_energy] at hh
  convert hh using 1
  dsimp only [frequencyCost]
  ring

theorem common_factor_uniform_cost {n : Type*} [Fintype n]
    (C ε U M N : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hnorm : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ)
    (hcost : ∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U) :
    (∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) *
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
      U*(DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2 := by
  have he := descended_energy_small_power ε hε cols hc N hN hnorm a
  have hsub := gcdPool_subset_columnDivisorPool cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hc j).2)
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        U * ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcost D hD E hE) (by positivity)
    _ = U*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      simp only [Finset.mul_sum]
    _ ≤ U*(∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hU
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hnot => by positivity)
    _ ≤ U*((DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left he hU
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.DescendantBounds -/

section

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma descendant_cross_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) :
    ((M/E)*(N/D))^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact mul_le_mul (div_le_self hM hE) (div_le_self hN hD) (by positivity) hM

lemma descendant_asymmetric_le (M N D E ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hξ : 1 ≤ ξ) :
    (M/E)^(1-ξ)*(N/D)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hp : E^(ξ-1) ≤ D^(2*ξ-1) :=
    (Real.rpow_le_rpow hE0.le hED (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
  have hr : E^(ξ-1)/D^(2*ξ-1) ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hD0 _)).mpr hp
  have he : E^(1-ξ) = (E^(ξ-1))⁻¹ := by
    rw [← Real.rpow_neg hE0.le]
    congr 1
    ring
  calc
    _ = (M^(1-ξ)*N^(2*ξ-1))*(E^(ξ-1)/D^(2*ξ-1)) := by
      rw [Real.div_rpow hM.le hE0.le, Real.div_rpow hN.le hD0.le, he]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hr

lemma descendant_loss_le (M N D E δ ε : ℝ) (hM : 1 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hDN : D ≤ N)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (M/E)^(-δ)*(N/D)^(3*δ+ε) ≤ N^(4*δ+ε) := by
  have hM0 : 0 < M := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hEM : E/M ≤ N := (div_le_self hE0.le hM).trans (hED.trans hDN)
  have hfirst : (M/E)^(-δ) ≤ N^δ := by
    rw [Real.rpow_neg (div_pos hM0 hE0).le, ← Real.inv_rpow (div_pos hM0 hE0).le, inv_div]
    exact Real.rpow_le_rpow (by positivity) hEM hδ
  have hsecond : (N/D)^(3*δ+ε) ≤ N^(3*δ+ε) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hD) (by positivity)
  calc
    _ ≤ N^δ*N^(3*δ+ε) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hN]
      congr 1
      ring

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hY : 1 ≤ N/D := (one_le_div hD0).mpr hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CostGrowth -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic EisensteinSchwartzPoisson SevenEighths.CubicDyadicDecay
noncomputable section

theorem HasCubicExponent.frequencyCost_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 ≤ C → ∀ hε : 0 < ε,
      ∀ X Y : ℝ, 0 < X → 1 ≤ Y →
        frequencyCost C ε hε X Y ≤
          (X*(2/Y))*‖paperRadialFourier rowMajorant 0‖ +
          (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A) * Y^ε *
            (Y^(3*δ)*X^(-δ) * (decayConstant (1/3+δ)*(X*Y)^(2/3 : ℝ) +
              decayConstant (ξ+δ)*X^(1-ξ)*Y^(2*ξ-1))) := by
  obtain ⟨A,hA,hb⟩ := h.full_element_bound hξ δ hδ
  refine ⟨A,hA,?_⟩
  intro C ε hC hε X Y hX hY
  have hY0 : 0 < Y := by linarith
  have hs := sieve_poisson_bound (fun K => elementSieveNorm K Y) A X Y δ ξ hA.le hX hY0
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun K hK => elementSieveNorm_nonneg K Y)
    (fun K hK => by simpa only [mul_comm Y (K^(1/3 : ℝ))] using hb K Y hK hY)
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*Y^ε := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  have he := add_le_add_left hh ((X*(2/Y))*‖paperRadialFourier rowMajorant 0‖)
  convert he using 1 <;> try dsimp only [frequencyCost, frequencyMajorant]
  all_goals ring

theorem frequencyCost_descendant_of_bound (C ε A δ ξ M N d e : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hα3 : 1/3+δ < 3) (hβ3 : ξ+δ < 3)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) (hdN : d ≤ N)
    (hb : frequencyCost C ε hε (M/e) (N/d) ≤
      ((M/e)*(2/(N/d)))*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*(N/d)^ε*
        ((N/d)^(3*δ)*(M/e)^(-δ) *
          (decayConstant (1/3+δ)*((M/e)*(N/d))^(2/3 : ℝ) +
            decayConstant (ξ+δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)))) :
    frequencyCost C ε hε (M/e) (N/d) ≤
      2*M*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*N^ε*
        (N^(3*δ)*M^(-δ) *
          (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
            decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1))) := by
  have hd : 1 ≤ d := he.trans hed
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hp := (decayConstant_pos (1/3+δ) (by linarith) hα3).le
  have hq := (decayConstant_pos (ξ+δ) (by linarith) hβ3).le
  have henv := poisson_envelope_descendant_le M N e d δ ξ
    (decayConstant (1/3+δ)) (decayConstant (ξ+δ)) hM hN he hed hδ hξ hp hq
  have hny : (N/d)^ε ≤ N^ε := Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd) hε.le
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (descendant_unit_scale_le M N d e hM.le hN hd he hdN) (norm_nonneg _)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hny hfac
    · exact henv
    · positivity
    · positivity

lemma poisson_envelope_absorb (M N δ ε ξ H Z P Q : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    2*M*Z + H*N^ε*(N^(3*δ)*M^(-δ)*
      (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1))) ≤
        (2*Z+H*(P+Q))*N^(3*δ+ε)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let X := (M*N)^(2/3 : ℝ)
  let Y := M^(1-ξ)*N^(2*ξ-1)
  let S := M+X+Y
  have hX : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hshape : P*X+Q*Y ≤ (P+Q)*S := by
    dsimp only [S]
    nlinarith [mul_nonneg hP hM0.le, mul_nonneg hQ hM0.le, mul_nonneg hP hY, mul_nonneg hQ hX]
  have hsmall : M^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hloss : 1 ≤ N^(3*δ+ε) := Real.one_le_rpow hN (by positivity)
  have hunit : 2*M*Z ≤ 2*Z*N^(3*δ+ε)*S := by
    have hmS : M ≤ S := by dsimp [S]; linarith
    calc
      _ = 2*Z*M := by ring
      _ ≤ 2*Z*S := mul_le_mul_of_nonneg_left hmS (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Z) hS) (sub_nonneg.mpr hloss)]
  have htail : H*N^ε*(N^(3*δ)*M^(-δ)*(P*X+Q*Y)) ≤
      H*(P+Q)*N^(3*δ+ε)*S := by
    have hs : M^(-δ)*(P*X+Q*Y) ≤ (P+Q)*S :=
      (mul_le_of_le_one_left (by positivity) hsmall).trans hshape
    have hpow : N^ε*N^(3*δ) = N^(3*δ+ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = H*(N^ε*N^(3*δ))*(M^(-δ)*(P*X+Q*Y)) := by ring
      _ ≤ H*(N^ε*N^(3*δ))*((P+Q)*S) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [hpow]; ring
  have hh := add_le_add hunit htail
  convert hh using 1 <;> dsimp only [S,X,Y] <;> ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.AnnularImprovement -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
open SevenEighths.CubicDyadicDecay
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem HasCubicExponent.annular_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (M N : ℝ), 1 ≤ M → 1 ≤ N → ∀ (cols : n → Ideal O), Function.Injective cols →
      (∀ j, Admissible (cols j)) →
      (∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ (a : n → ℂ) (R : Finset O),
        (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z*a j‖^2) ≤
          K*N^(6*θ)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1))*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hcf⟩ := cubic_common_factor_frequency_bound
  obtain ⟨A,hA,hfb⟩ := h.frequencyCost_bound hξ hξ2 θ hθ hθsmall
  let Z := ‖paperRadialFourier rowMajorant 0‖
  let P := decayConstant (1/3+θ)
  let Q := decayConstant (ξ+θ)
  let H := 2*C*IdealCoprimeSieveOperator.supportConstant θ hθ*A
  let V := 1+2*Z+H*(P+Q)
  let Dv := DivisorBlockCauchy.divisorConstant θ hθ
  have hZ : 0 ≤ Z := norm_nonneg _
  have hP : 0 ≤ P := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hQ : 0 ≤ Q := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hH : 0 ≤ H := by
    dsimp [H]
    have hs := (IdealCoprimeSieveOperator.supportConstant_pos θ hθ).le
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hDv : 0 < Dv := DivisorBlockCauchy.divisorConstant_pos θ hθ
  refine ⟨V*Dv^2, by positivity, ?_⟩
  intro n _ _ M N hM hN cols hinj hc hcols a R hR
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let U := V*N^(4*θ)*S
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcost (D : Ideal O) (hD : D ∈ gcdPool cols) (E : Ideal O) (hE : E ∈ idealDivisors D) :
      frequencyCost C θ hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U := by
    have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
    have hD0 := gcdPool_ne_zero cols hc0 D hD
    have hDE := (mem_idealDivisors hD0).mp hE
    have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hDE
    have he1 : 1 ≤ (Ideal.absNorm E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
    have hed : (Ideal.absNorm E : ℝ) ≤ (Ideal.absNorm D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
        (map_dvd Ideal.absNorm hDE)
    have hdN := (columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D
      (gcdPool_subset_columnDivisorPool cols hc0 hD)).2
    have hd0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have he0 : 0 < (Ideal.absNorm E : ℝ) := by linarith
    have hh := hfb C θ hC hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ))
      (div_pos hM0 he0) ((one_le_div hd0).mpr hdN)
    have hd := frequencyCost_descendant_of_bound C θ A θ ξ M N
      (Ideal.absNorm D) (Ideal.absNorm E) hC hθ hA.le hθ.le (by linarith)
      (by linarith) (by linarith) hM0 hN0 he1 hed hdN hh
    have hb := poisson_envelope_absorb M N θ θ ξ H Z P Q hM hN hθ.le hθ.le hH hZ hP hQ
    have hx : 3*θ+θ = 4*θ := by ring
    rw [hx] at hb
    apply (hd.trans hb).trans
    change (2*Z+H*(P+Q))*N^(4*θ)*S ≤ V*N^(4*θ)*S
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) (Real.rpow_nonneg hN0.le _)) hS
  have henergy := (hcf θ hθ M N hM0 cols hinj hc hcols a R hR).trans
    (common_factor_uniform_cost C θ U M N hθ hU hN0.le cols hc (fun j => (hcols j).2) a hcost)
  have hp : N^(4*θ)*(N^θ)^2 = N^(6*θ) := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ U*(Dv*N^θ)^2*∑ j, ‖a j‖^2 := henergy
    _ = (V*Dv^2)*(N^(4*θ)*(N^θ)^2)*S*∑ j, ‖a j‖^2 := by dsimp [U]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FullImprovement -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve (columnDyadicLength)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma improved_shape_shell (M N Y ξ : ℝ) (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y)
    (hYN : Y ≤ 2*N) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    M+(M*Y)^(2/3 : ℝ)+M^(1-ξ)*Y^(2*ξ-1) ≤
      8*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hp : (2:ℝ)^(2/3 : ℝ) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/3 : ℝ)≤3)
    norm_num at hh ⊢
    exact hh
  have hq : (2:ℝ)^(2*ξ-1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*ξ-1 ≤ 3 by linarith)
    norm_num at hh
    exact hh
  have hcross := Real.rpow_le_rpow (mul_nonneg hM.le hY)
    (mul_le_mul_of_nonneg_left hYN hM.le) (by norm_num : (0:ℝ)≤2/3)
  have hsec := Real.rpow_le_rpow hY hYN (show 0 ≤ 2*ξ-1 by linarith)
  rw [show M*(2*N) = 2*(M*N) by ring, Real.mul_rpow (by norm_num) (mul_pos hM hN).le] at hcross
  rw [Real.mul_rpow (by norm_num) hN.le] at hsec
  have hx := (hcross.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_pos hM hN).le _)))
  have hy := mul_le_mul_of_nonneg_left
    (hsec.trans (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hN.le _)))
      (Real.rpow_nonneg hM.le (1-ξ))
  nlinarith

lemma improved_loss_shell (N Y θ : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ 2*N)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/2) : Y^(6*θ) ≤ 8*N^(6*θ) := by
  have hh := Real.rpow_le_rpow hY hYN (show 0 ≤ 6*θ by positivity)
  rw [Real.mul_rpow (by norm_num) hN] at hh
  have hp : (2:ℝ)^(6*θ) ≤ 8 := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 6*θ ≤ 3 by linarith)
    norm_num at he
    exact he
  exact hh.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN _))

theorem HasCubicExponent.full_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*N^(7*θ)*
        (M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  obtain ⟨K,hK,hb⟩ := h.annular_improved hξ hξ2 θ hθ hθsmall
  let D : ℝ := 2+1/(θ*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  refine ⟨64*K*D, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let cols : idealRange N → Ideal O := fun j => j.val
  have hc (j : idealRange N) : Admissible (cols j) := (mem_idealRange.mp j.property).1
  have hn (j : idealRange N) : (Ideal.absNorm (cols j) : ℝ) ≤ N := (mem_idealRange.mp j.property).2
  let R := elementRange M
  have hR (z : O) (hz : z ∈ R) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    ((mem_elementRange M z).mp hz).2
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  have hsector (l : Fin (columnDyadicLength N + 1)) :
      (∑ z ∈ R, ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2) ≤
        (64*K*N^(6*θ)*S)*∑ j : CubicColumnShell cols N l, ‖a j.val‖^2 := by
    by_cases hne : Nonempty (CubicColumnShell cols N l)
    · obtain ⟨j₀⟩ := hne
      have hYN := cubicColumnShell_scale_le cols N hc hn l j₀
      have hY1 : 1 ≤ (2:ℝ)^l.val := one_le_pow₀ (by norm_num)
      have hs := hb M ((2:ℝ)^l.val) hM hY1
        (fun j : CubicColumnShell cols N l => cols j.val)
        (fun j k he => Subtype.ext (Subtype.ext he)) (fun j => hc j.val)
        (fun j => cubicColumnShell_bounds cols N hc hn l j)
        (fun j => a j.val) R hR
      have hl := improved_loss_shell N ((2:ℝ)^l.val) θ hN0.le (by positivity) hYN hθ.le hθsmall.le
      have ht := improved_shape_shell M N ((2:ℝ)^l.val) ξ hM0 hN0 (by positivity) hYN
        (by linarith) hξ2
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl hK.le) ht (by positivity) (by positivity)
      convert hh using 1; dsimp only [S]; ring
    · let : IsEmpty (CubicColumnShell cols N l) := not_nonempty_iff.mp hne
      simp
  have hsum := cubic_energy_column_shells cols N a R
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hsector l)
  rw [← Finset.mul_sum, cubicColumnShell_energy cols N a] at hle
  have he := hsum.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power θ hθ N hN
  have he' := he.trans (mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (64*K*N^(6*θ)*S)*∑ j, ‖a j‖^2 by positivity))
  have hp : N^θ*N^(6*θ) = N^(7*θ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val*a j‖^2) ≤ _
  apply he'.trans_eq
  calc
    _ = (64*K*D)*(N^θ*N^(6*θ))*S*∑ j, ‖a j‖^2 := by dsimp [D]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ExponentImprovement -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def enlargementExponent (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

lemma enlargement_bounds (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    1 ≤ enlargementExponent ξ ∧ enlargementExponent ξ ≤ SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 0 < 3*ξ-1 := by linarith
  constructor
  · unfold enlargementExponent
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargementExponent SevenEighths.HeathBrownIteration.step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma enlargement_cross_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    (enlargementExponent ξ+1)*(2/3 : ℝ) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

lemma enlargement_secondary_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    enlargementExponent ξ*(1-ξ)+(2*ξ-1) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

theorem enlarged_improved_shape (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    let T := max M (N^(enlargementExponent ξ))
    T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤
      3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ)) := by
  let α := enlargementExponent ξ
  let β := SevenEighths.HeathBrownIteration.step ξ
  let T := max M (N^α)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hαβ : α ≤ β := (enlargement_bounds ξ hξ).2
  have hNb : 0 ≤ N^β := Real.rpow_nonneg hN0.le _
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have ht : T ≤ M+N^β := by
    apply max_le
    · exact le_add_of_nonneg_right hNb
    · exact (Real.rpow_le_rpow_of_exponent_le hN hαβ).trans (le_add_of_nonneg_left hM0.le)
  have hnx : (N^α*N)^(2/3 : ℝ) = N^β := by
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le, enlargement_cross_identity ξ hξ]
  have htc : (T*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^β := by
    by_cases hm : M ≤ N^α
    · dsimp only [T]
      rw [max_eq_right hm, hnx]
      exact le_add_of_nonneg_left hcross
    · dsimp only [T]
      rw [max_eq_left (le_of_not_ge hm)]
      exact le_add_of_nonneg_right hNb
  have hts : T^(1-ξ)*N^(2*ξ-1) ≤ N^β := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 α)
      (le_max_right M (N^α)) (show 1-ξ ≤ 0 by linarith)
    calc
      _ ≤ (N^α)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN0.le _)
      _ = N^β := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, enlargement_secondary_identity ξ hξ]
  change T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤ 3*(M+N^β+(M*N)^(2/3 : ℝ))
  linarith

theorem HasCubicExponent.improve {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) < ξ) (hξ2 : ξ ≤ 2) :
    HasCubicExponent (SevenEighths.HeathBrownIteration.step ξ) := by
  intro ε hε
  let θ := min (ε/14) (1/4 : ℝ)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθε : 7*θ ≤ ε := by
    have hh : θ ≤ ε/14 := min_le_left _ _
    linarith
  obtain ⟨C,hC,hb⟩ := h.full_improved hξ.le hξ2 θ hθ hθsmall
  refine ⟨3*C, by positivity, ?_⟩
  intro M N hM hN
  let T := max M (N^(enlargementExponent ξ))
  have hT : 1 ≤ T := hM.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hp : N^(7*θ) ≤ (M*N)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hN hθε).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hε.le)
  have ht := enlarged_improved_shape M N ξ hM hN hξ.le
  have hshape : 0 ≤ M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ) := by positivity
  calc
    _ ≤ sieveNorm T N := sieveNorm_mono (le_max_left _ _) le_rfl
    _ ≤ elementSieveNorm T N := sieveNorm_le_elementSieveNorm T N
    _ ≤ C*N^(7*θ)*(T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1)) := hb T N hT hN
    _ ≤ C*N^(7*θ)*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ C*(M*N)^ε*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Sharp -/

section

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

theorem hasCubicExponent_four_thirds : HasCubicExponent (4/3 : ℝ) := by
  intro ε hε
  obtain ⟨ξ, hξ, hξ2, hξε, hx⟩ := SevenEighths.HeathBrownIteration.finite_improvement
    hasCubicExponent_initial (fun x hx hx2 hp => hp.improve hx hx2)
    (show 0 < ε/2 by positivity)
  obtain ⟨C,hC,hb⟩ := hx (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 0 < M*N := mul_pos hM0 hN0
  have hp : 1 ≤ N^(ε/2) := Real.one_le_rpow hN (by positivity)
  have hNpow : N^ξ ≤ N^(4/3 : ℝ)*N^(ε/2) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hξε.le
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg hMN.le _
  have hs : M+N^ξ+(M*N)^(2/3 : ℝ) ≤
      N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by
    nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hp),
      mul_nonneg hcross (sub_nonneg.mpr hp)]
  have hnp : N^(ε/2) ≤ (M*N)^(ε/2) :=
    Real.rpow_le_rpow hN0.le (by nlinarith) (by positivity)
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^ξ+(M*N)^(2/3 : ℝ)) := hb M N hM hN
    _ ≤ C*(M*N)^(ε/2)*(N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnp (by positivity)) (by positivity)
    _ = _ := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add hMN]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by ring
        _ = _ := by rw [he]

lemma four_thirds_le_cross (M N : ℝ) (_hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc
    N^(4/3 : ℝ) = (N*N)^(2/3 : ℝ) := by
      rw [Real.mul_rpow hN0 hN0, ← Real.rpow_add (by linarith : 0 < N)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hN0 hN0)
      (mul_le_mul_of_nonneg_right hNM hN0) (by norm_num)

theorem sieveNorm_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := hasCubicExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  by_cases hNM : N ≤ M
  · have hh := four_thirds_le_cross M N hM hN hNM
    calc
      _ ≤ C*(M*N)^ε*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := hb M N hM hN
      _ ≤ C*(M*N)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · have hMN := le_of_not_ge hNM
    have hh := four_thirds_le_cross N M hN hM hMN
    have hs : N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ) ≤
        2*(M+N+(M*N)^(2/3 : ℝ)) := by
      rw [mul_comm N M] at hh ⊢
      linarith
    calc
      _ = sieveNorm N M := sieveNorm_reciprocity M N
      _ ≤ C*(N*M)^ε*(N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ)) := hb N M hN hM
      _ ≤ C*(N*M)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_comm N M]; ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Completion -/

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, summand Ψ W X I J * d (I * J ^ 3)

theorem markedCompletedT_one (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun _ => 1) = completedT Ψ W X := by
  simp only [markedCompletedT, mul_one, completedT]

theorem markedCompletedT_congr_nonzero (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A ≠ 0, d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hI : I = 0
  · simp only [hI, summand_zero_left, zero_mul]
  by_cases hJ : J = 0
  · simp only [hJ, summand_zero_right, zero_mul]
  rw [h (I * J ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))]

theorem markedCompletedT_summable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

theorem markedCompletedT_prime_priority {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (L : σ → Finset (Ideal Eis))
    (a : σ → Ideal Eis → ℂ) (H : Ideal Eis) (hH : H ≠ 0)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A))) =
    ∑ J ∈ slots.powerset,
      primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
        markedCompletedT Ψ W X (fun A =>
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A)) := by
  have hmark (A : Ideal Eis) (hA : A ≠ 0) :
      primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A)) =
      ∑ J ∈ slots.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A) := by
    rw [mul_comm (H ^ 3) A, ideal_primeSupport_mul_cube A H hA hH,
      Finset.union_comm, primeMark_priority]
    simp only [primeMark_residual_lists]
  rw [markedCompletedT_congr_nonzero Ψ W X _ _ hmark,
    markedCompletedT_finset_sum slots.powerset Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

theorem markedExpandedTerm_finite_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem marked_cube_inverse_vstar (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CompletionSplit -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem marked_cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H^3*A)))).Finite := by
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, markedExpandedTerm Ψ W X d I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_markedCompletedT_reopen]
  simp only [hzero, tsum_zero]

theorem marked_large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)*d (I*B^3)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=markedExpandedTerm Ψ W X d I H J := by
    simp only [f,markedExpandedTerm,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal O × Ideal O => markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem marked_large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((markedExpandedTerm_finite_support Ψ W hW X hX d).subset (by
      intro p hp
      by_contra hn
      have he : markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [ite_eq_left h,weighted_markedCompletedT_reopen]
      · simp only [ite_eq_right h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_large_cube_inner_reopen Ψ W hW X H₀ hX d)

theorem marked_completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*d I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A))
  have hf := marked_cube_inverse_finite_support Ψ W hW X hX d
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [marked_cube_inverse Ψ W hW X hX d,←marked_large_cube_reopen Ψ W hW X H₀ hX d]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CompletionSupport -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem marked_large_cube_sum_comm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3)) =
      ∑'B:Ideal O,∑'I:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let a : Ideal O×Ideal O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2*d (p.1*p.2^3)
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero,zero_mul]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal O) (Ideal O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal O×Ideal O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal O×Ideal O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem marked_large_cube_sum_finite (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B*d (I*B^3)) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal O,summand (rowTwist Ψ m f z) W X I B*d (I*B^3) := by
  rw [marked_large_cube_sum_comm _ W hWc X H₀ hX d]
  simp only [mul_assoc, tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero,zero_mul]

theorem marked_inner_completed_sum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal O) (hB : B≠0) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,summand Ψ W X I B*d (I*B^3)) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*d (I*B^3) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  simp only [mul_assoc, tsum_mul_left]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Decomposition -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure HybridColumnData where
  common : Ideal Eis
  residualN : Ideal Eis
  residualB : Ideal Eis
  square : Ideal Eis
  n_squarefree : Squarefree (common * residualN)
  g_squarefree : Squarefree (common * residualB)
  residual_coprime : IsCoprime residualN residualB
  square_ne_zero : square ≠ 0

def HybridColumnData.reconstruct (d : HybridColumnData) : Ideal Eis × Ideal Eis :=
  (d.common * d.residualN, (d.common * d.residualB) * d.square ^ 2)

theorem HybridColumnData.common_ne_zero (d : HybridColumnData) : d.common ≠ 0 :=
  ne_zero_of_dvd_ne_zero d.n_squarefree.ne_zero (dvd_mul_right _ _)

theorem HybridColumnData.common_eq_gcd (d : HybridColumnData) :
    d.common = gcd (d.common * d.residualN) (d.common * d.residualB) := by
  rw [gcd_mul_left, normalize_eq, Ideal.isCoprime_iff_gcd.mp d.residual_coprime, mul_one]

theorem HybridColumnData.residual_product_squarefree (d : HybridColumnData) :
    Squarefree (d.residualN * d.residualB) := by
  have hm := (squarefree_mul_iff.mp d.n_squarefree).2.2
  have hh := (squarefree_mul_iff.mp d.g_squarefree).2.2
  exact squarefree_mul_iff.mpr ⟨d.residual_coprime.isRelPrime, hm, hh⟩

theorem HybridColumnData.primary_factors (d : HybridColumnData)
    (hn : CompletedGauss.primaryGenerator (d.common * d.residualN) ≠ 0)
    (hb : CompletedGauss.primaryGenerator ((d.common * d.residualB) * d.square ^ 2) ≠ 0) :
    CompletedGauss.primaryGenerator d.common ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualN ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualB ≠ 0 ∧
    CompletedGauss.primaryGenerator d.square ≠ 0 ∧
    CompletedGauss.primaryGenerator (d.common * d.square) ≠ 0 := by
  rw [CompletedGauss.primaryGenerator_mul] at hn
  have hpow : CompletedGauss.primaryGenerator (d.square ^ 2) =
      CompletedGauss.primaryGenerator d.square ^ 2 :=
    map_pow CompletedGauss.primaryGeneratorHom d.square 2
  rw [CompletedGauss.primaryGenerator_mul, CompletedGauss.primaryGenerator_mul, hpow] at hb
  have hc := (mul_ne_zero_iff.mp hn).1
  have hm := (mul_ne_zero_iff.mp hn).2
  have hch := (mul_ne_zero_iff.mp hb).1
  have hh := (mul_ne_zero_iff.mp hch).2
  have ht : CompletedGauss.primaryGenerator d.square ≠ 0 := by
    intro hz
    apply (mul_ne_zero_iff.mp hb).2
    simp [hz]
  refine ⟨hc, hm, hh, ht, ?_⟩
  rw [CompletedGauss.primaryGenerator_mul]
  exact mul_ne_zero hc ht

theorem HybridColumnData.residual_norm_identity (d : HybridColumnData) :
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) =
      ((Ideal.absNorm (d.common * d.residualN) : ℝ) *
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ)) /
      ((Ideal.absNorm d.common : ℝ) ^ 2 * (Ideal.absNorm d.square : ℝ) ^ 2) := by
  have hc : (Ideal.absNorm d.common : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.common_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm d.square : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.square_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  field_simp

theorem HybridColumnData.residual_norm_bounds (d : HybridColumnData)
    (N B C T : ℝ) (hN : 0 ≤ N) (_hB : 0 ≤ B) (hC : 0 < C) (hT : 0 < T)
    (hn : (Ideal.absNorm (d.common * d.residualN) : ℝ) ≤ N)
    (hb : (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B)
    (hc : C ≤ (Ideal.absNorm d.common : ℝ))
    (ht : T ≤ (Ideal.absNorm d.square : ℝ)) :
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  have hn' := hn
  have hb' := hb
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn' hb'
  have hm : (Ideal.absNorm d.residualN : ℝ) ≤ N / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualN : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc
          (Nat.cast_nonneg (Ideal.absNorm d.residualN))
      _ ≤ N := hn'
  have hh : (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) := by
    apply (le_div_iff₀ (mul_pos hC (sq_pos_of_pos hT))).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualB : ℝ) *
          (Ideal.absNorm d.square : ℝ) ^ 2 := by
        calc
          _ = C * (Ideal.absNorm d.residualB : ℝ) * T ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ ≤ B := hb'
  refine ⟨hm, hh, ?_⟩
  calc
    _ = (Ideal.absNorm d.residualN : ℝ) * (Ideal.absNorm d.residualB : ℝ) := by
      rw [map_mul, Nat.cast_mul]
    _ ≤ (N / C) * (B / (C * T ^ 2)) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) (div_nonneg hN hC.le)
    _ = N * B / (C ^ 2 * T ^ 2) := by ring

theorem HybridColumnData.reconstruct_injective :
    Function.Injective HybridColumnData.reconstruct := by
  intro d e he
  have hn : d.common * d.residualN = e.common * e.residualN := congrArg Prod.fst he
  have hb : d.square ^ 2 * (d.common * d.residualB) =
      e.square ^ 2 * (e.common * e.residualB) := by
    simpa only [HybridColumnData.reconstruct, mul_comm] using congrArg Prod.snd he
  obtain ⟨ht, hg⟩ := QuadraticSquarefreeKernel.squarefree_decomposition_unique
    d.square_ne_zero e.square_ne_zero d.g_squarefree e.g_squarefree hb
  have hc : d.common = e.common := by
    calc
      _ = gcd (d.common * d.residualN) (d.common * d.residualB) := d.common_eq_gcd
      _ = gcd (e.common * e.residualN) (e.common * e.residualB) := by rw [hn, hg]
      _ = e.common := e.common_eq_gcd.symm
  rw [hc] at hn hg
  have hm := mul_left_cancel₀ e.common_ne_zero hn
  have hh := mul_left_cancel₀ e.common_ne_zero hg
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def HybridColumnData.toOriginal (d : HybridColumnData) :
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  ⟨d.reconstruct, d.n_squarefree,
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero 2 d.square_ne_zero)⟩

theorem HybridColumnData.toOriginal_bijective : Function.Bijective HybridColumnData.toOriginal := by
  constructor
  · intro d e he
    exact reconstruct_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨c, m, h, t, hn, hb, hcs, hms, hhs, hcm, hch, hmh, ht⟩ :=
      hybrid_column_decomposition p.val.1 p.val.2 p.property.1 p.property.2
    refine ⟨⟨c, m, h, t, ?_, ?_, hmh, ht⟩, ?_⟩
    · exact hn ▸ p.property.1
    · exact squarefree_mul_iff.mpr ⟨hch, hcs, hhs⟩
    · apply Subtype.ext
      exact Prod.ext hn.symm hb.symm

def hybridColumnEquiv : HybridColumnData ≃
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  Equiv.ofBijective HybridColumnData.toOriginal HybridColumnData.toOriginal_bijective

theorem hybrid_column_reindex (f : Ideal Eis → Ideal Eis → ℂ) :
    (∑' p : {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0}, f p.val.1 p.val.2) =
      ∑' d : HybridColumnData,
        f (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) := by
  exact (hybridColumnEquiv.tsum_eq (fun p => f p.val.1 p.val.2)).symm

def hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis)) : Finset HybridColumnData :=
  S.preimage HybridColumnData.reconstruct HybridColumnData.reconstruct_injective.injOn

@[simp] theorem mem_hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis))
    (d : HybridColumnData) :
    d ∈ hybridColumnSupport S ↔ d.reconstruct ∈ S := Finset.mem_preimage

theorem hybrid_finite_column_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0)
    (f : Ideal Eis × Ideal Eis → A) :
    (∑ p ∈ S, f p) = ∑ d ∈ hybridColumnSupport S, f d.reconstruct := by
  symm
  apply Finset.sum_preimage
  intro p hp hn
  obtain ⟨d, hd⟩ := HybridColumnData.toOriginal_bijective.surjective ⟨p, hS p hp⟩
  exact (hn ⟨d, congrArg Subtype.val hd⟩).elim

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Hybrid -/

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

local notation "Eis" => ActualEisensteinCubic.O

def inverseCubicKernel (P n : Ideal Eis) : ℂ :=
  star (ConcreteTraceCRT.eisEmbedding
    (CubicJacobiGlobal.idealSymbol P (CompletedGauss.primaryGenerator n)))

theorem inverseCubicKernel_eq_inverse_square (P n : Ideal Eis) :
    inverseCubicKernel P n =
      (CanonicalRowCompletion.idealRowHom (CompletedGauss.primaryGenerator n) P)⁻¹ ^ 2 := by
  rw [inv_pow, CanonicalRowCompletion.idealRowHom_square,
    inverse_eq_square_of_fourth_eq (CubicSieve.idealSymbol_fourth P _)]
  exact (CubicSieve.idealKernel_square_eq_star P n).symm

theorem inverseCubicKernel_norm_le_one (P n : Ideal Eis) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star, CubicSieve.idealKernel] using
    CubicSieve.idealKernel_norm_le_one P n

def hybridCubicCoefficient (R r h t : Ideal Eis) (a : Ideal Eis → ℂ)
    (P : Ideal Eis) : ℂ :=
  (a (R * P) * inverseCubicKernel P r * (if IsCoprime P (h * t) then 1 else 0)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤ 256 := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal Eis) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ 128 * (2 * L) := by
    apply DescentFiberCost.finite_ideal_count_real S (2 * L) (by linarith)
    · intro P hP hz
      have hn := hP0 P hP
      simp [hz] at hn
    · intro P hP
      exact (hS P hP).2
  have hterm (P : Ideal Eis) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (128 * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 256 := by field_simp; ring

theorem hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, ite_eq_left, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (inverseCubicKernel_norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem inverseCubicKernel_mul_left (R P n : Ideal Eis) :
    inverseCubicKernel (R * P) n = inverseCubicKernel R n * inverseCubicKernel P n := by
  simp only [inverseCubicKernel, CubicJacobiGlobal.idealSymbol_mul, map_mul, star_mul]
  ring

theorem inverseCubicKernel_mul_right (P n m : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  rw [map_mul, star_mul]
  ring

theorem inverseCubicKernel_quotients (R P' r c' m : Ideal Eis)
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    inverseCubicKernel (R * P') ((r * c') * m) =
      inverseCubicKernel R ((r * c') * m) * inverseCubicKernel P' r *
        inverseCubicKernel P' (c' * m) := by
  rw [inverseCubicKernel_mul_left, mul_assoc r c' m,
    inverseCubicKernel_mul_right P' r (c' * m) hP']
  ring

theorem inverseCubicKernel_eq_zero_of_not_coprime (P n : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hn : CompletedGauss.primaryGenerator n ≠ 0) (hcop : ¬ IsCoprime P n) :
    inverseCubicKernel P n = 0 := by
  have hc := CubicSieve.idealSymbol_cube_mask P (CompletedGauss.primaryGenerator n) hP
  rw [(CompletedGauss.primaryGenerator_spec n hn).1, ite_eq_right hcop] at hc
  have hz := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hc
  simp only [inverseCubicKernel, hz, star_zero]

theorem hybrid_cubic_column_mask
    (P n b c m h t : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) =
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [inverseCubicKernel_eq_zero_of_not_coprime P n hP hngen hPn]
    simp

theorem hybrid_original_kernel_decomposition
    (k P n b c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) *
      inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
        (inverseCubicKernel P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hybrid_quadratic_square_mask k n b c m h t hk hn hb hct]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients (R r k' P' c' m h : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel (R * P') ((r * c') * m) =
    (CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel R ((r * c') * m)) *
      inverseCubicKernel P' r *
      CanonicalQuadraticSieve.quadraticRow k'
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P' (c' * m) := by
  rw [CanonicalQuadraticSieve.quadraticRow_mul (R * r) k' hk,
    inverseCubicKernel_quotients R P' r c' m hP']
  ring

def hybridColumnCoefficient (R r : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  beta (r * c) m h *
    CanonicalQuadraticSieve.quadraticRow (R * r) (CompletedGauss.primaryGenerator (m * h)) *
    inverseCubicKernel R ((r * c) * m)

theorem hybridColumnCoefficient_norm_le_one (R r c m h : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ *
      ‖CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h))‖ ≤ 1 := by
    exact (mul_le_mul hb (CanonicalQuadraticSieve.quadraticRow_norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (inverseCubicKernel_norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem normalized_ideal_product_weight (R P : Ideal Eis) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hybrid_extracted_block_identity
    (R r k' P' c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
          (CompletedGauss.primaryGenerator (m * h)) *
        inverseCubicKernel (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient R r beta c m h *
      CanonicalQuadraticSieve.quadraticRow k' (CompletedGauss.primaryGenerator (m * h)) *
      hybridCubicCoefficient R r h t a P' * inverseCubicKernel P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

def hybridInner (nset bset : Finset (Ideal Eis))
    (beta : Ideal Eis → Ideal Eis → ℂ) (k P : Ideal Eis) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * CanonicalQuadraticSieve.quadraticRow k
      (CompletedGauss.primaryGenerator (n * b)) * inverseCubicKernel P n *
        (if IsCoprime P b then 1 else 0)

def hybridRow (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner nset bset beta k P

def hybridDivisorTerm (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k R : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * hybridInner nset bset beta k P else 0

theorem hybridRow_mobius (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k : Ideal Eis) (hk : k ≠ 0) :
    hybridRow Pset nset bset a beta k =
      ∑ R ∈ idealDivisors k, (moebius R : ℂ) *
        ∑ P ∈ Pset, if R ∣ P then
          a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
            hybridInner nset bset beta k P else 0 := by
  unfold hybridRow
  conv_lhs => simp only [ideal_coprime_mobius k _ hk, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hRP : R ∣ P <;> simp only [hRP, ite_true, ite_false, mul_zero, zero_mul]
  ring

theorem hybrid_first_mask_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 1 ≤ K →
      ∀ (rows Pset nset bset : Finset (Ideal Eis))
        (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ R ∈ rows.biUnion idealDivisors, ∑ k ∈ rows,
            if R ∈ idealDivisors k then
              ‖hybridDivisorTerm Pset nset bset a beta k R‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK rows Pset nset bset a beta hrows
  have hrewrite : (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) =
      ∑ k ∈ rows, ‖∑ R ∈ idealDivisors k,
        (moebius R : ℂ) * hybridDivisorTerm Pset nset bset a beta k R‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hybridRow_mobius Pset nset bset a beta k (hrows k hk).1]
    rfl
  rw [hrewrite]
  apply finite_expansion_energy rows (rows.biUnion idealDivisors) idealDivisors
    (fun _ R => (moebius R : ℂ)) (hybridDivisorTerm Pset nset bset a beta) (C * K ^ ε)
  · intro k hk R hR
    exact Finset.mem_biUnion.mpr ⟨k, hk, hR⟩
  · intro k hk R hR
    exact QuadraticInitialBound.norm_ideal_moebius_le_one R
  · intro k hk
    exact (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 hε.le) hC.le)

def doubleMaskRow (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ p ∈ pairs, (if IsCoprime k (p.1 * p.2) then 1 else 0) * F k p.1 p.2

def doubleMaskDivisorTerm (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis)
    (D : Ideal Eis × Ideal Eis) : ℂ :=
  ∑ p ∈ pairs, if D.1 ∣ p.1 ∧ D.2 ∣ p.2 then F k p.1 p.2 else 0

theorem doubleMaskRow_mobius (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) (hk : k ≠ 0) :
    doubleMaskRow pairs F k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) * doubleMaskDivisorTerm pairs F k D := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold doubleMaskRow
  conv_lhs => simp only [hm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [doubleMaskDivisorTerm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : D.1 ∣ p.1 ∧ D.2 ∣ p.2 <;> simp [h]

theorem hybrid_double_mask_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖doubleMaskRow pairs F k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖doubleMaskDivisorTerm pairs F k D‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows pairs F hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) := doubleMaskRow_mobius pairs F k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (doubleMaskDivisorTerm pairs F) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end

end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkBounds -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

 theorem finite_primeSupport_card {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι) :
    (IdealMobiusDivisorSum.primeSupport (Ideal.span {∏ i ∈ U, p i})).card = U.card := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i : U => Ideal.span {p i.val})) := by
    intro i j hij
    exact hcop (fun he => hij (Subtype.ext he))
  have he := Fintype.card_congr (productPrimeIndexEquiv (fun i : U => p i.val) hc)
  simpa only [Finset.prod_coe_sort, PrimeIndex, Fintype.card_coe, CompletedGauss.primeSupport, IdealMobiusDivisorSum.primeSupport] using he.symm

theorem finite_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ U : Finset ι,
      ‖primeMark slots lists a U‖ ≤ C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  exact (primeMark_norm_le_divisor_count slots lists a U hslots ha).trans hh

theorem finite_primeMark_extracted_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ A U : Finset ι,
      ‖primeMark slots lists a (A ∪ U)‖ ≤ (2:ℝ)^A.card * C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  calc
    _ ≤ (2:ℝ)^(A ∪ U).card := primeMark_norm_le_divisor_count _ _ _ _ hslots ha
    _ ≤ (2:ℝ)^(A.card+U.card) := pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = (2:ℝ)^A.card * (2:ℝ)^U.card := pow_add _ _ _
    _ ≤ (2:ℝ)^A.card * (C * (primeProductNorm p U)^ε) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end

