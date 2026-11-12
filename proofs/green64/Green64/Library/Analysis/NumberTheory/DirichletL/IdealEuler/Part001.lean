module

public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part005
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part001
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / IdealEuler / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.IdealEuler -/

section

namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem weighted_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => weighted a s I) :=
  (weighted_summable_norm a ha s hs).of_norm

theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)

theorem series_eq_LSeries (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = LSeries (ShortDraftHeckeBridge.normFiberCoeff a) s :=
  SmoothMobiusCorrection.idealDirichlet_eq_LSeries a ha s hs

theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

theorem series_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : series a s ≠ 0 := by
  intro hz
  have h := inverseSeries_mul_series a ha s hs
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem primeValueHom_eq (f : Ideal O →*₀ ℂ) : CanonicalRowCompletion.primeValueHom f = f := by
  ext I
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  · change (if I = 0 then 0 else ((normalizedFactors I).map f).prod) = f I
    simp only [hI, ite_false]
    rw [← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

def deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) : Ideal O →*₀ ℂ :=
  CanonicalRowCompletion.primeValueHom
    (fun I => if I ∈ S.image Subtype.val then 0 else a I)

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [ite_eq_left ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

theorem series_ofResidue_source_mask (M K : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ K)] (χ : MulChar (O ⧸ M) ℂ) (φ : MulChar (O ⧸ K) ℂ)
    (hχ : IdealCharacter.UnitInvariant M χ) (hφ : IdealCharacter.UnitInvariant K φ)
    (hmask : ∀ x : O, χ (Ideal.Quotient.mk M x) =
      if IsUnit (Ideal.Quotient.mk M x) then φ (Ideal.Quotient.mk K x) else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series (IdealCharacter.ofResidue M χ hχ) s =
      series (IdealCharacter.ofResidue K φ hφ) s *
        ∏ P ∈ SmoothMobiusCorrection.primeSet M,
          (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) :=
  series_of_coprime_mask M hM _ _ (IdealCharacter.norm_ofResidue_le_one K φ hφ)
    (IdealCharacter.ofResidue_source_mask M K χ φ hχ hφ hmask) s hs

theorem exists_primitive_series_associate (M : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ M)] (χ : MulChar (O ⧸ M) ℂ) (hχ : IdealCharacter.UnitInvariant M χ) :
    ∃ (K : Ideal O) (φ : MulChar (O ⧸ K) ℂ) (hφ : IdealCharacter.UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ FiniteFourier.IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ (s : ℂ), 1 < s.re →
        series (IdealCharacter.ofResidue M χ hχ) s =
          series (IdealCharacter.ofResidue K φ hφ) s *
            ∏ P ∈ SmoothMobiusCorrection.primeSet M,
              (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) := by
  obtain ⟨K, φ, hφ, hMK, hK, hp, hn, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate M χ hχ
  let : Finite (O ⧸ K) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hMK)
  refine ⟨K, φ, hφ, hMK, hK, hp, hn, ?_⟩
  intro s hs
  exact series_of_coprime_mask M hM _ _
    (IdealCharacter.norm_ofResidue_le_one K φ hφ) hmask s hs

end

end SevenEighths.IdealEuler

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.Boundary -/

section

namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (SmoothMobiusCorrection.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem norm_residue_series_product_ge_one (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series (ofResidue M 1 (one_unitInvariant M)) (x : ℂ) ^ 3 *
      series (ofResidue M χ hχ) (x + I * y) ^ 4 *
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) (x + 2 * I * y)‖ :=
  norm_series_product_ge_one _ _ _
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ) hx y

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, ite_eq_right one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, ite_eq_right (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ ShortDraftHeckeBridge.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, ite_eq_right hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold ShortDraftHeckeBridge.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [SmoothMobiusCorrection.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

theorem fullIdealZeta_eq_dirichlet_product (s : ℂ) (hs : 1 < s.re) :
    CubicEisenstein.fullIdealZeta s = riemannZeta s *
      (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s := by
  let a := normWeight 0
  have ha (I : Ideal O) : ‖a I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hseries : series a s = CubicEisenstein.fullIdealZeta s := by
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hinverse : inverseSeries a s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))) s := by
    rw [← ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
      (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff (1 : DirichletCharacter ℂ 1)) s]
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one (1 : DirichletCharacter ℂ 1)) s hs]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight,
        ShortDraftHeckeBridge.baseChangeWeight, hI, hchar]
  have hi := inverseSeries_mul_series a ha s hs
  have hp := ShortDraftHeckeBridge.pair_inverse_euler_identity
    (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)) s hs
  rw [← hinverse, DirichletCharacter.LFunction_modOne_eq] at hp
  rw [← hseries]
  calc
    series a s = 1 * series a s := (one_mul _).symm
    _ = ((riemannZeta s *
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s) *
          inverseSeries a s) * series a s := by rw [hp]
    _ = _ := by rw [mul_assoc, hi, mul_one]

def regularizedIdealZeta (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1 s *
    (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).mul
    (DirichletCharacter.differentiable_LFunction
      (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
        (1 : DirichletCharacter ℂ 1) rfl))

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * CubicEisenstein.fullIdealZeta s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq, fullIdealZeta_eq_dirichlet_product s hs,
    mul_assoc]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at hz
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne (by norm_num : (-2 : ℝ) ≠ (1 : ℂ)),
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  simp only [ofReal_neg, ofReal_ofNat, hz, mul_zero, zero_mul]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.EulerLog -/

section

namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set Metric Filter Complex ActualEisensteinCubic
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)

namespace SevenEighths.HeckeEulerLog

def eulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' P : PrimeIdeal, -Complex.log (1 - weighted a s P.val)

def majorant (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  have h := (SmoothMobiusCorrection.prime_norm_series_summable (σ - 1)
    (by linarith)).mul_left (3 / 2)
  convert h using 1
  ext P
  unfold majorant
  congr 2
  ring

theorem weighted_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖weighted a s P.val‖ ≤ (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ ≤ _
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ ≤ _
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  have hn : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val from
      (by have := SmoothMobiusCorrection.prime_norm_two_le P; omega))
  exact (mul_le_of_le_one_left (by positivity) (ha _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))

theorem weighted_norm_le_half (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} (hs : 1 ≤ s.re) : ‖weighted a s P.val‖ ≤ 1 / 2 := by
  refine (weighted_norm_le a ha P hs).trans ?_
  rw [Real.rpow_neg_one]
  have hn : (2 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; exact hn)

theorem log_factor_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant σ P := by
  have hhalf := weighted_norm_le_half a ha P (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self
    (z := -weighted a s P.val) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (weighted_norm_le a ha P hs) (by norm_num))

theorem weighted_differentiable (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    Differentiable ℂ (fun s ↦ weighted a s P.val) := by
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_pos P).ne'
  change Differentiable ℂ (fun s ↦ a P.val * CubicEisenstein.fullIdealWeight s P.val)
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - weighted a s P.val)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn := prime_norm_lt_one a ha s (by linarith : 0 < s.re) P
  have hslit : 1 - weighted a s P.val ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -weighted a s P.val) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (weighted_differentiable a P s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro P
    exact (log_factor_differentiableOn a ha P).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro P s hs
    exact log_factor_norm_le a ha P hσ.le hs.le

theorem eulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane a ha hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Complex.exp (eulerLog a s) = series a s :=
  SevenEighths.HeckeBoundary.exp_log_euler_eq_series a ha s hs

def eulerLogBound : ℝ := 1 + ∑' P : PrimeIdeal, majorant (3 / 2) P

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P :=
    tsum_nonneg (fun P ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hb : ∀ P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant (3 / 2) P :=
    fun P ↦ log_factor_norm_le a ha P (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun P : PrimeIdeal ↦ ‖-Complex.log (1 - weighted a s P.val)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog a s‖ ≤ ∑' P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

theorem eulerLog_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) (series a)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog_eq_series a ha s (hsub hs)
  · intro s hs
    exact eulerLog_norm_le a ha (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s = series a s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) L (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  obtain ⟨hd, he, hb⟩ := eulerLog_inner_disk a ha t
  refine ⟨hd, ?_, hb⟩
  intro s hs
  have hr := inner_disk_re (ball_subset_closedBall hs)
  exact (he hs).trans (hL s (by linarith)).symm

def principalLog (s : ℂ) : ℂ := Complex.log (1 - 2 / (s + 1))

theorem norm_two_div_add_one_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖(2 : ℂ) / (s + 1)‖ < 1 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_lt_one hn).mpr (by linarith)

theorem norm_two_div_add_one_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖(2 : ℂ) / (s + 1)‖ ≤ 4 / 5 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ hn).mpr (by linarith)

theorem principalLog_differentiableOn :
    DifferentiableOn ℂ principalLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hnorm := norm_two_div_add_one_lt_one hs
  have hslit : 1 - (2 : ℂ) / (s + 1) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, neg_div] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(2 : ℂ) / (s + 1)) (by simpa using hnorm)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).div
      (differentiableAt_id.add_const 1) hs1))).differentiableWithinAt

theorem exp_principalLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalLog s) = (s - 1) / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [principalLog, Complex.exp_log (SmoothMobiusCorrection.one_sub_ne_zero
    (norm_two_div_add_one_lt_one hs))]
  field_simp
  ring

theorem principalLog_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalLog s‖ ≤ 3 := by
  have hb := norm_two_div_add_one_le hs
  have hlt : ‖-(2 : ℂ) / (s + 1)‖ < 1 := by simpa using hb.trans_lt (by norm_num : (4 : ℝ) / 5 < 1)
  have h := Complex.norm_log_one_add_le hlt
  have hn : ‖-(2 : ℂ) / (s + 1)‖ = ‖(2 : ℂ) / (s + 1)‖ := by simp
  rw [hn] at h
  have heq : 1 + -(2 : ℂ) / (s + 1) = 1 - 2 / (s + 1) := by ring
  rw [heq] at h
  change ‖principalLog s‖ ≤ _ at h
  have hden : 0 < 1 - ‖(2 : ℂ) / (s + 1)‖ := by linarith
  have hinv : (1 - ‖(2 : ℂ) / (s + 1)‖)⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hnorm := norm_nonneg ((2 : ℂ) / (s + 1))
  have hsq : ‖(2 : ℂ) / (s + 1)‖ ^ 2 ≤ 16 / 25 := by nlinarith
  have hmul := mul_le_mul hsq hinv (inv_nonneg.mpr hden.le) (by norm_num : (0 : ℝ) ≤ 16 / 25)
  nlinarith

def principalEulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := principalLog s + eulerLog a s

theorem principalEulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (principalEulerLog a) {s : ℂ | 1 < s.re} :=
  principalLog_differentiableOn.add (eulerLog_differentiableOn a ha)

theorem exp_principalEulerLog (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalEulerLog a s) = ((s - 1) / (s + 1)) * series a s := by
  rw [principalEulerLog, Complex.exp_add, exp_principalLog hs, exp_eulerLog_eq_series a ha s hs]

theorem principalEulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound :=
  (norm_add_le _ _).trans (add_le_add (principalLog_norm_le hs) (eulerLog_norm_le a ha hs))

theorem principal_continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) (t : ℝ) :
    DifferentiableOn ℂ (principalEulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ principalEulerLog a) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(principalEulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact (exp_principalEulerLog a ha (hsub hs)).trans (hL s (hsub hs)).symm
  · intro s hs
    exact principalEulerLog_norm_le a ha
      (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem residue_continued_inner_disk (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog (ofResidue M χ hχ))
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog (ofResidue M χ hχ)) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog (ofResidue M χ hχ) s‖ ≤ eulerLogBound :=
  continued_inner_disk _ (norm_ofResidue_le_one M χ hχ) L hL t

theorem continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e eulerLogBound M / (2 * e)) * Real.log C) := by
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he'
    eulerLogBound_ge_one hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := continued_inner_disk a ha L hEq t
  exact hbound b C L (eulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

theorem principal_continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e (3 + eulerLogBound) M / (2 * e)) * Real.log C) := by
  have hA : 1 ≤ 3 + eulerLogBound := by linarith [eulerLogBound_ge_one]
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := principal_continued_inner_disk a ha L hEq t
  exact hbound b C L (principalEulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

end SevenEighths.HeckeEulerLog

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.CanonicalReferenceThreshold -/

section

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap ContDiff

namespace SevenEighths.InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvzero⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (R / eta)) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self Alog, abs_nonneg hi, abs_nonneg window]
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self window, abs_nonneg hi, abs_nonneg Alog]

theorem canonical_reference_pool_coverage (hi B Z N L D : ℝ)
    (hB : 0 ≤ B) (hhi : hi ≤ B) (hZ : 1 ≤ Z) (hNL : N ≤ L)
    (hD : B * Z ^ L ≤ D) : hi * Z ^ N ≤ D := by
  calc
    hi * Z ^ N ≤ B * Z ^ N :=
      mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg (by linarith) _)
    _ ≤ B * Z ^ L :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hNL) hB
    _ ≤ D := hD

theorem exists_canonical_reference_family_gates {ι : Type*} (s : Finset ι)
    (hi Alog window : ι → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 < B ∧ ∃ Z0 : ℝ, 1 < Z0 ∧
      (∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧ Real.exp (window i) ≤ B) ∧
      ∀ Z : ℝ, Z0 ≤ Z →
        2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
        1 ≤ eta * Real.log Z ∧ B ≤ Z ^ eta ∧
        (∀ i ∈ s, hi i ≤ Z ^ eta ∧ Real.exp (Alog i) ≤ Z ^ eta ∧
          Real.exp (window i) ≤ Z ^ eta) ∧
        (∀ i ∈ s, ∀ N L D : ℝ, N ≤ L → B * Z ^ L ≤ D → hi i * Z ^ N ≤ D) := by
  let mass : ι → ℝ := fun i => |hi i| + Real.exp (Alog i) + Real.exp (window i)
  have hm : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  let B : ℝ := 1 + ∑ i ∈ s, mass i
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧
      Real.exp (window i) ≤ B := by
    intro i hiS
    have hsum : mass i ≤ ∑ j ∈ s, mass j := Finset.single_le_sum (fun j _ => hm j) hiS
    dsimp [mass, B] at *
    constructor
    · linarith [le_abs_self (hi i), Real.exp_pos (Alog i), Real.exp_pos (window i)]
    constructor
    · linarith [abs_nonneg (hi i), Real.exp_pos (window i)]
    · linarith [abs_nonneg (hi i), Real.exp_pos (Alog i)]
  obtain ⟨Z0, hZ0, hgate⟩ := eventually_canonical_reference_gates B 0 0 eta heta
  refine ⟨B, hB, Z0, hZ0, hbound, ?_⟩
  intro Z hZ
  obtain ⟨hZtwo, htwo, hexp, hlog, hBpow, _, _⟩ := hgate Z hZ
  refine ⟨hZtwo, htwo, hexp, hlog, hBpow, ?_, ?_⟩
  · intro i hiS
    obtain ⟨hhi, hA, hw⟩ := hbound i hiS
    exact ⟨hhi.trans hBpow, hA.trans hBpow, hw.trans hBpow⟩
  · intro i hiS N L D hNL hD
    exact canonical_reference_pool_coverage (hi i) B Z N L D hB.le
      (hbound i hiS).1 (by linarith) hNL hD

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialFibers -/

section

namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → SmoothMobiusCorrection.PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryGenerator x.divisor ≠ 0
  row_eq : primaryGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

theorem Valid.of_reconstruction {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O)
    (hf : primaryGenerator f ≠ 0) (hC : t*x.divisor = x.common)
    (hlabel : x.divisor*x.residual = f)
    (hrow : primaryGenerator x.divisor*x.frequency = k)
    (hslots : ∀ i, (x.assigned i).val ∣ t*f) : Valid x t f k := by
  refine ⟨hC, hlabel, ?_, hrow, hslots⟩
  intro hz
  apply hf
  rw [← hlabel, primaryGenerator_mul, hz, zero_mul]

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma valid_label_squarefree {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hC : Squarefree x.common) (hs : Squarefree x.residual)
    (hmask : IsCoprime x.residual x.common) : Squarefree f := by
  have hdC : x.divisor ∣ x.common := by rw [← hx.common_eq]; exact dvd_mul_left _ _
  have hds : IsCoprime x.divisor x.residual := (hmask.of_isCoprime_of_dvd_right hdC).symm
  rw [← hx.label_eq]
  exact squarefree_mul_iff.mpr ⟨hds.isRelPrime, hC.squarefree_of_dvd hdC, hs⟩

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

theorem valid_tuple_card_le_slot_cap {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) (K : ℕ) (hJ : J ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) := by
  apply (valid_tuple_card_le_separated T t f k ht hf hT).trans
  exact Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos t ht) hJ)

theorem valid_tuple_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (InitialTuple J)) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 → (∀ x ∈ T, Valid x t f k) →
      (T.card : ℝ) ≤ C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  have hJr : 0 < (J+1 : ℝ) := by positivity
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power
    (ε/(J+1)) (div_pos hε hJr)
  refine ⟨C^(J+1), by positivity, ?_⟩
  intro T t f k ht hf hT
  have htf : t*f ≠ 0 := mul_ne_zero ht hf
  have hsub : idealDivisors f ⊆ idealDivisors (t*f) := by
    intro D hD
    exact (mem_idealDivisors htf).mpr
      (((mem_idealDivisors hf).mp hD).trans (dvd_mul_left _ _))
  have hcard : T.card ≤ (idealDivisors (t*f)).card^(J+1) := by
    apply (valid_tuple_card_le T t f k ht hf hT).trans
    calc
      _ ≤ (idealDivisors (t*f)).card * (idealDivisors (t*f)).card^J :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = _ := by rw [pow_succ]; ring
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors (t*f)).card : ℝ))
    (hb (t*f) htf) (J+1)
  apply (show (T.card : ℝ) ≤ ((idealDivisors (t*f)).card : ℝ)^(J+1) by
    exact_mod_cast hcard).trans (hh.trans_eq ?_)
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), map_mul, Nat.cast_mul]
  congr 1
  push_cast
  field_simp

def initialFiber {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O) : Finset (InitialTuple J) :=
  source.filter (fun x => Valid x t f k ∧ (∀ i, x.assigned i ∈ lists i) ∧ keep x)

theorem initialFiber_card_le {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(J+1) * (idealDivisors t).card^J :=
  valid_tuple_card_le_separated _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_card_le_slot_cap {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (K : ℕ) (hJ : J ≤ 2*K) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1) K hJ

theorem initialFiber_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (source : Finset (InitialTuple J))
      (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
      (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 →
      ((initialFiber source lists keep t f k).card : ℝ) ≤
        C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  obtain ⟨C, hC, hbound⟩ := valid_tuple_small_power J ε hε
  refine ⟨C, hC, ?_⟩
  intro source lists keep t f k ht hf
  exact hbound _ t f k ht hf (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_weight_bound {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (w : InitialTuple J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ initialFiber source lists keep t f k, ‖w x‖ ≤ C) :
    (∑ x ∈ initialFiber source lists keep t f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(J+1) * ((idealDivisors t).card : ℝ)^J := by
  calc
    _ ≤ ∑ _x ∈ initialFiber source lists keep t f k, C :=
      Finset.sum_le_sum hw
    _ = ((initialFiber source lists keep t f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(J+1) * (idealDivisors t).card^J : ℕ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast initialFiber_card_le source lists keep t f k ht hf) hC
    _ = _ := by push_cast; ring

end
end SevenEighths.InverseInitialFibers

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.InitializationEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev InitialChild := Ideal Eis × Ideal Eis × Eis

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (idealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : idealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, idealQuotient_mul hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ idealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp [he])
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal Eis) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (hsource x hxs)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 : c.1 ≠ 0 := he ▸ (initialChild_nonzero x (hsource x hx)).1
    exact initialChild_fiber_weight source hsource c ht0
      (hlabels c.2.1 (Finset.mem_product.mp hfk).1) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

def initialPositiveEnergy {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) : ℝ :=
  ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
    ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
      ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2

theorem initialPositiveEnergy_nonneg {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) :
    0 ≤ initialPositiveEnergy source labels rows F := by
  unfold initialPositiveEnergy
  positivity

theorem initial_weighted_count {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      Real.sqrt (initialPositiveEnergy source labels rows F) *
        Real.sqrt (initialPositiveEnergy source labels rows G) := by
  have hF := initial_energy_projection source hsource labels rows hlabels hchild w hw1 F
  have hG := initial_energy_projection source hsource labels rows hlabels hchild w hw1 G
  apply (weighted_cauchy source w (F ∘ initialChild) (G ∘ initialChild) hw0).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem initial_weighted_count_normalized {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) (H : ℝ) (hH : 0 < H) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      H * (Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows F) *
        Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows G)) := by
  apply (initial_weighted_count source hsource labels rows hlabels hchild w hw0 hw1 F G).trans_eq
  rw [Real.sqrt_mul (inv_nonneg.mpr hH.le), Real.sqrt_mul (inv_nonneg.mpr hH.le)]
  have hc : H * (Real.sqrt H⁻¹) ^ 2 = 1 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hH.le), mul_inv_cancel₀ hH.ne']
  calc
    _ = (H * (Real.sqrt H⁻¹) ^ 2) *
        (Real.sqrt (initialPositiveEnergy source labels rows F) *
          Real.sqrt (initialPositiveEnergy source labels rows G)) := by rw [hc, one_mul]
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

def initialColumn (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i∈S,p i) *
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (j*C) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S d) *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S h * H S

theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      secondPreColumn p hp hcop hg Ψ (j*C) 1 1 d h H S := by
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]

theorem initial_common_extraction (hpr : ∀ i,λ₀^2∣p i-1)
    (Ψ : O →* ℂ) (j t d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    initialColumn p hp hcop hg Ψ j (d*t) d h H (V∪N) =
      initialColumn p hp hcop hg Ψ j (d*t) d h (fun _=>1) V *
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H (V∪U)) N := by
  simp only [initialColumn_eq_secondPre]
  simpa only [one_mul] using secondPreColumn_union p hp hcop hg hpr Ψ j t 1 1 d h H V N hVN

theorem initial_marked_child (F V A : Finset ι) (Ψ : O →* ℂ) (j t d h : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ j t 1 1 d h slots lists a W X

theorem initial_input_row (F : Finset ι) (Ψ : O →* ℂ) (j : O)
    (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p hg F Ψ j 1 1 H z =
      FirstCauchyArithmetic.supportConjugateSum (fun i=>Ideal.span {p i}) hg F
        (fun S=>Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S j*H S) z := by
  unfold inputConjugateRow
  congr 1
  funext S
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [secondInputCoefficient,hone,one_pow,mul_one]

def sourceIdeal (S : Finset ι) : Ideal O := Ideal.span {∏ i∈S,p i}

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_gen (hpr : ∀ i,λ₀^2∣p i-1) (S : Finset ι) :
    primaryGenerator (sourceIdeal p S)=∏ i∈S,p i := by
  apply primaryGenerator_span _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have he : p i*(∏ j∈S,p j)-1=(p i-1)*(∏ j∈S,p j)+((∏ j∈S,p j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (hpr i) _) ih

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

def sourcePrime (i : ι) : SmoothMobiusCorrection.PrimeIdeal :=
  ⟨Ideal.span {p i},Ideal.prime_of_isPrime (NeZero.ne _) inferInstance⟩

def sourceTuple {J : ℕ} (G E V : Finset ι) (h : O) (assigned : Fin J→ι) : InitialTuple J :=
  ⟨sourceIdeal p G,sourceIdeal p E,sourceIdeal p V,h,fun i=>sourcePrime p (assigned i)⟩

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

include hp in

theorem sourceTuple_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι)
    (hEG : E⊆G) (ha : ∀ i,assigned i∈G∪V) :
    InitialSourceValid (sourceTuple p G E V h assigned) := by
  refine ⟨sourceIdeal_ne_zero p hp G,sourceIdeal_ne_zero p hp V,?_,
    sourceIdeal_dvd p E G hEG,?_⟩
  · change primaryGenerator (sourceIdeal p E)≠0
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  · intro i
    change (sourcePrime p (assigned i)).val∣sourceIdeal p G*sourceIdeal p V
    rcases Finset.mem_union.mp (ha i) with hi|hi
    · exact dvd_mul_of_dvd_left (source_prime_dvd p G (assigned i) hi) _
    · exact dvd_mul_of_dvd_right (source_prime_dvd p V (assigned i) hi) _

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem source_quotient (G E : Finset ι) (hEG : E⊆G) :
    CanonicalQuadraticSieve.idealQuotient (sourceIdeal p E) (sourceIdeal p G)=
      sourceIdeal p (G\E) := by
  apply mul_left_cancel₀ (sourceIdeal_ne_zero p hp E)
  rw [CanonicalQuadraticSieve.idealQuotient_mul (sourceIdeal_dvd p E G hEG)]
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

include hp in

theorem source_child (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι) (hEG : E⊆G) :
    initialChild (sourceTuple p G E V h assigned)=
      (sourceIdeal p (G\E),sourceIdeal p E*sourceIdeal p V,(∏ i∈E,p i)*h) := by
  simp only [initialChild,sourceTuple,source_quotient p hp G E hEG,sourceIdeal_gen p hp hpr E]

theorem initial_pair_children
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (j t d h₁ h₂ : O) (H₁ H₂ : Finset ι→ℂ) :
    (∑ S∈F.powerset,∑ T∈F.powerset,if Disjoint S T then
      star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ H₁ S)*
        initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ H₂ T else 0) =
    ∑ V∈F.powerset,
      (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) V *
        star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ (fun _=>1) V)*
          initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ (fun _=>1) V) *
        star (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₁
          (j*t) (d*∏ i∈V,p i) (d*h₁) (fun U=>H₁ (V∪U)) N) *
        (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₂
          (j*t) (d*∏ i∈V,p i) (d*h₂) (fun U=>H₂ (V∪U)) N) := by
  simp only [initialColumn_eq_secondPre]
  simpa only [secondSeparatedPair,secondCommonWeight,secondChildSum,one_mul] using
    secondSeparatedPair_eq_children p hp hcop hg hinj hpr F Ψ₁ Ψ₂ j t 1 1 d h₁ h₂ H₁ H₂

theorem initial_scalar_self_pair
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (Ψ : O →* ℂ) (j C d h : O) (V : Finset ι)
    (hΨ : ‖Ψ (∏ i∈V,p i)‖=1) :
    star (initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V)*
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V =
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V d *
        rowCoprimeMask (fun i=>Ideal.span {p i}) V h := by
  have hcol := columnCoefficient_mul_star p hp hcop hg hc V
  have hphase : Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i))=1 := by
    rw [←starRingEnd_apply,Complex.mul_conj',hΨ]
    norm_num
  have hmask : star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C) := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V d
  have hh := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V h
  simp only [initialColumn,mul_one,star_mul,star_star]
  calc
    _ = (columnCoefficient p hp hcop hg V*star (columnCoefficient p hp hcop hg V))*
      (Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i)))*
      (star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h) := by ring
    _ = _ := by rw [hcol,hphase,hmask,hd,hh]; ring

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

@[ext] structure Source (J : ℕ) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  assigned : Fin J→ι

def toTuple {J : ℕ} (x : Source (ι:=ι) J) : InitialTuple J :=
  sourceTuple p x.common x.divisor x.overlap x.frequency x.assigned

theorem toTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) {J : ℕ} :
    Function.Injective (toTuple p (J:=J)) := by
  intro x y he
  have hC := congrArg InitialTuple.common he
  have hD := congrArg InitialTuple.divisor he
  have hV := congrArg InitialTuple.residual he
  have hf := congrArg InitialTuple.frequency he
  have ha := congrArg InitialTuple.assigned he
  apply Source.ext
  · exact sourceIdeal_injective p hinj hC
  · exact sourceIdeal_injective p hinj hD
  · exact sourceIdeal_injective p hinj hV
  · exact hf
  · funext i
    apply hinj
    exact congrArg Subtype.val (congrFun ha i)

def assignedTerm {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) : ℂ :=
  ∏ i, if assigned i∈lists i ∧ assigned i∈outer then a i (assigned i) else 0

theorem assignedTerm_source {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) (h : assignedTerm lists a outer assigned≠0) :
    ∀ i,assigned i∈lists i ∧ assigned i∈outer := by
  intro i
  have hn := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  by_contra hi
  simp only [hi,ite_false,ne_eq,not_true_eq_false] at hn

include hp in

theorem actual_source_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (x : Source (ι:=ι) J) (hdiv : x.divisor⊆x.common)
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hterm : assignedTerm lists a (x.common∪x.overlap) x.assigned≠0) :
    InitialSourceValid (toTuple p x) :=
  sourceTuple_valid p hp hpr x.common x.divisor x.overlap x.frequency x.assigned hdiv
    (fun i=>(assignedTerm_source lists a _ _ hterm i).2)

include hp in

theorem actual_source_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))
  let T := S.image (toTuple p)
  have hvalid : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have hv := initialChild_valid (toTuple p x)
      (actual_source_valid p hp hpr x (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using hv
  have hh := valid_tuple_card_le_separated T t f k ht hf hvalid
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (toTuple_injective p hinj)
  rw [hcard] at hh
  exact hh

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem poisson_generator_unit (hpr : ∀ i,λ₀^2∣p i-1) (E : Finset ι) :
    ∃ u : Oˣ, primeSubsetGenerator (fun i=>Ideal.span {p i}) E=
      (u : O)*primaryGenerator (sourceIdeal p E) := by
  have hg0 : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs : Ideal.span {primaryGenerator (sourceIdeal p E)}=
      Ideal.span {primeSubsetGenerator (fun i=>Ideal.span {p i}) E} := by
    rw [(primaryGenerator_spec _ hg0).1]
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,
      sourceIdeal,FiniteGaussPhase.span_finset_prod]
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

def sectorSource {J : ℕ} (u : Oˣ) (x : Source (ι:=ι) J) : Source (ι:=ι) J :=
  {x with frequency := (u : O)^5*x.frequency}

omit [DecidableEq ι] in
theorem sectorSource_injective {J : ℕ} (u : Oˣ) :
    Function.Injective (sectorSource (J:=J) (ι:=ι) u) := by
  intro x y he
  apply Source.ext
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.common) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.divisor) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.overlap) he
  · have hh := congrArg Source.frequency he
    exact mul_left_cancel₀ (pow_ne_zero 5 (Units.ne_zero u)) hh
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.assigned) he

include hp in

omit hp in
theorem sectorTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {J : ℕ} (u : Oˣ) :
    Function.Injective (fun x : Source (ι:=ι) J=>toTuple p (sectorSource u x)) :=
  (toTuple_injective p hinj).comp (sectorSource_injective u)

include hp in

theorem actual_sector_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ} (u : Oˣ)
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))
  let T := S.image (fun x=>toTuple p (sectorSource u x))
  have hv : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have he := initialChild_valid (toTuple p (sectorSource u x))
      (actual_source_valid p hp hpr (sectorSource u x) (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using he
  have hh := valid_tuple_card_le_separated T t f k ht hf hv
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (sectorTuple_injective p hinj u)
  rw [hcard] at hh
  exact hh

theorem initial_poisson_child_normalized
    (hpr : ∀ i,λ₀^2∣p i-1) (G E V : Finset ι) (Ψ : O →* ℂ)
    (j e t h : O) (he : Ideal.span {e}=sourceIdeal p E)
    (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Oˣ, e=(u:O)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (H : Finset ι→ℂ) (N : Finset ι),
        secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
          secondChildColumn p hp hcop hg Ψ
            (j*primaryGenerator (sourceIdeal p (G\E)))
            (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
            (primaryGenerator (sourceIdeal p E)*((u:O)^5*h)) H N := by
  have hgE : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) e he hgE
  refine ⟨u,hu,?_⟩
  intro H N
  have hts : Ideal.span {t}=Ideal.span {primaryGenerator (sourceIdeal p (G\E))} := by
    rw [ht,sourceIdeal_gen p hp hpr (G\E)]
    rfl
  have hmask := rowCoprimeMask_mul_eq_of_span_eq (fun i=>Ideal.span {p i}) N j hts
  have hchange : secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
      secondChildColumn p hp hcop hg Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (e*∏ i∈V,p i) (e*h) H N := by
    simp only [secondChildColumn,hmask]
  rw [hchange,hu,primaryGenerator_mul,sourceIdeal_gen p hp hpr V]
  rw [mul_assoc (u:O)]
  exact secondChildColumn_generator_unit p hp hcop hg Ψ u _ _ _ h H N

end SevenEighths.InverseInitialArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlap -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

abbrev O := ActualEisensteinCubic.O

def residual (P j : Ideal O) : Ideal O := idealQuotient j P

def column (P j n : Ideal O) : Ideal O := idealQuotient j n * residual P j

def reconstruct (P j c : Ideal O) : Ideal O := j * idealQuotient (residual P j) c

def original (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  S.filter fun n => Squarefree n ∧ gcd n P = j

def columns (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  (original S P j).image (column P j)

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

def overlapEquiv (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) : original S P j ≃ columns S P j where
  toFun n := ⟨column P j n, Finset.mem_image.mpr ⟨n, n.property, rfl⟩⟩
  invFun c := ⟨reconstruct P j c, by
    obtain ⟨hc, hcj, hPc, hnS⟩ := (mem_columns hP hj).mp c.property
    exact mem_original.mpr ⟨hnS, reconstruct_properties hP hj hc hcj hPc⟩⟩
  left_inv n := Subtype.ext (reconstruct_column hP hj (mem_original.mp n.property).2.2)
  right_inv c := Subtype.ext (column_reconstruct hP hj
    ((mem_columns hP hj).mp c.property).2.2.1)

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem columns_filter (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (mask : Ideal O → Prop) [DecidablePred mask] :
    columns (S.filter mask) P j =
      (columns S P j).filter fun c => mask (reconstruct P j c) := by
  ext c
  simp only [mem_columns hP hj, Finset.mem_filter]
  tauto

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ S.filter Squarefree,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ∑ j ∈ idealDivisors P,
      ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
            ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_fixed_overlap S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

theorem overlap_coefficient_norm_le {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (ψ : Ideal O →* ℂ) (hψ : ‖ψ j‖ ≤ 1) :
    ‖(moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2‖ ≤ 1 := by
  have hjSF := hP.squarefree_of_dvd hj
  have hresSF := residual_squarefree hP hj
  simpa [norm_mul, hjSF.moebius_eq, hresSF.moebius_eq] using
    InverseMoment.overlap_scalar_norm_le hψ

end SevenEighths.InverseInitialOverlap

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialExcludedSource -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedSource
open InverseInitialOverlap
local notation "O"=>ActualEisensteinCubic.O

def columns (S:Finset (Ideal O))(P j:Ideal O):Finset (Ideal O):=
  (original S P j).image (idealQuotient j)

theorem quotient_properties {P j n:Ideal O}(hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩

theorem reconstruct_properties {P j c:Ideal O}(hP:Squarefree P)(hj:j∣P)
    (hc:Squarefree c)(hcp:IsCoprime c P):
    Squarefree (j*c) ∧ gcd (j*c) P=j := by
  exact ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩

theorem mem_columns {S:Finset (Ideal O)}{P j c:Ideal O}
    (hP:Squarefree P)(hj:j∣P):
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    obtain ⟨hcs,hcp,he⟩:=quotient_properties hns hng
    exact ⟨hcs,hcp,he.symm ▸ hnS⟩
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)

theorem sum_reconstruct (S:Finset (Ideal O)){P j:Ideal O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]

theorem cutoff_argument (j c:Ideal O)(X:ℝ):
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

theorem coefficient_identity (ψ:Ideal O→*ℂ){P j c:Ideal O}
    (hj:j∣P)(hcp:IsCoprime c P):
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring

theorem polynomial_slice (S:Finset (Ideal O)){P j:Ideal O}
    (hP:Squarefree P)(hj:j∣P)(ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring

theorem polynomial_decomposition (S:Finset (Ideal O)){P:Ideal O}(hP:Squarefree P)
    (ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [ite_eq_left hs]
    · simp only [ite_eq_right hs,moebius_of_not_squarefree hs,Int.cast_zero,zero_mul]
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

end SevenEighths.InverseInitialExcludedSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def density (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ℂ := (𝓕 g) t*logPhase t xj

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,logPhase_norm,mul_one]

theorem density_moment (g : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀xj,
      Integrable (fun t:ℝ=>(1+‖t‖)^J*‖density g xj t‖) ∧
      (∫t:ℝ,(1+‖t‖)^J*‖density g xj t‖)≤C := by
  refine ⟨∫t:ℝ,(1+‖t‖)^J*‖(𝓕 g) t‖,integral_nonneg (fun t=>by positivity),?_⟩
  intro xj
  simp only [density_norm]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J,le_rfl⟩

lemma phase_neg (t x : ℝ) : logPhase (-t) x=logPhase t (-x) := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma phase_sub (t xj xc y : ℝ) :
    logPhase t xj*logPhase t xc*logPhase (-t) y=logPhase t (xj+xc-y) := by
  rw [phase_neg,←logPhase_add,←logPhase_add]
  rfl

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

theorem tuple_mark_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMark_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*logPhase t xj*logPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*logPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_logPhase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem overlap_mode_integrable (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A) := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1
  funext t
  rw [←phase_sub]
  ring

theorem actual_overlap_separation
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        logPhase t (Real.log yc)*
        primeMark I L (fun i p=>a i p*logPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp only [CubicReflectionKernel.logSchwartz_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property)
    ((Finset.mem_pi.mp hp) i.val i.property))).symm

end SevenEighths.InverseInitialOverlapFourier

end

end OAI

end

