module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.RetainedProfile -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

theorem dilated_normPowerProfile_uniform_degree (a b B : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, ∀ hc : 1 ≤ c, ∀ hcB : c ≤ B, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (normPowerProfile (dilated W c) (a / B) b
          (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
          (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
        C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := normPowerProfile_uniform_degree a b ha F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  refine ⟨B ^ (F.sup Prod.snd) * C, mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hB) _) hC, ?_⟩
  intro c hc hcB t
  have ht : (1 + ‖t / (2 * Real.pi)‖) ^ J ≤ (1 + ‖t‖) ^ J := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  calc
    _ ≤ B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) :=
      normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW t F
    _ ≤ B ^ (F.sup Prod.snd) * (C * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left
        ((hbound t).trans (mul_le_mul_of_nonneg_left ht hC.le)) (by positivity)
    _ = _ := by ring

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipDilation_eq_one (S : ℝ) (hS : 1 ≤ S) : clipDilation S = 1 := by
  simp [clipDilation, clippedScale, max_eq_right hS, ne_of_gt (lt_of_lt_of_le zero_lt_one hS)]

theorem clipDilation_subunit (S : ℝ) (hS : S ≤ 1) :
    clipDilation S = 1 / S := by simp [clipDilation, clippedScale, max_eq_left hS]

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    twistedIdealSum χ W t S =
      twistedIdealSum χ (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_twistedIdealSum_zero (χ : Character) (W : ℝ → ℂ)
    (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : twistedIdealSum χ W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t x : ℝ) :
    retainedProfile W a b ha hs hW S hS hret t x =
      (x : ℂ) ^ (Complex.I * t) * W (clipDilation S * x) :=
  normPowerProfile_apply _ _ _ _ _ _ _ _

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

theorem retainedProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W a b ha hs hW S hS hret t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := dilated_normPowerProfile_uniform_degree a b (max 1 b) ha (le_max_left _ _) F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  exact ⟨C, hC, fun S hS hret t =>
    hbound (clipDilation S) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) t⟩

theorem two_retainedProfile_uniform_degree (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ S₁ S₂ : ℝ, ∀ hS₁ : 0 < S₁, ∀ hS₂ : 0 < S₂,
      ∀ hret₁ : 1 ≤ S₁ * b₁, ∀ hret₂ : 1 ≤ S₂ * b₂, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ S₁ hS₁ hret₁ t) +
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ S₂ hS₂ hret₂ t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J₁, hJ₁⟩ := retainedProfile_uniform_degree a₁ b₁ ha₁ F
  obtain ⟨J₂, hJ₂⟩ := retainedProfile_uniform_degree a₂ b₂ ha₂ F
  refine ⟨max J₁ J₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C₁, hC₁, hb₁⟩ := hJ₁ W₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := hJ₂ W₂ hs₂ hW₂
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro S₁ S₂ hS₁ hS₂ hret₁ hret₂ t
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have h₁ := (hb₁ S₁ hS₁ hret₁ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left J₁ J₂)) hC₁.le)
  have h₂ := (hb₂ S₂ hS₂ hret₂ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right J₁ J₂)) hC₂.le)
  nlinarith

theorem retained_row_rectangle (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) =
      A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂)) := by
  rw [clipped_rowTwistedSum η m A₀ z W₁ t S₁ hS₁,
    clipped_rowTwistedSum η m A₀ z W₂ t S₂ hS₂]

theorem strict_subunit_row_rectangle_zero (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hstrict : S₁ * b₁ < 1 ∨ S₂ * b₂ < 1) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) = 0 := by
  rcases hstrict with h₁ | h₂
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₁ b₁ t S₁ hS₁ hs₁ h₁, zero_mul, mul_zero]
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₂ b₂ t S₂ hS₂ hs₂ h₂, mul_zero, mul_zero]

theorem two_retained_row_rectangles (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (A : ℂ) :
    ‖A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
      rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ≤
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ +
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ := by
  rw [mul_sub, retained_row_rectangle η m A₀ z W₁ W₂ t S₁ S₂ hS₁ hS₂ A,
    retained_row_rectangle η m A₀ z W₁ W₂ t T₁ T₂ hT₁ hT₂ A]
  exact norm_sub_le _ _

theorem two_retained_row_energies (η : Character) (m A₀ : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (rows : Finset O) (A : O → ℂ) (w : O → ℝ) (hw : ∀ z ∈ rows, 0 ≤ w z) :
    (∑ z ∈ rows, w z * ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2) ≤
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2) +
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hb := two_retained_row_rectangles η m A₀ z W₁ W₂ t S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm : ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2 ≤
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2 +
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ -
       ‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖)]
  convert mul_le_mul_of_nonneg_left hnorm (hw z hz) using 1; ring

theorem retained_volumeControl_le (Q : Ideal O) (χ : Character)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
      (max 1 b) ^ (pvSeminorms.sup Prod.snd) *
        volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  have h := normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation S)
    ha (le_max_left _ _) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs hW t pvSeminorms
  change pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (retainedProfile W a b ha hs hW S hS hret t) ≤ _ at h
  unfold volumeControl pvControl
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((IdealMobiusDivisorSum.idealDivisors χ.modulus).card : ℝ) *
      (Nat.card (O ⧸ Ideal.span {fixedPeriod Q}) : ℝ) * pvConstant from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) pvConstant_pos.le)
  convert hh using 1 <;> ring

theorem retained_volumeControl_uniform_degree (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := volumeControl_polynomial_height Q a b ε B ha hε hB
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  let D := (max 1 b) ^ (pvSeminorms.sup Prod.snd)
  have hD : 0 < D := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Z hZ χ hχ S hS hret t
  calc
    _ ≤ D * volumeControl Q χ (normPowerProfile W a b ha hs hW t) :=
      retained_volumeControl_le Q χ W a b ha hs hW S hS hret t
    _ ≤ D * (C * Z ^ ε * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left (hbound Z hZ χ hχ t) hD.le
    _ = _ := by ring

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalVolume -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeHeight
open CenteredMomentMask
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B → ∀ t : ℝ,
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * Z^ε * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha pvSeminorms
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  let A := D*mass*pvConstant*C
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hpv := pvConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1+A,by positivity,?_⟩
  intro W hs Z hZ χ hnorm t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
      (D*Z^ε)*(mass*(pvConstant*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg hpv.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _ ≤ _ := herr
    _ = A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A]; ring
    _ ≤ (1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem retained_volumeControl_source_control (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character,
      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      ∀ X : ℝ, ∀ hX : 0<X, ∀ hret : 1≤X*b, ∀ t : ℝ,
      volumeControl Q χ (CenteredMomentRetainedProfile.retainedProfile
        W a b ha hs (W.smooth ⊤) X hX hret t) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨n,S,hS,hbound⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨n,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩ := hbound Q
  refine ⟨(max 1 b)^(pvSeminorms.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs Z hZ χ hχ X hX hret t
  exact (CenteredMomentRetainedProfile.retained_volumeControl_le
    Q χ W a b ha hs (W.smooth ⊤) X hX hret t).trans
    ((mul_le_mul_of_nonneg_left (hCbound W hs Z hZ χ hχ t) (by positivity)).trans_eq (by ring))
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalUnit -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_unit (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁≤1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂≤1 →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hvol⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨D,hD,hDvol⟩ := hvol Q
  let V := 128*(b+b)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨1+8*D*V,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ hS₁ hS₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hbound₁ (y:ℝ) : ‖W₁ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₁)
  have hbound₂ (y:ℝ) : ‖W₂ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₂)
  have herr (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
      (hS':S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤1) :
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        D*Z^ε*(1+‖t‖)^J := by
    apply (hDvol W hs Z hZ χ hnorm t).trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS' hD.le) (Real.rpow_nonneg (by linarith) _))
        (show 0≤(1+‖t‖)^J by positivity)
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    W₁ W₂ a b a b 1 1 ha ha hb hb zero_le_one zero_le_one hs₁ hs₂
    (W₁.smooth ⊤) (W₂.smooth ⊤) hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hn := CenteredMoment.normalized_centered_saving _ T L V _ hT (by
    simpa only [mul_one] using hraw)
  have hE := add_le_add (herr W₁ hs₁ hS₁) (herr W₂ hs₂ hS₂)
  have hr : 0≤Real.sqrt T/L := div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _ ≤ _ := hn
    _ ≤ 4*(D*Z^ε*(1+‖t‖)^J+D*Z^ε*(1+‖t‖)^J)*V*(Real.sqrt T/L) := by
      gcongr
    _ = (8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by ring
    _ ≤ (1+8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
      gcongr
      linarith
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

theorem sourceControl_zero (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) (hW : sourceControl S W=0) : W=0 := by
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans_eq hW)

theorem normalizedProfile_control (S) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S (normalizedProfile S W)≤1 := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((sourceControl S W)⁻¹ • W)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (sourceControl_nonneg S W))]
  change (sourceControl S W)⁻¹*sourceControl S W≤1
  by_cases h : sourceControl S W=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem normalizedProfile_support (S) (W : 𝓢(ℝ,ℂ)) :
    Function.support (normalizedProfile S W:ℝ→ℂ)⊆Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [normalizedProfile,smul_apply,hw]

theorem normalizedProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S W • normalizedProfile S W=W := by
  by_cases h : sourceControl S W=0
  · rw [sourceControl_zero S hS W h]
    simp [sourceControl,normalizedProfile]
  · simp [normalizedProfile,smul_smul,h]

theorem twistedIdealSum_profile_smul (χ : Character) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : Character) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalRectangle -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_control (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hunit⟩ := rectangle_source_unit a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hunit Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound (normalizedProfile S W₁) (normalizedProfile S W₂)
    ((normalizedProfile_support S W₁).trans hs₁)
    ((normalizedProfile_support S W₂).trans hs₂)
    (normalizedProfile_control S W₁) (normalizedProfile_control S W₂)
    Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have heq : (Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
      twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂) =
      ((sourceControl S W₁*sourceControl S W₂:ℝ):ℂ)*
      ((Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ (normalizedProfile S W₁) t X₁*
        twistedIdealSum χ (normalizedProfile S W₂) t X₂-
        twistedIdealSum χ (normalizedProfile S W₁) t Y₁*
        twistedIdealSum χ (normalizedProfile S W₂) t Y₂)) := by
    rw [twistedIdealSum_normalized S hS χ W₁ t X₁,
      twistedIdealSum_normalized S hS χ W₂ t X₂,
      twistedIdealSum_normalized S hS χ W₁ t Y₁,
      twistedIdealSum_normalized S hS χ W₂ t Y₂]
    push_cast
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))]
  exact (mul_le_mul_of_nonneg_left h
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))).trans_eq (by ring)
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RetainedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

def retainedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  positiveSlotRow η m A z (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂))
    S β P t (clippedScale X₁) (clippedScale X₂)

omit [DecidableEq ι] in
theorem retained_rectangle_raw_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ T : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏ i,rowSlot η m A z (S i) (β i) t)‖^2 =
      (clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hp : 0 < ∏ i,P i := Finset.prod_pos (fun i _ => hP i)
  have hc₁ : 0 < clippedScale X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hc₂ : 0 < clippedScale X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  unfold retainedPositiveRow positiveSlotRow
  rw [normalized_norm_sq _ (mul_pos hT hp),normalized_norm_sq _ (mul_pos (mul_pos hc₁ hc₂) hp),
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  field_simp [hp.ne',hT.ne',hc₁.ne',hc₂.ne']

omit [DecidableEq ι] in
theorem centered_to_retained_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
      2*(clippedScale Y₁*clippedScale Y₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2 := by
  let F (U V : ℝ) : ℂ := (Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
    ((rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V)*
      ∏ i,rowSlot η m A z (S i) (β i) t)
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T=F X₁ X₂-F Y₁ Y₂ := by
    unfold centeredSlotRow F
    ring
  rw [he]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F X₁ X₂) (F Y₁ Y₂)) 2
  have hn : ‖F X₁ X₂-F Y₁ Y₂‖^2 ≤ 2*‖F X₁ X₂‖^2+2*‖F Y₁ Y₂‖^2 := by
    nlinarith [sq_nonneg (‖F X₁ X₂‖-‖F Y₁ Y₂‖)]
  have hx := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ T hX₁ hX₂ hT
  have hy := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t Y₁ Y₂ T hY₁ hY₂ hT
  change ‖F X₁ X₂‖^2=_ at hx
  change ‖F Y₁ Y₂‖^2=_ at hy
  rw [hx,hy] at hn
  convert hn using 1 ; ring

omit [DecidableEq ι] in
theorem centered_to_retained_weighted_energy (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T)
    (rows : Finset O) (ω : O → ℝ) (hω : ∀ z∈rows,0 ≤ ω z) :
    (∑ z∈rows,ω z*‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      2*(clippedScale X₁*clippedScale X₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2)+
      2*(clippedScale Y₁*clippedScale Y₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hh := mul_le_mul_of_nonneg_left
    (centered_to_retained_energy η m A z W₁ W₂ S β P hP t X₁ X₂ Y₁ Y₂ T
      hX₁ hX₂ hY₁ hY₂ hT) (hω z hz)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
theorem retained_rectangle_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      (max 1 b₁*max 1 b₂)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hB : 0 ≤ max 1 b₁*max 1 b₂ := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  by_cases h₁ : X₁*b₁ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h₁,zero_mul,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  by_cases h₂ : X₂*b₂ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h₂,mul_zero,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  have hr : clippedScale X₁*clippedScale X₂/(X₁*X₂) ≤ max 1 b₁*max 1 b₂ := by
    have h := mul_le_mul (clipDilation_le b₁ X₁ hX₁ (le_of_not_gt h₁))
      (clipDilation_le b₂ X₂ hX₂ (le_of_not_gt h₂))
      (zero_le_one.trans (clipDilation_ge_one _ hX₂)) (zero_le_one.trans (le_max_left _ _))
    simpa only [clipDilation,div_mul_div_comm] using h
  unfold positiveSlotRow
  rw [retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [DecidableEq ι] in
theorem centered_to_retained_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(max 1 b₁*max 1 b₂)*
        (‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
         ‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T =
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂-
      positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂ := by
    unfold centeredSlotRow positiveSlotRow
    rw [hX,hY]
    ring
  rw [he]
  have hx := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t X₁ X₂ hX₁ hX₂ hs₁ hs₂
  have hy := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t Y₁ Y₂ hY₁ hY₂ hs₁ hs₂
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
    (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    (positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂)) 2
  nlinarith [sq_nonneg (‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖-
    ‖positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂‖)]

end SevenEighths.CenteredMomentRetainedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorRetained -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

theorem masked_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := actual_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SlotRatios -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

theorem disjoint_frozen_ratio_bound (entrance old fresh : Finset ι)
    (hold : old ⊆ entrance) (hfresh : fresh ⊆ entrance) (hdis : Disjoint old fresh)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ old ∪ fresh,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |(∑ i ∈ old,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))+
      (∑ i ∈ fresh,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  rw [← Finset.sum_union hdis]
  exact frozen_subset_ratio_bound entrance (old ∪ fresh) (Finset.union_subset hold hfresh)
    W a b P v Z hZ ha hs hW

end SevenEighths.CenteredMomentSlotRatios

end

end OAI

end

