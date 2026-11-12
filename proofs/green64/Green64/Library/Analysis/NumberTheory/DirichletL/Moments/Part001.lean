module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.Basic -/

section

namespace OAI

open scoped BigOperators NNReal
namespace SevenEighths.CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def ofResidueMask {S : Type*} [CommRing S] (ρ : M →* R)
    (χ : MulChar R ℂ) (puncture : M →* S) : MaskedCharacter M R where
  residue := ρ
  character := χ
  keep a := IsUnit (puncture a)
  keep_mul a b := by
    rw [map_mul]
    exact (Commute.all _ _).isUnit_mul_iff

@[simp] theorem ofResidueMask_keep_one {S : Type*} [CommRing S]
    (ρ : M →* R) (χ : MulChar R ℂ) (puncture : M →* S) :
    (ofResidueMask ρ χ puncture).keep 1 := by
  change IsUnit (puncture 1)
  simp only [map_one, isUnit_one]

def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0

@[simp] theorem MaskedCharacter.value_mul (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all

def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)

@[simp] theorem normTwist_mul (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by
  simp only [normTwist, map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (N a).coe_nonneg (N b).coe_nonneg _

def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a

@[simp] theorem coefficient_mul (d : MaskedCharacter M R) (N : M →* ℝ≥0)
    (t : ℝ) (a b : M) :
    coefficient d N t (a * b) = coefficient d N t a * coefficient d N t b := by
  simp only [coefficient, MaskedCharacter.value_mul, normTwist_mul]
  ring

def plainSum (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s : Finset M) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ a ∈ s, coefficient d N t a * W ((N a : ℝ) / X)

def rectangle (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂) -
    W₁ ((N a : ℝ) / Y₁) * W₂ ((N b : ℝ) / Y₂)

theorem rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by
  simp only [plainSum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [coefficient_mul, rectangle]
  ring

theorem slot_rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (p : M) (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (p * (a * b)) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      coefficient d N t p *
        (plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
          plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂) := by
  rw [← rectangle_sum_eq]
  simp only [coefficient_mul, Finset.mul_sum, mul_assoc]

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

theorem volume_products_eq (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  calc
    _ = c ^ 2 * I₁ * I₂ *
      ((X₁ : ℂ) ^ (1 + Complex.I * t) * (X₂ : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [hpow]; ring

theorem centered_error_identity (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    A₁ * A₂ - B₁ * B₂ =
      (A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) -
        (B₁ - b₁) * B₂ - b₁ * (B₂ - b₂) := by
  linear_combination hmain

theorem norm_centered_le (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [norm_mul]

theorem norm_centered_le_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith

theorem scale_le_product_div {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX

theorem sum_scales_le {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  have a := scale_le_product_div (le_trans hL.le hX₁) hL hX₂ hprodX
  have b := scale_le_product_div (le_trans hL.le hX₂) hL hX₁
    (by simpa only [mul_comm] using hprodX)
  have c := scale_le_product_div (le_trans hL.le hY₁) hL hY₂ hprodY
  have d := scale_le_product_div (le_trans hL.le hY₂) hL hY₁
    (by simpa only [mul_comm] using hprodY)
  linarith

theorem centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring

theorem extracted_volume_phase (X D t : ℝ) (hX : 0 ≤ X) (hD : 0 < D) :
    (D : ℂ) ^ (Complex.I * t) * ((X / D : ℝ) : ℂ) ^ (1 + Complex.I * t) =
      (X : ℂ) ^ (1 + Complex.I * t) / (D : ℂ) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hp : (D : ℂ) ^ (Complex.I * t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hX hD.le,
    Complex.cpow_add _ _ hDc, Complex.cpow_one]
  field_simp

theorem extracted_volume_sum {D : Type*} (s : Finset D) (a : D → ℂ)
    (norm : D → ℝ) (hnorm : ∀ d ∈ s, 0 < norm d)
    (c I : ℂ) (t X : ℝ) (hX : 0 ≤ X) :
    (∑ d ∈ s, a d * (norm d : ℂ) ^ (Complex.I * t) *
      volumeTerm c I t (X / norm d)) =
      volumeTerm (c * ∑ d ∈ s, a d / (norm d : ℂ)) I t X := by
  unfold volumeTerm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := extracted_volume_phase X (norm d) t hX (hnorm d hd)
  calc
    _ = a d * c * I * ((norm d : ℂ) ^ (Complex.I * t) *
        ((X / norm d : ℝ) : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [h]; ring

theorem centered_volume_fallback (A₁ A₂ B₁ B₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T C : ℝ)
    (hA₁ : ‖A₁‖ ≤ C * X₁) (hA₂ : ‖A₂‖ ≤ C * X₂)
    (hB₁ : ‖B₁‖ ≤ C * Y₁) (hB₂ : ‖B₂‖ ≤ C * Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 2 * C ^ 2 * T := by
  have hA := mul_le_mul hA₁ hA₂ (norm_nonneg A₂) ((norm_nonneg A₁).trans hA₁)
  have hB := mul_le_mul hB₁ hB₂ (norm_nonneg B₂) ((norm_nonneg B₁).trans hB₁)
  have h := norm_sub_le (A₁ * A₂) (B₁ * B₂)
  rw [norm_mul, norm_mul] at h
  have heX : C * X₁ * (C * X₂) = C ^ 2 * T := by rw [← hprodX]; ring
  have heY : C * Y₁ * (C * Y₂) = C ^ 2 * T := by rw [← hprodY]; ring
  rw [heX] at hA
  rw [heY] at hB
  linarith

theorem normalized_centered_saving (D : ℂ) (T L C E : ℝ)
    (hT : 0 < T) (hbound : ‖D‖ ≤ 4 * E * C * (T / L)) :
    ‖(Real.sqrt T : ℂ)⁻¹ * D‖ ≤ 4 * E * C * (Real.sqrt T / L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (4 * E * C * (T / L)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)
    _ = 4 * E * C * ((T / Real.sqrt T) / L) := by ring
    _ = _ := by
      have hdiv : T / Real.sqrt T = Real.sqrt T :=
        (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt hT.le).symm
      rw [hdiv]

end
end SevenEighths.CenteredMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Correlation -/

section

namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)

def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0

omit [Fintype R] in
theorem fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]

theorem fullCorrelation_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by
  classical
  simp only [fourierSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h : R) (x : X) (y : Y) :
      (f x * ψ (h * left x) * (star (ψ (h * right y)) * star (g y))) * ψ (-(h * j)) =
        (f x * star (g y)) * ψ (h * (left x - right y - j)) := by
    have hs : star (ψ (h * right y)) = ψ (-(h * right y)) := by
      simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj ψ (h * right y)).symm
    rw [hs]
    calc
      _ = (f x * star (g y)) *
          (ψ (h * left x) * ψ (-(h * right y)) * ψ (-(h * j))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hphase, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [fullCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : left x - right y = j
  · simp [hxy, mul_comm]
  · simp [sub_ne_zero.mpr hxy, hxy]

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))

lemma character_mul_star (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ (χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))

theorem shiftCorrelation_scale (χ : MulChar F ℂ) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = shiftCorrelation χ 1 := by
  unfold shiftCorrelation
  rw [← (Equiv.mulLeft₀ k hk).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.mulLeft₀_apply]
  rw [show k * x - k = k * (x - 1) by ring, map_mul, map_mul, star_mul]
  calc
    _ = (χ k * star (χ k)) * (χ x * star (χ (x - 1))) := by ring
    _ = _ := by rw [character_mul_star χ hk, one_mul]

theorem shiftCorrelation_one (χ : MulChar F ℂ) :
    shiftCorrelation χ 1 = χ⁻¹ (-1) * jacobiSum χ χ⁻¹ := by
  simp only [shiftCorrelation, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.star_apply', show x - 1 = (-1) * (1 - x) by ring, map_mul]
  ring

theorem shiftCorrelation_zero (χ : MulChar F ℂ) :
    shiftCorrelation χ 0 = (Fintype.card F : ℂ) - 1 := by
  classical
  simp only [shiftCorrelation, sub_zero, MulChar.star_apply', ← MulChar.mul_apply,
    mul_inv_cancel]
  rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
  simp

theorem shiftCorrelation_nonprincipal (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 := by
  rw [shiftCorrelation_scale χ hk, shiftCorrelation_one, jacobiSum_nontrivial_inv hχ,
    mul_neg, ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))]

theorem shiftCorrelation_principal {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  rw [shiftCorrelation_scale _ hk, shiftCorrelation_one, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)), one_mul, jacobiSum_one_one]

def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k

theorem localCorrelation_eq_shift (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) * shiftCorrelation χ (k / n₁) := by
  classical
  have hsolve (x y : F) : n₂ * x - n₁ * y = k ↔ y = (n₂ * x - k) / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  unfold localCorrelation fullCorrelation
  simp only [hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Equiv.mulLeft₀ (n₁ / n₂) (div_ne_zero h₁ h₂)).sum_comp]
  swap
  · simp
  simp only [Equiv.mulLeft₀_apply, shiftCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have heq : (n₂ * (n₁ / n₂ * x) - k) / n₁ = x - k / n₁ := by
    field_simp
  rw [heq, mul_assoc]

theorem localCorrelation_units (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) *
      (if k = 0 then (Fintype.card F : ℂ) - 1
       else if χ = 1 then (Fintype.card F : ℂ) - 2 else -1) := by
  rw [localCorrelation_eq_shift χ h₁ h₂]
  by_cases hk : k = 0
  · simp [hk, shiftCorrelation_zero]
  · by_cases hχ : χ = 1
    · simp [hk, hχ, shiftCorrelation_principal (div_ne_zero hk h₁)]
    · simp [hk, hχ, shiftCorrelation_nonprincipal χ hχ (div_ne_zero hk h₁)]

lemma character_sum (χ : MulChar F ℂ) :
    (∑ x : F, χ x) = if χ = 1 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
    simp
  · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]

theorem localCorrelation_first_zero (χ : MulChar F ℂ) {n₂ : F} (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ 0 n₂ k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (x : F) : n₂ * x = k ↔ x = k / n₂ := by
    rw [eq_div_iff h₂, mul_comm]
  have hsum : localCorrelation χ 0 n₂ k = χ (k / n₂) * star (∑ y : F, χ y) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, sub_zero, hsolve]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, ← star_sum]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
      simp [hk]
  · simp [hχ]

theorem localCorrelation_second_zero (χ : MulChar F ℂ) {n₁ : F} (h₁ : n₁ ≠ 0) (k : F) :
    localCorrelation χ n₁ 0 k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (y : F) : -(n₁ * y) = k ↔ y = -k / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  have hsum : localCorrelation χ n₁ 0 k = (∑ x : F, χ x) * star (χ (-k / n₁)) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, zero_sub, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
      simp [hk]
  · simp [hχ]

end FiniteField

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

theorem reductionMultiplicity_mul_card (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

theorem reductionMultiplicity_eq_pow (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]

theorem fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_reduction_unit_right (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))

theorem fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CRT -/

section

namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, heq]

theorem fullCorrelation_product (u v k : A × B) (f₁ g₁ : A → ℂ) (f₂ g₂ : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f₁ x.1 * f₂ x.2) (fun y => g₁ y.1 * g₂ y.2) k =
      fullCorrelation (fun x => v.1 * x) (fun y => u.1 * y) f₁ g₁ k.1 *
        fullCorrelation (fun x => v.2 * x) (fun y => u.2 * y) f₂ g₂ k.2 := by
  classical
  simp only [fullCorrelation, Fintype.sum_prod_type]
  have hterm (x₁ y₁ : A) (x₂ y₂ : B) :
      (if v * (x₁, x₂) - u * (y₁, y₂) = k
       then (f₁ x₁ * f₂ x₂) * star (g₁ y₁ * g₂ y₂) else 0) =
      (if v.1 * x₁ - u.1 * y₁ = k.1 then f₁ x₁ * star (g₁ y₁) else 0) *
      (if v.2 * x₂ - u.2 * y₂ = k.2 then f₂ x₂ * star (g₂ y₂) else 0) := by
    have heq : v * (x₁, x₂) - u * (y₁, y₂) = k ↔
        v.1 * x₁ - u.1 * y₁ = k.1 ∧ v.2 * x₂ - u.2 * y₂ = k.2 := by
      exact Prod.ext_iff
    by_cases h₁ : v.1 * x₁ - u.1 * y₁ = k.1 <;>
      by_cases h₂ : v.2 * x₂ - u.2 * y₂ = k.2 <;>
      simp [heq, h₁, h₂, star_mul] ; ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  rw [Finset.mul_sum]

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [ite_eq_right hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_idealCRT {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by
  classical
  dsimp only
  rw [fullCorrelation_ringEquiv (Ideal.quotientInfRingEquivPiQuotient I hI) u v k
    (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)), fullCorrelation_pi]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FullCorrelation -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)

@[simp] theorem scaledResidue_mk (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl

def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)

theorem scaledResidue_congruence (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton

theorem fullModulusCorrelation_fourier (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ h : A ⧸ Ideal.span {u * v},
      fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
          ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) * fullModulusCorrelation u v χu χv j :=
  fullCorrelation_fourier ψ hψ _ _ χu χv _

theorem common_divisor_frequency {u v d x y j : A}
    (hdu : d ∣ u) (hdv : d ∣ v) (hcong : u * v ∣ v * x - u * y - j) : d ∣ j := by
  have hleft : d ∣ v * x - u * y := dvd_sub (hdv.trans (dvd_mul_right v x))
    (hdu.trans (dvd_mul_right u y))
  have hprod : d ∣ u * v := hdu.trans (dvd_mul_right u v)
  have hdiff := dvd_sub hleft (hprod.trans hcong)
  convert hdiff using 1 ; ring

theorem fullModulusCorrelation_eq_zero_of_common_not_dvd (u v d j : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hdu : d ∣ u) (hdv : d ∣ v) (hdj : ¬d ∣ j) :
    fullModulusCorrelation u v χu χv j = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  have hn : ¬ scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j := by
    intro h
    exact hdj (common_divisor_frequency hdu hdv ((scaledResidue_congruence u v a b j).mp h))
  exact ite_eq_right hn

theorem dvd_of_unit_residue_mul {u x v : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x)) (hdiv : u ∣ v * x) : u ∣ v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hm : Ideal.Quotient.mk (Ideal.span {u}) v *
      Ideal.Quotient.mk (Ideal.span {u}) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact hx.mul_right_injective (by simpa only [mul_comm, mul_zero, zero_mul] using hm)

theorem zero_frequency_units_force_divides {u v x y : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) y))
    (hcong : u * v ∣ v * x - u * y) : u ∣ v ∧ v ∣ u := by
  have hu : u ∣ v * x := by
    have h := dvd_add ((dvd_mul_right u v).trans hcong) (dvd_mul_right u y)
    simpa only [sub_add_cancel] using h
  have hv : v ∣ u * y := by
    have h := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hcong)
    convert h using 1 ; ring
  exact ⟨dvd_of_unit_residue_mul hx hu, dvd_of_unit_residue_mul hy hv⟩

theorem fullModulusCorrelation_zero_frequency_off_diagonal (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hne : Ideal.span ({u} : Set A) ≠ Ideal.span ({v} : Set A)) :
    fullModulusCorrelation u v χu χv 0 = 0 := by
  classical
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  change (if scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) 0
    then χu (Ideal.Quotient.mk (Ideal.span {u}) a) *
      star (χv (Ideal.Quotient.mk (Ideal.span {v}) b)) else 0) = 0
  by_cases hx : χu (Ideal.Quotient.mk (Ideal.span {u}) a) = 0
  · simp only [hx, zero_mul, ite_self]
  by_cases hy : χv (Ideal.Quotient.mk (Ideal.span {v}) b) = 0
  · simp only [hy, star_zero, mul_zero, ite_self]
  split_ifs with h
  · exfalso
    have hd := (scaledResidue_congruence u v a b 0).mp h
    rw [sub_zero] at hd
    obtain ⟨huv, hvu⟩ := zero_frequency_units_force_divides
      (χu.apply_ne_zero_iff.mp hx) (χv.apply_ne_zero_iff.mp hy) hd
    apply hne
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr hvu
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr huv
  · rfl

variable [IsDomain A]

theorem scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd

theorem fullModulusCorrelation_zero_frequency_diagonal (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) :
    fullModulusCorrelation u u χ χ 0 =
      (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  classical
  have hinj := scaledResidue_injective u u (u * u) rfl hu
  unfold fullModulusCorrelation fullCorrelation
  have hcond (x y : A ⧸ Ideal.span {u}) :
      scaledResidue u u (u * u) rfl x -
        scaledResidue u u (u * u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u * u}) 0 ↔ y = x := by
    rw [map_zero, sub_eq_zero]
    exact hinj.eq_iff.trans eq_comm
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units

end SevenEighths.CenteredMomentCorrelation
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCommonParam -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}

def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)

abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}

def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t

def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t

omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _

def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩

lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=>p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl

lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh

lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _

def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩

@[simp] lemma solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCommonLinear -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCommonSum -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=>rfl)

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PrimePower -/

section

namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl

theorem primePower_localCorrelation_units (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      χ (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, localCorrelation_units _ hu hv,
    MulChar.pow_apply' _ (by omega), hcard, hpow, mul_assoc]
  split_ifs <;> rfl

theorem primePower_localCorrelation_second_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, hv, localCorrelation_second_zero _ hu, hcard, hpow]
  split_ifs <;> rfl

theorem primePower_localCorrelation_first_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hv : primePowerReduction P hc v ≠ 0 :=
    (isUnit_iff_ne_zero.mp (v.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  change (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) = _
  rw [hu, localCorrelation_first_zero _ hv, hcard, hpow]
  split_ifs <;> rfl

end Local
end
end SevenEighths.CenteredMomentCorrelation

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Parameters -/

section

namespace OAI

namespace SevenEighths.Parameters

theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

theorem exists_height_cutoff {dmin allowance A : ℝ}
    (hd : 0 < dmin) (ha : 0 < allowance) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < dmin / 100 ∧
      A * τ < dmin * allowance / 100 := by
  have hden : 0 < 200 * (1 + A) := by positivity
  let τ := min (dmin / 200) (dmin * allowance / (200 * (1 + A)))
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have h1 : τ ≤ dmin / 200 := min_le_left _ _
  have h2 : τ ≤ dmin * allowance / (200 * (1 + A)) := min_le_right _ _
  have h2' : τ * (200 * (1 + A)) ≤ dmin * allowance :=
    (le_div_iff₀ hden).mp h2
  refine ⟨τ, ht, by linarith, ?_⟩
  have hp : 0 < dmin * allowance := mul_pos hd ha
  nlinarith

theorem exists_tail_order {τ B saving : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, B - τ * N < -saving := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + saving) / τ)
  have h := (div_lt_iff₀ hτ).mp hN
  exact ⟨N, by nlinarith⟩

theorem cumulative_frequency_bound {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfreq : ∀ i ∈ s, |frequency i| ≤ T / (4 * s.card)) :
    |∑ i ∈ s, frequency i| ≤ T / 4 := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    simp only [he, Finset.sum_empty, abs_zero]
    positivity
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      |∑ i ∈ s, frequency i| ≤ ∑ i ∈ s, |frequency i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, T / (4 * s.card) := Finset.sum_le_sum hfreq
      _ = T / 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

end SevenEighths.Parameters

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ParametersSlotLengths -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0< mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0< rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤ mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0< rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ParametersDetectorScales -/

section

namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0< rmin) (hm : 0< mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε< rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤ rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith
end SevenEighths.Parameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ParametersCentralBudget -/

section

namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end SevenEighths.Parameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ParametersHighData -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0< rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε< rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

theorem exists_high_data (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ }⟩
  intro J hJ
  let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
  have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0≤τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
end SevenEighths.Parameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ParametersHighDataFine -/

section

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

theorem exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)(mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0<t→0< mesh t):
    ∃D:HighData Δ,∀j,D.ell j≤ mesh D.t/200:=by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring

theorem fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0< mesh D.t)(hfine:∀j,D.ell j≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ)≤d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d≤ mesh D.t:=by
  have hd0:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end SevenEighths.Parameters

end

end OAI

end

