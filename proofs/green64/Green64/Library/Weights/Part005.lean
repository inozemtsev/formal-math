module

public import Green64.Library.Weights.IntegerPositionBlocks
public import Green64.Library.Weights.FiniteBlockHolder
public import Green64.Library.Correlation.PositionRootCompression
public import Green64.Library.Weights.ParityShiftTwoMask
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Weights / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LocalKernelPairing -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual complex matrix pairing in the physical-state Hilbert space,
with the original conjugation at the first endpoint. -/
theorem b652_matrix_pairing_sum434
    (K : Matrix α α ℂ) (f g : EuclideanSpace ℂ α) :
    inner ℂ f (K.toEuclideanLin g) =
      ∑ x : α, ∑ y : α, (starRingEnd ℂ) (f x)*K x y*g y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [starRingEnd_apply]
  ring

/-- Exact localization of one block pairing from the actual nonzero kernel
step condition. The second endpoint is arbitrary on its mark fibres. -/
theorem b652_local_block_kernel_pairing434
    (pos : α → ℤ) (H : ℤ) (hH : 1≤H) (K : Matrix α α ℂ)
    (hstep : ∀ x y, K x y≠0 → |pos y-pos x|≤H)
    (j : ℤ) (f g : EuclideanSpace ℂ α) :
    inner ℂ (b652PositionBlock434 pos H j f) (K.toEuclideanLin g) =
      inner ℂ (b652PositionBlock434 pos H j f)
        (K.toEuclideanLin (b652PositionNearBlock434 pos H j g)) := by
  rw [b652_matrix_pairing_sum434, b652_matrix_pairing_sum434]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : pos x/H=j
  · by_cases hy : |pos y/H-j|≤1
    · simp [b652PositionNearBlock434,hy]
    · have hz : K x y=0 := by
        by_contra hne
        have h := b652_integer_step_blocks434 (pos y) (pos x) H hH (hstep x y hne)
        exact hy (by simpa only [hx] using h)
      simp [hz]
  · simp [b652PositionBlock434,hx]

/-- Genuine finite position-block pairing decomposition. Blocks and their
three-block neighborhoods are constructed explicitly; no decomposition or
bounded-overlap hypothesis is supplied by the caller. -/
theorem b652_position_kernel_pairing_decomposition434
    (pos : α → ℤ) (H : ℤ) (hH : 1≤H) (K : Matrix α α ℂ)
    (hstep : ∀ x y, K x y≠0 → |pos y-pos x|≤H)
    (f g : EuclideanSpace ℂ α) :
    inner ℂ f (K.toEuclideanLin g) =
      ∑ j ∈ b652PositionBlocks434 pos H,
        inner ℂ (b652PositionBlock434 pos H j f)
          (K.toEuclideanLin (b652PositionNearBlock434 pos H j g)) := by
  calc
    _ = inner ℂ (∑ j ∈ b652PositionBlocks434 pos H, b652PositionBlock434 pos H j f)
        (K.toEuclideanLin g) := by rw [b652_position_blocks_sum434]
    _ = ∑ j ∈ b652PositionBlocks434 pos H,
        inner ℂ (b652PositionBlock434 pos H j f) (K.toEuclideanLin g) := by
      rw [sum_inner]
    _ = _ := Finset.sum_congr rfl fun j _ =>
      b652_local_block_kernel_pairing434 pos H hH K hstep j f g
end Green64Analytic.SpectralEndpoint

end

end

/-! ## LocalizedOperatorMoment -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The complete finite S02 localization/Hölder operator estimate, proved
from the actual matrix step condition. The original state Hilbert norms are
preserved, overlap costs exactly sqrt(3), and the moment is the literal
sum of block quadratic moments of (A A*)^R. No moment/RMS bound, abstract
partition, equal-norm root family, or terminal mark restriction is assumed. -/
theorem b652_localized_operator_moment434
    {α : Type*} [Fintype α] [DecidableEq α]
    (pos : α → ℤ) (H : ℤ) (hH : 1≤H) (K : Matrix α α ℂ)
    (hstep : ∀ x y, K x y≠0 → |pos y-pos x|≤H)
    (R : ℕ) (hR : 1≤R) (f g : EuclideanSpace ℂ α) :
    ‖inner ℂ f (K.toEuclideanLin g)‖ ≤
      Real.sqrt 3*‖g‖*‖f‖^(1-(R:ℝ)⁻¹) *
      (∑ j ∈ b652PositionBlocks434 pos H,
        (inner ℂ (b652PositionBlock434 pos H j f)
          (((K.toEuclideanLin.comp K.toEuclideanLin.adjoint)^R)
            (b652PositionBlock434 pos H j f))).re)^((2*(R:ℝ))⁻¹) := by
  let A := K.toEuclideanLin
  let J := b652PositionBlocks434 pos H
  let fj := fun j => b652PositionBlock434 pos H j f
  let gj := fun j => b652PositionNearBlock434 pos H j g
  let m := fun j => (inner ℂ (fj j) (((A.comp A.adjoint)^R) (fj j))).re
  let p : ℝ := 1-(R:ℝ)⁻¹
  let q : ℝ := (2*(R:ℝ))⁻¹
  change ‖inner ℂ f (A g)‖ ≤ Real.sqrt 3*‖g‖*‖f‖^p*(∑ j ∈ J, m j)^q
  have hm (j : ℤ) : 0 ≤ m j :=
    (b649_positive_power434 (A.comp A.adjoint) A.isPositive_self_comp_adjoint R).re_inner_nonneg_right (fj j)
  have hM : 0≤∑ j ∈ J, m j := Finset.sum_nonneg fun j _ => hm j
  have hF : (∑ j ∈ J, ‖fj j‖^2)=‖f‖^2 := b652_position_blocks_norm_sq434 pos H f
  have hG : (∑ j ∈ J, ‖gj j‖^2)≤3*‖g‖^2 := b652_near_blocks_norm_sq_le434 pos H J g
  have hG0 : 0≤∑ j ∈ J, ‖gj j‖^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have he := b652_position_kernel_pairing_decomposition434 pos H hH K hstep f g
  change inner ℂ f (A g)=∑ j ∈ J, inner ℂ (fj j) (A (gj j)) at he
  have hFp : (‖f‖^2 : ℝ)^(p/2)=‖f‖^p := by
    rw [← Real.rpow_natCast ‖f‖ 2, ← Real.rpow_mul (norm_nonneg f)]
    congr 1
    ring
  have hGp : (3*‖g‖^2 : ℝ)^((1:ℝ)/2)=Real.sqrt 3*‖g‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0:ℝ)≤3), Real.sqrt_sq (norm_nonneg g)]
  calc
    _ = ‖∑ j ∈ J, inner ℂ (fj j) (A (gj j))‖ := congrArg norm he
    _ ≤ ∑ j ∈ J, ‖inner ℂ (fj j) (A (gj j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖gj j‖*‖fj j‖^p*(m j)^q := by
      apply Finset.sum_le_sum
      intro j _
      exact b649_spectral_endpoint_pairing434 A R hR (fj j) (gj j)
    _ ≤ (∑ j ∈ J, ‖gj j‖^2)^((1:ℝ)/2) *
        (∑ j ∈ J, ‖fj j‖^2)^(p/2)*(∑ j ∈ J, m j)^q :=
      b652_finite_block_holder434 J (fun j => ‖gj j‖) (fun j => ‖fj j‖) m R hR
        (fun j _ => norm_nonneg _) (fun j _ => hm j)
    _ = (∑ j ∈ J, ‖gj j‖^2)^((1:ℝ)/2) *
        (‖f‖^2 : ℝ)^(p/2)*(∑ j ∈ J, m j)^q := by rw [hF]
    _ ≤ (3*‖g‖^2 : ℝ)^((1:ℝ)/2) *
        (‖f‖^2 : ℝ)^(p/2)*(∑ j ∈ J, m j)^q := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hM _)
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hG0 hG (by norm_num)) (Real.rpow_nonneg (sq_nonneg _) _)
    _ = _ := by rw [hFp,hGp]
end Green64Analytic.SpectralEndpoint

end

end

/-! ## MarkedPositionEndpoint -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The complete finite S02 endpoint estimate in the original physical
state norm. Only the FIRST endpoint is position-constant. Root vectors
are w times the full mark-fibre indicator and keep their unequal norms.
The second endpoint is arbitrary. The local factor is (H C²)^(1/(2R)),
with H counting integer positions, and the final factor is the literal
sum of ALL root moments of (A A*)^R. No RMS or root-moment estimate is
assumed, and no mark-size normalization or factor is introduced. -/
theorem b652_mark_independent_position_endpoint434
    {α : Type*} [Fintype α] [DecidableEq α]
    (pos : α → ℤ) (H : ℤ) (hH : 1≤H) (K : Matrix α α ℂ)
    (hstep : ∀ x y, K x y≠0 → |pos y-pos x|≤H)
    (R : ℕ) (hR : 1≤R) (w : ℂ) (I : Finset ℤ) (c : ℤ → ℂ)
    (C : ℝ) (hC : ∀ n∈I, ‖c n‖≤C) (g : EuclideanSpace ℂ α) :
    ‖inner ℂ (b652FirstPositionVector434 pos w I c) (K.toEuclideanLin g)‖ ≤
      Real.sqrt 3 * ‖g‖ * ‖b652FirstPositionVector434 pos w I c‖^(1-(R:ℝ)⁻¹) *
      ((H:ℝ)*C^2)^((2*(R:ℝ))⁻¹) *
      (∑ n ∈ I, (inner ℂ (b652PositionRoot434 pos w n)
        (((K.toEuclideanLin.comp K.toEuclideanLin.adjoint)^R)
          (b652PositionRoot434 pos w n))).re)^((2*(R:ℝ))⁻¹) := by
  let A := K.toEuclideanLin
  let f := b652FirstPositionVector434 pos w I c
  let d := fun n =>
    (inner ℂ (b652PositionRoot434 pos w n) (((A.comp A.adjoint)^R)
      (b652PositionRoot434 pos w n))).re
  let M : ℝ := (H:ℝ)*C^2
  let p : ℝ := 1-(R:ℝ)⁻¹
  let q : ℝ := (2*(R:ℝ))⁻¹
  have hpos := b649_positive_power434 (A.comp A.adjoint) A.isPositive_self_comp_adjoint R
  have hd (n : ℤ) : 0≤d n := hpos.re_inner_nonneg_right _
  have hD : 0≤∑ n ∈ I, d n := Finset.sum_nonneg fun n _ => hd n
  have hM : 0≤M := mul_nonneg (by exact_mod_cast (show 0≤H by omega)) (sq_nonneg C)
  have hlocal := b652_localized_operator_moment434 pos H hH K hstep R hR f g
  have hcompress := b652_position_root_block_moment434 pos w I c C hC H hH
    (A.comp A.adjoint) A.isPositive_self_comp_adjoint R
  have hquadratic : 0≤∑ j ∈ b652PositionBlocks434 pos H,
      (inner ℂ (b652PositionBlock434 pos H j f)
        (((A.comp A.adjoint)^R) (b652PositionBlock434 pos H j f))).re :=
    Finset.sum_nonneg fun j _ => hpos.re_inner_nonneg_right _
  have h : ‖inner ℂ f (A g)‖ ≤ Real.sqrt 3*‖g‖*‖f‖^p*(M*(∑ n ∈ I, d n))^q := by
    refine hlocal.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hquadratic hcompress ?_) ?_)
    · positivity
    · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (Real.rpow_nonneg (norm_nonneg _) _)
  change ‖inner ℂ f (A g)‖ ≤ Real.sqrt 3*‖g‖*‖f‖^p*M^q*(∑ n ∈ I, d n)^q
  calc
    _ ≤ Real.sqrt 3*‖g‖*‖f‖^p*(M*(∑ n ∈ I, d n))^q := h
    _ = _ := by rw [Real.mul_rpow hM hD]; ring
end Green64Analytic.SpectralEndpoint

end

end

/-! ## EndpointPowerBudget -/

section

open scoped BigOperators
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact cancellation of the long interval powers in the S02 endpoint.
In particular, the moment's X^(1/(2R)) is not discarded or bounded by a
local window. The remaining polynomial loss is at most L^(2C). -/
theorem b655_endpoint_power_budget434 (X L E C F G T : ℝ) (R : ℕ)
    (hX : 1 ≤ X) (hL : 1 ≤ L) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hF0 : 0 ≤ F) (hT0 : 0 ≤ T)
    (hF : F ≤ Real.sqrt X*L^C) (hG : G ≤ Real.sqrt X*L^C)
    (hT : T ≤ X*L^(-E*(2*(R:ℝ)))) :
    G*F^(1-(R:ℝ)⁻¹)*T^((2*(R:ℝ))⁻¹) ≤ X*L^(-E+2*C) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hRp : 0 < (R:ℝ) := zero_lt_one.trans_le hRr
  have hRne : (R:ℝ)≠0 := ne_of_gt hRp
  have hinv : (R:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hRr
  have hp : 0 ≤ 1-(R:ℝ)⁻¹ := by linarith
  have hq : 0 ≤ (2*(R:ℝ))⁻¹ := by positivity
  have hb0 : 0 ≤ Real.sqrt X*L^C := by positivity
  have hbound : G*F^(1-(R:ℝ)⁻¹)*T^((2*(R:ℝ))⁻¹) ≤
      (Real.sqrt X*L^C)*(Real.sqrt X*L^C)^(1-(R:ℝ)⁻¹)*
        (X*L^(-E*(2*(R:ℝ))))^((2*(R:ℝ))⁻¹) := by
    apply mul_le_mul
      (mul_le_mul hG (Real.rpow_le_rpow hF0 hF hp)
        (Real.rpow_nonneg hF0 _) hb0)
      (Real.rpow_le_rpow hT0 hT hq)
      (Real.rpow_nonneg hT0 _) (mul_nonneg hb0 (Real.rpow_nonneg hb0 _))
  have hXeq : Real.sqrt X*(Real.sqrt X)^(1-(R:ℝ)⁻¹)*X^((2*(R:ℝ))⁻¹)=X := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hXp.le,←Real.rpow_add hXp,←Real.rpow_add hXp]
    have he : (1/2:ℝ)+(1/2)*(1-(R:ℝ)⁻¹)+(2*(R:ℝ))⁻¹=1 := by
      field_simp
      ring
    rw [he,Real.rpow_one]
  have hLeq : L^C*(L^C)^(1-(R:ℝ)⁻¹)*
      (L^(-E*(2*(R:ℝ))))^((2*(R:ℝ))⁻¹) =
      L^(-E+C*(2-(R:ℝ)⁻¹)) := by
    rw [←Real.rpow_mul hLp.le,←Real.rpow_mul hLp.le,
      ←Real.rpow_add hLp,←Real.rpow_add hLp]
    congr 1
    field_simp
    ring
  have he : -E+C*(2-(R:ℝ)⁻¹) ≤ -E+2*C := by
    have hi : 0 ≤ (R:ℝ)⁻¹ := inv_nonneg.mpr hRp.le
    nlinarith [mul_nonneg hC hi]
  calc
    _ ≤ (Real.sqrt X*L^C)*(Real.sqrt X*L^C)^(1-(R:ℝ)⁻¹)*
        (X*L^(-E*(2*(R:ℝ))))^((2*(R:ℝ))⁻¹) := hbound
    _ = (Real.sqrt X*(Real.sqrt X)^(1-(R:ℝ)⁻¹)*X^((2*(R:ℝ))⁻¹))*
        (L^C*(L^C)^(1-(R:ℝ)⁻¹)*(L^(-E*(2*(R:ℝ))))^((2*(R:ℝ))⁻¹)) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.rpow_nonneg hLp.le _),
        Real.mul_rpow hXp.le (Real.rpow_nonneg hLp.le _)]
      ring
    _ = X*L^(-E+C*(2-(R:ℝ)⁻¹)) := by rw [hXeq,hLeq]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he) hXp.le
end Green64Analytic.SpectralEndpoint

end

end

/-! ## ShiftTwoMaskMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Original Parity (2.6) specialized to h=-2, a=1, b=2, R=2.
The original residue set T_{|k|,2} is retained unchanged and Fourier
normalization uses the TRUE totient of Q=2*|k|. -/
def parityShiftTwoMaskCoefficient434 (d : ℕ)
    (chi : DirichletCharacter ℂ (2*d)) : ℂ :=
  (∑ r ∈ b625ParityShiftTwoResidues434 d,
    star (chi (r : ZMod (2*d)))) / ((2*d).totient : ℂ)

/-- At k≠0 every character coefficient has its true original
1/φ(2|k|) normalization bound: odd |k| has the empty mask, even |k|
consists of exactly one residue, not two. -/
theorem parity_shift_two_mask_coefficient_bound434
    (d : ℕ) (hd : 0 < d)
    (chi : DirichletCharacter ℂ (2*d)) :
    ‖parityShiftTwoMaskCoefficient434 d chi‖ ≤
      ((2*d).totient : ℝ)⁻¹ := by
  have htot : 0 < (2*d).totient := Nat.totient_pos.mpr (by omega)
  by_cases he : Even d
  · have hset : b625ParityShiftTwoResidues434 d = {d+1} := by
      ext r
      rw [b625_parity_shift_two_residue_classification434 d r hd]
      simp [he]
    have hchi : ‖chi ((d+1 : ℕ) : ZMod (2*d))‖ ≤ 1 :=
      DirichletCharacter.norm_le_one chi _
    calc
      _ = ‖chi ((d+1 : ℕ) : ZMod (2*d))‖ * ((2*d).totient : ℝ)⁻¹ := by
        simp [parityShiftTwoMaskCoefficient434, hset, norm_div, div_eq_mul_inv]
      _ ≤ 1 * ((2*d).totient : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hchi (by positivity)
      _ = _ := one_mul _
  · have hset : b625ParityShiftTwoResidues434 d = ∅ := by
      ext r
      rw [b625_parity_shift_two_residue_classification434 d r hd]
      simp [he]
    simp [parityShiftTwoMaskCoefficient434, hset]

/-- STRONGER than Parity (2.7), which only uses mass ≤R=2:
for h=-2 the full original character Fourier coefficient ℓ1 mass is ≤1,
uniformly for any nonzero signed k and all characters modulo 2|k|.
This assumes no discrepancy or roughness and is a finite-group fact. -/
theorem parity_shift_two_mask_coefficient_mass_le_one434
    (d : ℕ) (hd : 0 < d) :
    (∑ chi : DirichletCharacter ℂ (2*d),
      ‖parityShiftTwoMaskCoefficient434 d chi‖) ≤ 1 := by
  letI : NeZero (2*d) := ⟨by omega⟩
  have htot : 0 < (2*d).totient := Nat.totient_pos.mpr (by omega)
  have hcard : Fintype.card (DirichletCharacter ℂ (2*d)) =
      (2*d).totient := by
    simpa only [Nat.card_eq_fintype_card] using
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (2*d))
  calc
    _ ≤ ∑ _chi : DirichletCharacter ℂ (2*d),
        ((2*d).totient : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact parity_shift_two_mask_coefficient_bound434 d hd chi
    _ = (Fintype.card (DirichletCharacter ℂ (2*d)) : ℝ) *
        ((2*d).totient : ℝ)⁻¹ := by simp [nsmul_eq_mul]
    _ = 1 := by
      rw [hcard]
      have hreal : ((2*d).totient : ℝ) ≠ 0 := by exact_mod_cast htot.ne'
      exact mul_inv_cancel₀ hreal

/-- True signed shift version; the Type-II mask modulus is exactly 2*|k|. -/
theorem parity_signed_shift_two_mask_coefficient_mass_le_one434
    (k : ℤ) (hk : k ≠ 0) :
    (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) ≤ 1 :=
  parity_shift_two_mask_coefficient_mass_le_one434 k.natAbs
    (Int.natAbs_pos.mpr hk)

/-- An odd nonzero signed k has NO admissible original Parity h=-2
mask residues. This is the true (m,mprime)-unit obstruction, not a
cancellation bound obtained by discarding the source odd-e condition. -/
theorem parity_signed_shift_two_odd_coefficient_zero434
    (k : ℤ) (hk : k ≠ 0) (hodd : Odd k)
    (chi : DirichletCharacter ℂ (2*k.natAbs)) :
    parityShiftTwoMaskCoefficient434 k.natAbs chi = 0 := by
  have hne : ¬ Even k := by
    intro he
    rcases he with ⟨u, hu⟩
    rcases hodd with ⟨v, hv⟩
    omega
  have hres := b625_parity_signed_shift_residue_set434 k hk
  rw [if_neg hne] at hres
  simp [parityShiftTwoMaskCoefficient434, hres]

/-- Hence all character coefficients vanish for odd signed k. -/
theorem parity_signed_shift_two_odd_mask_mass_zero434
    (k : ℤ) (hk : k ≠ 0) (hodd : Odd k) :
    (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) = 0 := by
  simp [parity_signed_shift_two_odd_coefficient_zero434 k hk hodd]
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoMaskOrthogonality -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- For the original unit residues, complex conjugation of a Dirichlet
character equals evaluation at the multiplicative inverse. This permits
Parity's original star(chi r) coefficients to use true character orthogonality. -/
theorem parity_shift_two_character_conjugate_unit434
    (d : ℕ) (chi : DirichletCharacter ℂ (2*d))
    (a : ZMod (2*d)) (ha : IsUnit a) :
    star (chi a) = chi a⁻¹ := by
  have hnorm : ‖chi a‖ = 1 := by
    simpa using (chi.unit_norm_eq_one ha.unit)
  have hprod : chi a * star (chi a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hnorm]
    norm_num
  have hinv : a⁻¹ * a = 1 := (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl
  have hinv2 : a * a⁻¹ = 1 := by simpa only [mul_comm] using hinv
  have hchar : chi a * chi a⁻¹ = 1 := by
    calc
      _ = chi (a*a⁻¹) := (map_mul chi a a⁻¹).symm
      _ = 1 := by rw [hinv2, map_one]
  exact (inv_eq_of_mul_eq_one_right hprod).symm.trans
    (inv_eq_of_mul_eq_one_right hchar)

/-- Every original Parity T_{d,2} residue is a genuine unit modulo Q=2d.
This is not inferred from parity alone: the complete coprimality gate
from the original residue definition is retained. -/
theorem parity_shift_two_mask_residue_unit434
    (d r : ℕ) (hr : r ∈ b625ParityShiftTwoResidues434 d) :
    IsUnit (r : ZMod (2*d)) := by
  have hcop : r.Coprime (2*d) :=
    (Finset.mem_filter.mp hr).2.1
  exact (ZMod.isUnit_iff_coprime r (2*d)).mpr hcop

/-- EXACT original Parity (2.6) character Fourier expansion on the unit
ratio class b=m'*m^{-1}. The coefficient is the original cχ with
complex conjugation and denominator totient(Q), not a surrogate; the
mask is the literal admissible T_{d,2} unit and odd-quotient set.
No input discrepancy, external correlation theorem or source saving. -/
theorem parity_shift_two_mask_original_fourier_expansion434
    (d : ℕ) (hd : 0 < d) (b : ZMod (2*d)) :
    (∑ chi : DirichletCharacter ℂ (2*d),
      parityShiftTwoMaskCoefficient434 d chi * chi b) =
        if b.val ∈ b625ParityShiftTwoResidues434 d then 1 else 0 := by
  letI : NeZero (2*d) := ⟨by omega⟩
  have htot : 0 < (2*d).totient := Nat.totient_pos.mpr (by omega)
  have htotC : ((2*d).totient : ℂ) ≠ 0 := by exact_mod_cast htot.ne'
  let T : Finset ℕ := b625ParityShiftTwoResidues434 d
  have hterm (chi : DirichletCharacter ℂ (2*d)) :
      parityShiftTwoMaskCoefficient434 d chi * chi b =
      ∑ r ∈ T, (chi ((r : ZMod (2*d))⁻¹) * chi b) / ((2*d).totient : ℂ) := by
    calc
      _ = ∑ r ∈ T, (star (chi (r : ZMod (2*d))) * chi b) / ((2*d).totient : ℂ) := by
        simp only [parityShiftTwoMaskCoefficient434, T, Finset.sum_div, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [parity_shift_two_character_conjugate_unit434 d chi _
          (parity_shift_two_mask_residue_unit434 d r hr)]
  have hcoeff :
      (∑ chi : DirichletCharacter ℂ (2*d),
         parityShiftTwoMaskCoefficient434 d chi * chi b) =
      ∑ r ∈ T, (if ((r : ZMod (2*d)) = b) then (1 : ℂ) else 0) := by
    calc
      _ = ∑ chi : DirichletCharacter ℂ (2*d),
            ∑ r ∈ T, (chi ((r : ZMod (2*d))⁻¹) * chi b) / ((2*d).totient : ℂ) := by
              apply Finset.sum_congr rfl
              intro chi hchi
              exact hterm chi
      _ = ∑ r ∈ T, ∑ chi : DirichletCharacter ℂ (2*d),
            (chi ((r : ZMod (2*d))⁻¹) * chi b) / ((2*d).totient : ℂ) := by
              rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
          (parity_shift_two_mask_residue_unit434 d r hr) b
        rw [← Finset.sum_div, horth]
        split_ifs <;> simp [htotC]
  rw [hcoeff]
  have hiff (r : ℕ) (hr : r ∈ T) :
      ((r : ZMod (2*d)) = b) ↔ r = b.val := by
    have hrange : r < 2*d := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hval : (r : ZMod (2*d)).val = r :=
      ZMod.val_natCast_of_lt hrange
    constructor
    · intro h; exact hval.symm.trans (congrArg ZMod.val h)
    · intro h
      rw [h]
      exact ZMod.natCast_zmod_val b
  calc
    _ = ∑ r ∈ T, (if r = b.val then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hc : ((r : ZMod (2*d)) = b)
      · have hnat : r = b.val := (hiff r hr).mp hc
        simp [hc, hnat]
      · have hnat : r ≠ b.val := by
          intro hh
          exact hc ((hiff r hr).mpr hh)
        simp [hc, hnat]
    _ = if b.val ∈ T then (1 : ℂ) else 0 := by simp
    _ = _ := rfl

/-- Literal original Parity (2.6) on the two physical rough cofactors:
the admissible ratio m' * m^{-1} is exactly the sum of characters
cχ χ(m') star χ(m). Only the original unit hypothesis on m is needed
for the inverse ratio; no E theorem or analytic cancellation assumed. -/
theorem parity_shift_two_mask_original_pair_fourier_expansion434
    (d : ℕ) (hd : 0 < d)
    (m mp : ZMod (2*d)) (hm : IsUnit m) :
    (if (mp*m⁻¹).val ∈ b625ParityShiftTwoResidues434 d then
      (1 : ℂ) else 0) =
      ∑ chi : DirichletCharacter ℂ (2*d),
        parityShiftTwoMaskCoefficient434 d chi * chi mp * star (chi m) := by
  have h := parity_shift_two_mask_original_fourier_expansion434 d hd (mp*m⁻¹)
  calc
    _ = ∑ chi : DirichletCharacter ℂ (2*d),
          parityShiftTwoMaskCoefficient434 d chi * chi (mp*m⁻¹) := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [map_mul, ← parity_shift_two_character_conjugate_unit434 d chi m hm]
      ring
/-- The literal original Parity (2.6) specialized to the signed actual h=-2
shift, valid for either positive or negative nonzero k. The original
ratio is mp/m modulo 2*abs(k), with m a unit as in the source's inverse
parametrization, and every coefficient is its exact totient Fourier term. -/
theorem parity_signed_shift_two_original_pair_fourier_expansion434
    (k : ℤ) (hk : k ≠ 0)
    (m mp : ZMod (2*k.natAbs)) (hm : IsUnit m) :
    (if (mp*m⁻¹).val ∈ b625ParityShiftTwoResidues434 k.natAbs then
      (1 : ℂ) else 0) =
      ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * chi mp * star (chi m) :=
  parity_shift_two_mask_original_pair_fourier_expansion434 k.natAbs
    (Int.natAbs_pos.mpr hk) m mp hm

/-- For odd signed k the literal admissible ratio mask is identically
zero, even before any character expansion or coefficient cancellation. -/
theorem parity_signed_shift_two_original_odd_ratio_zero434
    (k : ℤ) (hk : k ≠ 0) (hodd : Odd k)
    (m mp : ZMod (2*k.natAbs)) (hm : IsUnit m) :
    (if (mp*m⁻¹).val ∈ b625ParityShiftTwoResidues434 k.natAbs then
      (1 : ℂ) else 0) = 0 := by
  have he : ¬Even k := by
    intro h
    rcases hodd with ⟨v,hv⟩
    rcases h with ⟨u,hu⟩
    omega
  rw [parity_signed_shift_two_original_pair_fourier_expansion434 k hk m mp hm]
  simp [parity_signed_shift_two_odd_coefficient_zero434 k hk hodd]

end Green64Analytic.Parity

end

end

/-! ## ShiftTwoMaskFinitePairs -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 28000

/-- Exact original Fourier reindex over arbitrary finite off-diagonal
cofactor pairs, preserving original m-unit condition at every row. -/
theorem parity_signed_shift_two_finite_pair_character_expansion434
    {I : Type} [DecidableEq I]
    (k : ℤ) (hk : k ≠ 0)
    (S : Finset I) (m mp : I → ZMod (2*k.natAbs))
    (hm : ∀ i ∈ S, IsUnit (m i)) (A : I → ℂ) :
    (∑ i ∈ S,
      A i * (if ((mp i)*(m i)⁻¹).val ∈
        b625ParityShiftTwoResidues434 k.natAbs then (1 : ℂ) else 0)) =
    ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑ i ∈ S, A i * chi (mp i) * star (chi (m i))) := by
  calc
    _ = ∑ i ∈ S,
      A i * (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * chi (mp i) *
          star (chi (m i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [parity_signed_shift_two_original_pair_fourier_expansion434 k hk
          (m i) (mp i) (hm i hi)]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi hchi
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Sharp global character budget: the h=-2 original Parity mask incurs
no logarithmic coefficient loss in any finite off-diagonal pair sum.
Each individual twisted sum may use a different character, but the
bound M must hold uniformly; this is not an assumption of E4.1. -/
theorem parity_signed_shift_two_finite_pair_character_budget434
    {I : Type} [DecidableEq I]
    (k : ℤ) (hk : k ≠ 0)
    (S : Finset I) (m mp : I → ZMod (2*k.natAbs))
    (hm : ∀ i ∈ S, IsUnit (m i)) (A : I → ℂ)
    (M : ℝ) (hM : 0 ≤ M)
    (hEach : ∀ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖∑ i ∈ S, A i * chi (mp i) * star (chi (m i))‖ ≤ M) :
    ‖∑ i ∈ S,
      A i * (if ((mp i)*(m i)⁻¹).val ∈
        b625ParityShiftTwoResidues434 k.natAbs then (1 : ℂ) else 0)‖ ≤ M := by
  rw [parity_signed_shift_two_finite_pair_character_expansion434 k hk S m mp hm A]
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∑ i ∈ S, A i * chi (mp i) * star (chi (m i)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ * M := by
        apply Finset.sum_le_sum
        intro chi hchi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hEach chi) (norm_nonneg _)
    _ = M * (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) := by
        rw [←Finset.sum_mul]
        ring
    _ ≤ M * 1 :=
      mul_le_mul_of_nonneg_left (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = M := mul_one _
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoMaskIntegerTwo -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Literal original Parity (2.3)-(2.6), for signed k=±2:
integer divisibility with an ODD quotient (not a parity-only replacement)
coincides with exact totient-normalized Fourier character mask. The two
integer cofactors must be odd; the true m unit mod 4 is not discarded.
This is a special signed shift case, not yet general variable k. -/
theorem parity_signed_shift_two_integer_quotient_fourier_k_two434
    (m mp k : ℤ) (hm : Odd m) (hp : Odd mp)
    (hk : k = 2 ∨ k = -2)
    (hunit : IsUnit (m : ZMod 4))
    (hunitp : IsUnit (mp : ZMod 4)) :
    (if k ∣ mp-m ∧ Odd ((mp-m)/k) then (1 : ℂ) else 0) =
      ∑ chi : DirichletCharacter ℂ 4,
        parityShiftTwoMaskCoefficient434 2 chi *
          chi (mp : ZMod 4) * star (chi (m : ZMod 4)) := by
  have hOriginal := b625_parity_signed_two_quotient_projector434 m mp k hm hp hk
  have hRatio := b625_parity_k_two_ratio_projector434
    (m : ZMod 4) (mp : ZMod 4) hunit hunitp
  have hFourier := parity_shift_two_mask_original_pair_fourier_expansion434
    2 (by norm_num) (m : ZMod 4) (mp : ZMod 4) hunit
  calc
    _ = (1-b625ParityChiFour434 (mp : ZMod 4) *
      star (b625ParityChiFour434 (m : ZMod 4)))/2 := hOriginal
    _ = (if ((mp : ZMod 4)*(m : ZMod 4)⁻¹).val ∈
      b625ParityShiftTwoResidues434 2 then (1 : ℂ) else 0) := hRatio.symm
    _ = _ := hFourier
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoMaskIntegerGeneral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 28000

/-- For all d>0, Parity's d-divisibility with odd integer quotient is exactly
the residue class d modulo 2d, with no unit or sign assumptions. -/
theorem parity_positive_d_odd_integer_quotient_iff434
    (d : ℕ) (hd : 0 < d) (diff : ℤ) :
    ((d : ℤ) ∣ diff ∧ Odd (diff / (d : ℤ))) ↔
      (2*(d : ℤ)) ∣ (diff-(d : ℤ)) := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · rintro ⟨hdiv,⟨t,ht⟩⟩
    have hmul : diff = (d : ℤ)*(diff/(d : ℤ)) := by
      nlinarith [Int.ediv_mul_cancel hdiv]
    refine ⟨t,?_⟩
    nlinarith
  · rintro ⟨t,ht⟩
    have hmul : diff=(d : ℤ)*(2*t+1) := by nlinarith
    have hdiv : (d : ℤ) ∣ diff := ⟨2*t+1,hmul⟩
    refine ⟨hdiv,⟨t,?_⟩⟩
    rw [hmul,Int.mul_ediv_cancel_left _ hdZ]

/-- A unit odd m multiplied by the sole even-d Parity residue d+1 is
exactly m+d modulo 2d. The factor d(m-1) is divisible by 2d, not zero
as an integer; this is why the unit/oddness condition is indispensable. -/
theorem parity_even_d_odd_m_residue_product434
    (d : ℕ) (hd : 0 < d) (m : ℤ) (hm : Odd m) :
    (m : ZMod (2*d)) * ((d+1 : ℕ) : ZMod (2*d)) =
      ((m + (d : ℤ)) : ZMod (2*d)) := by
  have hcast :
      (m : ZMod (2*d)) * ((d+1 : ℕ) : ZMod (2*d)) =
        ((m*((d : ℤ)+1) : ℤ) : ZMod (2*d)) := by
    push_cast
    ring
  rw [hcast]
  have hsum : (m : ZMod (2*d)) + ((d : ℤ) : ZMod (2*d)) =
      ((m+(d : ℤ) : ℤ) : ZMod (2*d)) := by push_cast; ring
  rw [hsum]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hm with ⟨t,ht⟩
  refine ⟨-t,?_⟩
  push_cast
  nlinarith

/-- Exact original congruence for arbitrary even or odd d: on odd m,
the equality mp ≡ m(d+1) (mod 2d) is equivalent to the INTEGER
condition mp-m ≡ d (mod 2d), with no invalid cancellation of d. -/
theorem parity_odd_m_ratio_residue_congruence434
    (d : ℕ) (hd : 0 < d) (m mp : ℤ) (hm : Odd m) :
    ((mp : ZMod (2*d)) =
       (m : ZMod (2*d))*((d+1 : ℕ) : ZMod (2*d))) ↔
      (2*(d : ℤ)) ∣ (mp-m-(d : ℤ)) := by
  rw [parity_even_d_odd_m_residue_product434 d hd m hm]
  have hCast : (mp : ZMod (2*d)) = ((m+(d : ℤ) : ℤ) : ZMod (2*d)) ↔
      ((2*d : ℕ) : ℤ) ∣ ((m+(d : ℤ))-mp) :=
    ZMod.intCast_eq_intCast_iff_dvd_sub mp (m+(d : ℤ)) (2*d)
  have hsum : (m : ZMod (2*d)) + ((d : ℤ) : ZMod (2*d)) =
      ((m+(d : ℤ) : ℤ) : ZMod (2*d)) := by push_cast; ring
  rw [hsum, hCast]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨-t,?_⟩
    push_cast at ht ⊢
    nlinarith
  · rintro ⟨t,ht⟩
    refine ⟨-t,?_⟩
    push_cast at ht ⊢
    nlinarith

/-- Valid ZMod ratio cancellation on an actual unit. The quotient is
ordinary multiplicative inverse in the exact residue ring, not an assumed
integer division equality. -/
theorem parity_unit_ratio_cancel434
    (q : ℕ) [NeZero q] (m mp r : ZMod q) (hm : IsUnit m) :
    (mp*m⁻¹ = r) ↔ (mp = m*r) := by
  have hi : m⁻¹*m = 1 := (ZMod.inv_mul_eq_one_of_isUnit hm m).mpr rfl
  have hj : m*m⁻¹ = 1 := by simpa only [mul_comm] using hi
  constructor
  · intro h
    calc
      mp = (mp*m⁻¹)*m := by rw [mul_assoc,hi,mul_one]
      _ = r*m := by rw [h]
      _ = m*r := by ring
  · intro h
    calc
      mp*m⁻¹ = (m*r)*m⁻¹ := by rw [h]
      _ = r*(m*m⁻¹) := by ring
      _ = r := by rw [hj,mul_one]

/-- ORIGINAL Parity (2.5) even-d case for ANY d, not just d=2:
the literal unit-ratio T_{d,2} gate is equivalent to integer d-divisibility
with an odd quotient, provided m is an actual odd unit modulo 2d. -/
theorem parity_even_d_original_ratio_iff_odd_quotient434
    (d : ℕ) (hd : 0 < d) (he : Even d) (m mp : ℤ)
    (hm : Odd m) (hu : IsUnit (m : ZMod (2*d))) :
    (((mp : ZMod (2*d))*(m : ZMod (2*d))⁻¹).val ∈
      b625ParityShiftTwoResidues434 d) ↔
    ((d : ℤ) ∣ mp-m ∧ Odd ((mp-m)/(d : ℤ))) := by
  letI : NeZero (2*d) := ⟨by omega⟩
  have hq : d+1 < 2*d := by
    rcases he with ⟨t,ht⟩
    omega
  have hval : (((d+1 : ℕ) : ZMod (2*d))).val = d+1 :=
    ZMod.val_natCast_of_lt hq
  have hres (r : ZMod (2*d)) :
      r.val = d+1 ↔ r = ((d+1 : ℕ) : ZMod (2*d)) := by
    constructor
    · intro hr
      calc
        r = (r.val : ZMod (2*d)) := (ZMod.natCast_zmod_val r).symm
        _ = ((d+1 : ℕ) : ZMod (2*d)) := by rw [hr]
    · intro hr
      rw [hr]
      exact hval
  rw [b625_parity_shift_two_residue_classification434 d _ hd]
  simp only [he,true_and]
  rw [hres,parity_unit_ratio_cancel434 (2*d) (m : ZMod (2*d))
    (mp : ZMod (2*d)) ((d+1 : ℕ) : ZMod (2*d)) hu]
  rw [parity_odd_m_ratio_residue_congruence434 d hd m mp hm]
  exact (parity_positive_d_odd_integer_quotient_iff434 d hd (mp-m)).symm

/-- FULL original Parity (2.5) ratio gate for EVERY positive d, including odd
d where the mask is empty. Original integer m,m' must both be odd;
the true unit assumption is required for inversion modulo Q=2d. -/
theorem parity_positive_d_original_ratio_iff_odd_quotient434
    (d : ℕ) (hd : 0 < d) (m mp : ℤ)
    (hm : Odd m) (hp : Odd mp)
    (hu : IsUnit (m : ZMod (2*d))) :
    (((mp : ZMod (2*d))*(m : ZMod (2*d))⁻¹).val ∈
      b625ParityShiftTwoResidues434 d) ↔
    ((d : ℤ) ∣ mp-m ∧ Odd ((mp-m)/(d : ℤ))) := by
  by_cases he : Even d
  · exact parity_even_d_original_ratio_iff_odd_quotient434 d hd he m mp hm hu
  · have hset : b625ParityShiftTwoResidues434 d = ∅ := by
      ext r
      rw [b625_parity_shift_two_residue_classification434 d r hd]
      simp [he]
    have hNo : ¬ (((mp : ZMod (2*d))*(m : ZMod (2*d))⁻¹).val ∈
        b625ParityShiftTwoResidues434 d) := by rw [hset]; simp
    constructor
    · intro hr
      exact False.elim (hNo hr)
    rintro ⟨hdiv,hquot⟩
    have hod : Odd d := Nat.not_even_iff_odd.mp he
    rcases hod with ⟨u,huD⟩
    rcases hm with ⟨a,ha⟩
    rcases hp with ⟨b,hb⟩
    obtain ⟨t,ht⟩ :=
      (parity_positive_d_odd_integer_quotient_iff434 d hd (mp-m)).mp
        ⟨hdiv,hquot⟩
    have huDz : (d : ℤ) = 2*(u:ℤ)+1 := by exact_mod_cast huD
    have htZ : mp-m-(d : ℤ) = 2*(d : ℤ)*t := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using ht
    have hmDz := congrArg (fun x : ℤ => 2*x*t) huDz
    have hoddEven : (2*(b-a) : ℤ) =
        2*(2*(u:ℤ)*t+t+(u:ℤ))+1 := by
      nlinarith [htZ,hmDz,ha,hb,huDz]
    omega

/-- For an arbitrary signed nonzero k, the original odd integer quotient
and divisibility are unaffected by replacing k with the actual positive
modulus d=natAbs(k). The negative case uses true integer division by -k. -/
theorem parity_signed_k_odd_integer_quotient_natAbs434
    (k : ℤ) (hk : k ≠ 0) (diff : ℤ) :
    (k ∣ diff ∧ Odd (diff/k)) ↔
      ((k.natAbs : ℤ) ∣ diff ∧ Odd (diff/(k.natAbs : ℤ))) := by
  by_cases hp : 0 ≤ k
  · rw [Int.natAbs_of_nonneg hp]
  · have habs : (k.natAbs : ℤ) = -k := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hp)]
    rw [habs]
    have hdiv : (k ∣ diff) ↔ (-k ∣ diff) := by
      constructor
      · rintro ⟨u,hu⟩
        refine ⟨-u,?_⟩
        nlinarith
      · rintro ⟨u,hu⟩
        refine ⟨-u,?_⟩
        nlinarith
    have hodd : Odd (diff/k) ↔ Odd (diff/(-k)) := by
      rw [Int.ediv_neg]
      constructor
      · intro h
        exact h.neg
      · intro h
        simpa only [neg_neg] using h.neg
    exact ⟨fun h => ⟨hdiv.mp h.1,hodd.mp h.2⟩,
      fun h => ⟨hdiv.mpr h.1,hodd.mpr h.2⟩⟩

/-- FULL signed original Parity (2.5) equivalence for EVERY k≠0:
the integer condition k | (m'-m) with odd signed quotient equals the
literal unit ratio mask T_{|k|,2}. Both original physical cofactors are
odd, and m remains a unit modulo the true Q=2|k|. -/
theorem parity_signed_k_original_integer_ratio_iff434
    (k : ℤ) (hk : k ≠ 0) (m mp : ℤ)
    (hm : Odd m) (hp : Odd mp)
    (hu : IsUnit (m : ZMod (2*k.natAbs))) :
    (((mp : ZMod (2*k.natAbs))*(m : ZMod (2*k.natAbs))⁻¹).val ∈
      b625ParityShiftTwoResidues434 k.natAbs) ↔
    (k ∣ mp-m ∧ Odd ((mp-m)/k)) := by
  exact (parity_positive_d_original_ratio_iff_odd_quotient434
    k.natAbs (Int.natAbs_pos.mpr hk) m mp hm hp hu).trans
      (parity_signed_k_odd_integer_quotient_natAbs434 k hk (mp-m)).symm

/-- EXACT original Parity (2.5)-(2.6) for all signed nonzero k, with
original m,m' odd and the actual unit modulus Q=2|k|. Neither the
unit-ratio gate nor the odd integer quotient is silently discarded. -/
theorem parity_signed_k_original_integer_fourier_expansion434
    (k : ℤ) (hk : k ≠ 0) (m mp : ℤ)
    (hm : Odd m) (hp : Odd mp)
    (hu : IsUnit (m : ZMod (2*k.natAbs))) :
    (if k ∣ mp-m ∧ Odd ((mp-m)/k) then (1 : ℂ) else 0) =
      ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))) := by
  have hiff := parity_signed_k_original_integer_ratio_iff434 k hk m mp hm hp hu
  have hite :
      (if k ∣ mp-m ∧ Odd ((mp-m)/k) then (1 : ℂ) else 0) =
      (if ((mp : ZMod (2*k.natAbs))*(m : ZMod (2*k.natAbs))⁻¹).val ∈
          b625ParityShiftTwoResidues434 k.natAbs then (1 : ℂ) else 0) := by
    by_cases h : k ∣ mp-m ∧ Odd ((mp-m)/k)
    · have hr := hiff.mpr h
      simp only [if_pos h,if_pos hr]
    · have hr : ¬ (((mp : ZMod (2*k.natAbs))*(m : ZMod (2*k.natAbs))⁻¹).val ∈
          b625ParityShiftTwoResidues434 k.natAbs) := fun hh => h (hiff.mp hh)
      simp only [if_neg h,if_neg hr]
  rw [hite]
  exact parity_signed_shift_two_original_pair_fourier_expansion434 k hk
    (m : ZMod (2*k.natAbs)) (mp : ZMod (2*k.natAbs)) hu
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoBilinearDeterminant -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- For h=-2, a=1 and b=2, the original pair m*n=e*v+2 with odd e
forces (e,n)=1. No unproved coprimality of n and e is assumed. -/
theorem parity_shift_two_original_e_n_coprime434
    (e m n v : ℕ) (he : Odd e)
    (hEq : m*n = e*v+2) : e.Coprime n := by
  let g := e.gcd n
  have hge : g ∣ e := Nat.gcd_dvd_left e n
  have hgn : g ∣ n := Nat.gcd_dvd_right e n
  have hgev : g ∣ e*v := hge.mul_right v
  have hgm : g ∣ m*n := hgn.mul_left m
  have hsum : g ∣ e*v+2 := by rw [←hEq]; exact hgm
  have htwo : g ∣ 2 := (Nat.dvd_add_iff_right hgev).mpr hsum
  have hcop2 : e.Coprime 2 := Nat.coprime_two_right.mpr he
  have hgc : g.Coprime 2 := Nat.Coprime.of_dvd hge (dvd_refl 2) hcop2
  have hg1 : g.gcd 2=1 := Nat.coprime_iff_gcd_eq_one.mp hgc
  have hg2 : g.gcd 2=g := Nat.gcd_eq_left_iff_dvd.mpr htwo
  change e.gcd n=1
  omega

/-- Original Parity (2.1)->(2.2), specialized to h=-2 (a=1,b=2).
The signed nonzero k is actually DERIVED from both bilinear equations
and the original odd-e support. Neither e|m'-m nor coprimality(e,n)
is assumed. The two integer shifts and determinant are exact. -/
theorem parity_shift_two_original_forward_bilinear434
    (e m mp n v vp : ℕ) (he : Odd e)
    (h1 : m*n=e*v+2) (h2 : mp*n=e*vp+2)
    (hmneq : m ≠ mp) :
    ∃ k : ℤ, k ≠ 0 ∧
      ((mp : ℤ)-(m : ℤ)) = (e : ℤ)*k ∧
      ((vp : ℤ)-(v : ℤ)) = k*(n : ℤ) ∧
      ((m : ℤ)*(vp : ℤ) - (mp : ℤ)*(v : ℤ)) = 2*k := by
  have hc : IsCoprime (e : ℤ) (n : ℤ) :=
    (parity_shift_two_original_e_n_coprime434 e m n v he h1).isCoprime
  have heZ : (e : ℤ) ≠ 0 := by
    rcases he with ⟨t,ht⟩
    have he0 : e ≠ 0 := by omega
    exact_mod_cast he0
  have h1z : (m : ℤ)*(n : ℤ) = (e : ℤ)*(v : ℤ)+2 := by
    exact_mod_cast h1
  have h2z : (mp : ℤ)*(n : ℤ) = (e : ℤ)*(vp : ℤ)+2 := by
    exact_mod_cast h2
  have hdiff : ((mp : ℤ)-(m : ℤ))*(n : ℤ) =
      (e : ℤ)*((vp : ℤ)-(v : ℤ)) := by
    calc
      _ = (mp : ℤ)*(n : ℤ)-(m : ℤ)*(n : ℤ) := by ring
      _ = ((e : ℤ)*(vp : ℤ)+2)-((e : ℤ)*(v : ℤ)+2) := by rw [h2z,h1z]
      _ = (e : ℤ)*((vp : ℤ)-(v : ℤ)) := by ring
  have hdivProd : (e : ℤ) ∣ ((mp : ℤ)-(m : ℤ))*(n : ℤ) :=
    ⟨((vp : ℤ)-(v : ℤ)),hdiff⟩
  obtain ⟨k,hk⟩ : (e : ℤ) ∣ ((mp : ℤ)-(m : ℤ)) :=
    hc.dvd_of_dvd_mul_right hdivProd
  have hk0 : k ≠ 0 := by
    intro hz
    have hsame : (mp : ℤ)=(m : ℤ) := by
      rw [hz,mul_zero] at hk
      omega
    have hsamenat : mp=m := by exact_mod_cast hsame
    exact hmneq hsamenat.symm
  have hvrel : ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) := by
    have hmul : (e : ℤ)*((vp : ℤ)-(v : ℤ)) =
        (e : ℤ)*(k*(n : ℤ)) := by
      calc
        _ = ((mp : ℤ)-(m : ℤ))*(n : ℤ) := hdiff.symm
        _ = ((e : ℤ)*k)*(n : ℤ) := by rw [hk]
        _ = (e : ℤ)*(k*(n : ℤ)) := by ring
    exact mul_left_cancel₀ heZ hmul
  have hdet : ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k := by
    have hmp : (mp : ℤ)=(m : ℤ)+(e : ℤ)*k := by linarith [hk]
    have hvp : (vp : ℤ)=(v : ℤ)+k*(n : ℤ) := by linarith [hvrel]
    have hbase : (m : ℤ)*(n : ℤ)-(e : ℤ)*(v : ℤ)=2 := by
      linarith [h1z]
    calc
      _ = k*((m : ℤ)*(n : ℤ)-(e : ℤ)*(v : ℤ)) := by
        rw [hmp,hvp]
        ring
      _ = 2*k := by rw [hbase]; ring
  exact ⟨k,hk0,hk,hvrel,hdet⟩

/-- The true converse of original Parity (2.2)->(2.1) for h=-2:
under the source inverse conditions e>0, m>0, integer e*k=m'-m,
original determinant m*v'-m'*v=2*k, and true gcd(m,k)=1,
construct a POSITIVE integer n, rather than assuming its integrality.
All three original bilinear equations and v'-v=k*n then follow. -/
theorem parity_shift_two_original_inverse_bilinear434
    (e m mp v vp k : ℤ)
    (he : 0 < e) (hm : 0 < m) (hv : 0 < v)
    (hmp : 0 < mp) (hvp : 0 < vp)
    (hk : k ≠ 0) (hcop : IsCoprime m k)
    (hshift : mp-m=e*k)
    (hdet : m*vp-mp*v=2*k) :
    ∃ n : ℤ, 0 < n ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧ vp-v=k*n := by
  have hprod : m*(vp-v)=k*(e*v+2) := by
    calc
      _ = (m*vp-mp*v)+(mp-m)*v := by ring
      _ = 2*k+(e*k)*v := by rw [hdet,hshift]
      _ = k*(e*v+2) := by ring
  have hdivProd : m ∣ k*(e*v+2) := ⟨vp-v,hprod.symm⟩
  have hdiv : m ∣ e*v+2 := hcop.dvd_of_dvd_mul_left hdivProd
  let n : ℤ := (e*v+2)/m
  have hnum : 0 < e*v+2 := by positivity
  have hnumEq : e*v+2=n*m := by
    exact (Int.ediv_mul_cancel hdiv).symm
  have hn : 0 < n := by
    by_contra hnnot
    have hnle : n ≤ 0 := le_of_not_gt hnnot
    have hx : n*m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnle hm.le
    omega
  have hmn : m*n=e*v+2 := by rw [hnumEq]; ring
  have hvrel : vp-v=k*n := by
    have hmul : m*(vp-v)=m*(k*n) := by
      calc
        _ = k*(e*v+2) := hprod
        _ = k*(m*n) := by rw [←hmn]
        _ = m*(k*n) := by ring
    exact mul_left_cancel₀ hm.ne' hmul
  have hmpn : mp*n=e*vp+2 := by
    have hmpEq : mp=m+e*k := by linarith [hshift]
    have hvpEq : vp=v+k*n := by linarith [hvrel]
    calc
      mp*n = (m+e*k)*n := by rw [hmpEq]
      _ = (e*v+2)+e*(k*n) := by rw [←hmn];ring
      _ = e*vp+2 := by rw [hvpEq]; ring
  exact ⟨n,hn,hmn,hmpn,hvrel⟩
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoMaskIntegerPairs -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 28000

/-- The FULL original Parity off-diagonal arithmetic mask (2.3)-(2.6)
for arbitrary finite integer m,m' cofactor pairs and ALL signed k!=0:
no ratio/character or odd quotient is dropped before summation. -/
theorem parity_signed_k_finite_integer_pair_fourier_expansion434
    {I : Type} [DecidableEq I]
    (k : ℤ) (hk : k ≠ 0)
    (S : Finset I) (m mp : I → ℤ)
    (hm : ∀ i ∈ S, Odd (m i))
    (hp : ∀ i ∈ S, Odd (mp i))
    (hu : ∀ i ∈ S, IsUnit ((m i : ℤ) : ZMod (2*k.natAbs)))
    (A : I → ℂ) :
    (∑ i ∈ S, A i *
      (if k ∣ mp i-m i ∧ Odd ((mp i-m i)/k) then (1 : ℂ) else 0)) =
    ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∑ i ∈ S, A i * chi ((mp i : ℤ) : ZMod (2*k.natAbs)) *
        star (chi ((m i : ℤ) : ZMod (2*k.natAbs)))) := by
  calc
    _ = ∑ i ∈ S, A i *
      (if (((mp i : ℤ) : ZMod (2*k.natAbs)) *
          ((m i : ℤ) : ZMod (2*k.natAbs))⁻¹).val ∈
          b625ParityShiftTwoResidues434 k.natAbs then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiff := parity_signed_k_original_integer_ratio_iff434
        k hk (m i) (mp i) (hm i hi) (hp i hi) (hu i hi)
      by_cases h : k ∣ mp i-m i ∧ Odd ((mp i-m i)/k)
      · have hr := hiff.mpr h
        simp only [if_pos h,if_pos hr]
      · have hr : ¬ (((mp i : ℤ) : ZMod (2*k.natAbs)) *
            ((m i : ℤ) : ZMod (2*k.natAbs))⁻¹).val ∈
              b625ParityShiftTwoResidues434 k.natAbs := fun hh => h (hiff.mp hh)
        simp only [if_neg h,if_neg hr]
    _ = _ := parity_signed_shift_two_finite_pair_character_expansion434
      k hk S (fun i => ((m i : ℤ) : ZMod (2*k.natAbs)))
      (fun i => ((mp i : ℤ) : ZMod (2*k.natAbs))) hu A

/-- Sharp full-cofactor original integer-pair mask bound. Under the
original odd/unit support and a common bound M on EVERY chi-twisted sum,
Parity's full signed Fourier mask costs AT MOST M (not phi(Q)*M or 2*M).
The per-character analytic bound remains an explicit debt for TypeII. -/
theorem parity_signed_k_finite_integer_pair_mask_budget434
    {I : Type} [DecidableEq I]
    (k : ℤ) (hk : k ≠ 0)
    (S : Finset I) (m mp : I → ℤ)
    (hm : ∀ i ∈ S, Odd (m i))
    (hp : ∀ i ∈ S, Odd (mp i))
    (hu : ∀ i ∈ S, IsUnit ((m i : ℤ) : ZMod (2*k.natAbs)))
    (A : I → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hEach : ∀ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖∑ i ∈ S, A i * chi ((mp i : ℤ) : ZMod (2*k.natAbs)) *
        star (chi ((m i : ℤ) : ZMod (2*k.natAbs)))‖ ≤ M) :
    ‖∑ i ∈ S, A i *
      (if k ∣ mp i-m i ∧ Odd ((mp i-m i)/k) then (1 : ℂ) else 0)‖ ≤ M := by
  rw [parity_signed_k_finite_integer_pair_fourier_expansion434
    k hk S m mp hm hp hu A]
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑ i ∈ S, A i * chi ((mp i : ℤ) : ZMod (2*k.natAbs)) *
          star (chi ((m i : ℤ) : ZMod (2*k.natAbs))))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ * M := by
        apply Finset.sum_le_sum
        intro chi hchi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hEach chi) (norm_nonneg _)
    _ = M * (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) := by
        rw [←Finset.sum_mul]
        ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = M := mul_one _
end Green64Analytic.Parity

end

end

/-! ## Standalone.SourceU1Min -/

section

namespace Green64Analytic.LongPrime

-- Exact unproved source output contract, not a theorem or proof certificate.
noncomputable def SourceLongPrimeU1 : Prop :=
  let P : (q : ℕ) → DirichletCharacter ℂ q → ℝ → Set ℝ → ℝ → ℂ :=
    fun q χ N I t =>
      ∑ p ∈ (@Finset.filter ℕ (fun p => (p : ℝ) ∈ I)
        (fun _ => Classical.propDecidable _)
        ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)),
        χ (p : ZMod q) * (p : ℂ)^((-1 : ℂ) + (t : ℂ)*Complex.I)
  ∀ τ η C A : ℝ,
    0 < τ → τ < η → η < 1/4 → 0 < C → 0 < A →
    ∃ B₀ K X₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 3 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
      ∀ N : ℝ, x^τ/2 ≤ N → N ≤ x^η →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x)^C →
      ∀ χ : DirichletCharacter ℂ q,
      ∀ I : Set ℝ, Set.OrdConnected I →
      I ⊆ Set.Icc N (2*N) →
      ∀ t : ℝ, (Real.log x)^B₀ ≤ |t| → |t| ≤ x^2 →
        ‖P q χ N I t‖ ≤ K/(Real.log x)^A
end Green64Analytic.LongPrime

end

/-! ## LifespanRowWeight -/

section

open scoped BigOperators
open Classical
namespace Green64MemoryJoin

theorem lifespan_row_weight :
∀ (N a z : ℕ) (A hit : ℕ → Prop) [DecidablePred A] [DecidablePred hit]
 (ρ V p b : ℂ) (q η : ℕ → ℂ),
 a ≤ z → z ≤ N → (∀ i, A i → a ≤ i ∧ i ≤ z) →
 (a = z → A a) → hit a → hit z → ρ ≠ 0 → V ≠ 0 → p ≠ 0 → b ≠ 0 →
 let runs := (Finset.range (N+1)).filter (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)));
 let promotions := (Finset.range (N+1)).filter
   (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1));
 let localRow (i : ℕ) :=
   (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then ρ else 1) *
   (if (z = i ∧ ¬ A i) ∧ hit i then -η i / ρ
    else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then q i / ρ^2 else 1) *
   (if (a = i ∧ ¬ A i) ∧ hit i then -η i * V / ρ else 1) *
   (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then ρ else 1);
 (1 / (V*p*b)) * (1/V)^promotions.card *
     (∏ i ∈ Finset.range (N+1), localRow i) =
 (1/V)^runs.card / (p*b) *
   (if A a then 1 else -η a) * (if A z then 1 else -η z) *
   (∏ i ∈ Finset.range (N+1),
     if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then q i else 1) :=
by
  have rho : ∀ (a z i : ℕ) (active hit : Prop) [Decidable active] [Decidable hit]
 (ρ q η V : ℂ), a ≤ z → (a = z → a = i → active) → ρ ≠ 0 →
 let before := a < i ∧ i ≤ z ∧ ¬ active;
 let after := a ≤ i ∧ i < z ∧ ¬ active;
 let born := a = i ∧ ¬ active;
 let ended := z = i ∧ ¬ active;
 let keep := a < i ∧ i < z ∧ ¬ active;
 (if before ∧ hit then ρ else 1) *
 (if ended ∧ hit then -η/ρ else if before ∧ hit then q/ρ^2 else 1) *
 (if born ∧ hit then -η*V/ρ else 1) *
 (if after ∧ hit then ρ else 1) =
 (if born ∧ hit then -η*V else 1) *
 (if ended ∧ hit then -η else 1) *
 (if keep ∧ hit then q else 1) :=
    by
      classical
      intro a z i active hit _ _ ρ q η V haz heq hρ
      dsimp only
      by_cases hA : active
      · simp [hA]
      by_cases hh : hit
      · simp only [hA,hh,not_false_eq_true,and_true]
        by_cases hs : a = z
        · have hai : a ≠ i := fun h => hA (heq hs h)
          subst z
          have h1 : ¬ (a < i ∧ i ≤ a) := by omega
          have h2 : ¬ (a ≤ i ∧ i < a) := by omega
          have h3 : ¬ (a < i ∧ i < a) := by omega
          simp [hai,h1,h2,h3]
        · have hlt : a < z := by omega
          by_cases h1 : a < i <;> by_cases h2 : i < z <;>
            by_cases h3 : a = i <;> by_cases h4 : z = i <;>
            simp_all <;> (try split_ifs) <;> try omega
          all_goals field_simp <;> ring
      · simp [hh]
  have charge : ∀ (N a z : ℕ) (A : ℕ → Prop) [DecidablePred A],
 a ≤ z → z ≤ N → (∀ i, A i → a ≤ i ∧ i ≤ z) →
 let R := (Finset.range (N+1)).filter (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)));
 let F := (Finset.range (N+1)).filter (fun i => A i ∧ a = i);
 let H := (Finset.range (N+1)).filter
   (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1));
 R = F ∪ H ∧ Disjoint F H ∧
 F.card = (if A a then 1 else 0) ∧
 R.card = (if A a then 1 else 0) + H.card ∧
 ∀ V p b : ℂ, V ≠ 0 → p ≠ 0 → b ≠ 0 →
 (1 / (V*p*b)) * (if A a then 1 else V) * (1/V)^H.card =
   (1/V)^R.card / (p*b) :=
    by
      classical
      intro N a z A _ haz hz hA
      dsimp only
      let R := (Finset.range (N+1)).filter (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
      let F := (Finset.range (N+1)).filter (fun i => A i ∧ a = i)
      let H := (Finset.range (N+1)).filter
        (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
      change R = F ∪ H ∧ Disjoint F H ∧
        F.card = (if A a then 1 else 0) ∧
        R.card = (if A a then 1 else 0) + H.card ∧ _
      have hr : R = F ∪ H := by
        ext i
        simp only [R,F,H,Finset.mem_filter,Finset.mem_range,Finset.mem_union]
        by_cases hi : A i
        · have hia := hA i hi
          by_cases hp : A (i-1)
          · have hpa := hA (i-1) hp
            simp only [hi,hp,not_true_eq_false,and_false,and_true,true_and,or_false,false_and]
            omega
          · simp only [hi,hp,not_false_eq_true,and_true,true_and,or_true]
            omega
        · simp [hi]
      have hd : Disjoint F H := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        simp only [F,H,Finset.mem_filter,Finset.mem_range] at hi hj
        omega
      have hfset : F = if A a then {a} else ∅ := by
        ext i
        simp only [F,Finset.mem_filter,Finset.mem_range]
        by_cases ha : A a
        · simp only [ha,ite_true,Finset.mem_singleton]
          constructor
          · rintro ⟨_,_,hai⟩
            exact hai.symm
          · intro hai
            subst i
            exact ⟨by omega,ha,rfl⟩
        · simp only [ha,ite_false]
          constructor
          · rintro ⟨_,hi,hai⟩
            subst i
            exact (ha hi).elim
          · simp
      have hf : F.card = if A a then 1 else 0 := by
        rw [hfset]
        split_ifs <;> simp
      have hc : R.card = (if A a then 1 else 0) + H.card := by
        rw [hr,Finset.card_union_eq_card_add_card.mpr hd,hf]
      refine ⟨hr,hd,hf,hc,?_⟩
      intro V p b hV hp hb
      rw [hc]
      by_cases ha : A a
      · simp only [ha,ite_true,one_mul,mul_one]
        rw [pow_add]
        simp only [pow_one]
        field_simp
        rfl
      · simp only [ha,ite_false,zero_add]
        field_simp
        rfl
  classical
  intro N a z A hit _ _ ρ V p b q η haz hz hA hsingle haHit hzHit hρ hV hp hb
  dsimp only
  let runs := (Finset.range (N+1)).filter (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
  let promotions := (Finset.range (N+1)).filter
    (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
  let localRow (i : ℕ) :=
    (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then ρ else 1) *
    (if (z = i ∧ ¬ A i) ∧ hit i then -η i / ρ
     else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then q i / ρ^2 else 1) *
    (if (a = i ∧ ¬ A i) ∧ hit i then -η i * V / ρ else 1) *
    (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then ρ else 1)
  let mid := ∏ i ∈ Finset.range (N+1),
    if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then q i else 1
  have factor (i : ℕ) : localRow i =
      (if a = i then (if A a then 1 else -η a * V) else 1) *
      (if z = i then (if A z then 1 else -η z) else 1) *
      (if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then q i else 1) := by
    have heq : a = z → a = i → A i := by
      intro he hi
      simpa [hi] using hsingle he
    have hh := rho a z i (A i) (hit i) ρ (q i) (η i) V haz heq hρ
    change localRow i = _ at hh
    rw [hh]
    have hb : (if (a = i ∧ ¬ A i) ∧ hit i then -η i * V else 1) =
        (if a = i then (if A a then 1 else -η a * V) else 1) := by
      by_cases hi : a = i
      · subst i
        simp [haHit]
      · simp [hi]
    have hd : (if (z = i ∧ ¬ A i) ∧ hit i then -η i else 1) =
        (if z = i then (if A z then 1 else -η z) else 1) := by
      by_cases hi : z = i
      · subst i
        simp [hzHit]
      · simp [hi]
    rw [hb,hd]
  have product : (∏ i ∈ Finset.range (N+1), localRow i) =
      (if A a then 1 else -η a * V) * (if A z then 1 else -η z) * mid := by
    simp_rw [factor]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    rw [Finset.prod_ite_eq_of_mem (s := Finset.range (N+1)) (a := a) (b := fun _ => if A a then (1 : ℂ) else -η a * V) (by simp; omega),
      Finset.prod_ite_eq_of_mem (s := Finset.range (N+1)) (a := z) (b := fun _ => if A z then (1 : ℂ) else -η z) (by simp; omega)]
  have hc : (1 / (V*p*b)) * (if A a then 1 else V) * (1/V)^promotions.card =
      (1/V)^runs.card / (p*b) :=
    (charge N a z A haz hz hA).2.2.2.2 V p b hV hp hb
  change (1 / (V*p*b)) * (1/V)^promotions.card *
    (∏ i ∈ Finset.range (N+1), localRow i) =
    (1/V)^runs.card / (p*b) * (if A a then 1 else -η a) *
      (if A z then 1 else -η z) * mid
  rw [product,← hc]
  by_cases h : A a <;> simp [h] <;> ring


end Green64MemoryJoin

end

/-! ## LogLogIntegral -/

section

open intervalIntegral MeasureTheory
namespace Green64Analytic.ReciprocalPrimeGrid

/-- The logarithmic mass measure on an exponential coordinate interval. -/
theorem integral_inv_log (U V : ℝ) (hU : 1 < U) (hUV : U ≤ V) :
    (∫ t in U..V, t⁻¹ / Real.log t) =
       Real.log (Real.log V / Real.log U) := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc U V) : 1 < t := hU.trans_le ht.1
  have hLogU : 0 < Real.log U := Real.log_pos hU
  have hLogV : 0 < Real.log V := Real.log_pos (hU.trans_le hUV)
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.uIcc U V) := by
    rw [Set.uIcc_of_le hUV]
    have hlog : ContinuousOn Real.log (Set.Icc U V) :=
      Real.continuousOn_log.mono (by intro t ht; exact (ne_of_gt (lt_trans zero_lt_one (hp t ht))))
    apply ContinuousOn.div
    · apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      exact ne_of_gt (lt_trans zero_lt_one (hp t ht))
    · exact hlog
    · intro t ht
      exact ne_of_gt (Real.log_pos (hp t ht))
  have hdiff : ∀ t ∈ Set.uIcc U V, DifferentiableAt ℝ
       (fun x : ℝ => Real.log (Real.log x)) t := by
    rw [Set.uIcc_of_le hUV]
    intro t ht
    have hpt := hp t ht
    apply Real.differentiableAt_log_log
      (by linarith) (by linarith) (by linarith)
  have hF : (∫ t in U..V, t⁻¹ / Real.log t) =
      Real.log (Real.log V) - Real.log (Real.log U) := by
    exact intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ => Real.log (Real.log x)) Real.deriv_log_log hdiff hcont
  rw [hF, Real.log_div (ne_of_gt hLogV) (ne_of_gt hLogU)]

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## M1ActualLogDerivative -/

section

open ArithmeticFunction
open scoped LSeries.notation Topology
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_continued_dirichlet_logderivative
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    -(deriv (fun w : ℂ => LSeries (fun n : ℕ => χ (n : ZMod q)) w) s) /
        LSeries (fun n : ℕ => χ (n : ZMod q)) s =
    -(deriv (DirichletCharacter.LFunction χ) s) /
        DirichletCharacter.LFunction χ s := by
  have hOpen : IsOpen {w : ℂ | (1:ℝ) < w.re} := by
    exact isOpen_Ioi.preimage Complex.continuous_re
  have hEv : (fun w : ℂ => LSeries (fun n : ℕ => χ (n : ZMod q)) w) =ᶠ[nhds s]
      (DirichletCharacter.LFunction χ) := by
    filter_upwards [hOpen.mem_nhds hs] with w hw
    exact (DirichletCharacter.LFunction_eq_LSeries χ hw).symm
  have hDer := Filter.EventuallyEq.deriv_eq hEv
  have hVal := DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [hDer, ← hVal]

theorem actual_continued_twist_vonMangoldt
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries ((fun n : ℕ => χ (n : ZMod q)) *
       (fun n : ℕ => (Λ n : ℂ))) s =
    -(deriv (DirichletCharacter.LFunction χ) s) /
      DirichletCharacter.LFunction χ s := by
  calc
    LSeries ((fun n : ℕ => χ (n : ZMod q)) *
       (fun n : ℕ => (Λ n : ℂ))) s =
      -(deriv (fun w : ℂ => LSeries (fun n : ℕ => χ (n : ZMod q)) w) s) /
        LSeries (fun n : ℕ => χ (n : ZMod q)) s := by
          exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    _ = _ := actual_continued_dirichlet_logderivative q χ s hs
end Green64Analytic.LongPrime

end

/-! ## M1Convergence -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_convergent_compact :
∀ (a b : ℝ) (g : ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b → Continuous g →
  (∀ t : ℝ, t ≤ a ∨ b < t → g t = 0) →
  MellinConvergent g s :=
by
  intro a b g s ha hab hg hsupp
  have hcont : ContinuousOn
      (fun t : ℝ => (t:ℂ)^(s-1) * g t) (Set.Icc a b) := by
    intro t ht
    have htpos : 0 < t := ha.trans_le ht.1
    exact ((Complex.continuousAt_ofReal_cpow_const t (s-1)
      (Or.inr htpos.ne')).mul hg.continuousAt).continuousWithinAt
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t:ℂ)^(s-1) * g t) (Set.Icc a b) :=
    hcont.integrableOn_Icc
  have hz : ∀ t, t ∉ Set.Icc a b →
      (t:ℂ)^(s-1) * g t = 0 := by
    intro t ht
    have hcases : t ≤ a ∨ b < t := by
      by_contra hn
      push_neg at hn
      exact ht ⟨hn.1.le,hn.2⟩
    simp [hsupp t hcases]
  have hAll : MeasureTheory.Integrable
      (fun t : ℝ => (t:ℂ)^(s-1) * g t) :=
    hint.integrable_of_forall_notMem_eq_zero hz
  change MeasureTheory.IntegrableOn
    (fun t : ℝ => (t:ℂ)^(s-1) * g t) (Set.Ioi 0)
  exact hAll.integrableOn
end Green64Analytic.LongPrime

end

/-! ## M1InvDef -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellinInv_complex_def :
∀ (σ u : ℝ) (F : ℂ → ℂ),
  mellinInv σ F u =
    (1/(2*Real.pi):ℂ) * (∫ y : ℝ,
      (u:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I)) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I)) :=
by
  intro σ u F
  unfold mellinInv
  rw [Complex.real_smul]
  push_cast
  rfl
end Green64Analytic.LongPrime

end

/-! ## M1Kernel -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem integrable_vertical_kernel :
∀ (u σ : ℝ) (F : ℂ → ℂ), 0 < u →
  Complex.VerticalIntegrable F σ →
  MeasureTheory.Integrable
    (fun y : ℝ => (u:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I)) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I)) :=
by
  intro u σ F hu hF
  have huc : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hd : Differentiable ℂ (fun z : ℂ => (u:ℂ)^(-z)) :=
    (differentiable_id.neg).const_cpow (.inl huc)
  have hc : Continuous (fun y : ℝ =>
      (u:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) :=
    hd.continuous.comp (by fun_prop)
  have hnorm : ∀ y : ℝ,
      ‖(u:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))‖ ≤ u^(-σ) := by
    intro y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp
  change MeasureTheory.Integrable
      (fun y : ℝ => F ((σ:ℂ)+(y:ℂ)*Complex.I)) at hF
  exact hF.bdd_mul hc.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hnorm)
end Green64Analytic.LongPrime

end

/-! ## M1InfiniteExchange -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem infinite_mellin_exchange
    (u : ℕ → ℝ) (c : ℕ → ℂ) (σ : ℝ) (F : ℂ → ℂ)
    (hu : ∀ n, 0 < u n)
    (hV : Complex.VerticalIntegrable F σ)
    (hc : Summable (fun n : ℕ => ‖c n‖ * (u n)^(-σ))) :
    (∑' n : ℕ, ∫ y : ℝ, (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
       F ((σ:ℂ)+(y:ℂ)*Complex.I)) =
    ∫ y : ℝ, ∑' n : ℕ, (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
       F ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  let K : ℕ → ℝ → ℂ := fun n y =>
    (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
       F ((σ:ℂ)+(y:ℂ)*Complex.I)
  have hint (n : ℕ) : MeasureTheory.Integrable (K n) := by
    have h := (integrable_vertical_kernel (u n) σ F (hu n) hV).const_mul (c n)
    simpa only [K, mul_assoc] using h
  have hne (n : ℕ) (y : ℝ) :
      ‖K n y‖ = (‖c n‖*(u n)^(-σ)) *
          ‖F ((σ:ℂ)+(y:ℂ)*Complex.I)‖ := by
    dsimp only [K]
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu n),
      Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero, add_zero, mul_one]
  have hnormsum : Summable
      (fun n : ℕ => ∫ y : ℝ, ‖K n y‖) := by
    have hbase : Summable (fun n : ℕ =>
      (‖c n‖*(u n)^(-σ)) * (∫ y : ℝ, ‖F ((σ:ℂ)+(y:ℂ)*Complex.I)‖)) := by
      simpa only [mul_comm] using
        (Summable.mul_left
          (∫ y : ℝ, ‖F ((σ:ℂ)+(y:ℂ)*Complex.I)‖) hc)
    convert hbase using 1
    ext n
    simp_rw [hne n]
    rw [MeasureTheory.integral_const_mul]
  simpa only [K] using
    (MeasureTheory.integral_tsum_of_summable_integral_norm hint hnormsum)
end Green64Analytic.LongPrime

end

/-! ## M1InfiniteInverse -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem infinite_weighted_mellin_inverse
    (u : ℕ → ℝ) (c : ℕ → ℂ) (σ : ℝ) (F : ℂ → ℂ)
    (hu : ∀ n, 0 < u n)
    (hV : Complex.VerticalIntegrable F σ)
    (hc : Summable (fun n : ℕ => ‖c n‖ * (u n)^(-σ))) :
    (∑' n : ℕ, c n * mellinInv σ F (u n)) =
    (1/(2*Real.pi):ℂ) * (∫ y : ℝ, ∑' n : ℕ,
      (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I)) := by
  have hterm (n : ℕ) :
      c n * mellinInv σ F (u n) =
      (1/(2*Real.pi):ℂ) * (∫ y : ℝ,
        (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
        F ((σ:ℂ)+(y:ℂ)*Complex.I)) := by
    rw [mellinInv_complex_def]
    simp_rw [show ∀ y : ℝ,
      (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
        F ((σ:ℂ)+(y:ℂ)*Complex.I) =
        c n * ((u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I)) *
          F ((σ:ℂ)+(y:ℂ)*Complex.I)) from fun y => by ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  calc
    (∑' n : ℕ, c n * mellinInv σ F (u n)) =
      ∑' n : ℕ, (1/(2*Real.pi):ℂ) * (∫ y : ℝ,
        (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
        F ((σ:ℂ)+(y:ℂ)*Complex.I)) :=
          tsum_congr hterm
    _ = (1/(2*Real.pi):ℂ) * (∑' n : ℕ, ∫ y : ℝ,
        (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
        F ((σ:ℂ)+(y:ℂ)*Complex.I)) := by
          rw [tsum_mul_left]
    _ = _ := by
          rw [infinite_mellin_exchange u c σ F hu hV hc]
end Green64Analytic.LongPrime

end

/-! ## M1LSeriesShift -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem lseries_tsum_shift_one (f : ℕ → ℂ) (s : ℂ)
    (h : LSeriesSummable f s) :
    (∑' n : ℕ, LSeries.term f s (n+1)) = LSeries f s := by
  have ht := h.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, LSeries.term_zero, zero_add, LSeries] using ht
end Green64Analytic.LongPrime

end

/-! ## M1Majorant -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem integrable_frequency_majorant :
∀ (C : ℝ), MeasureTheory.Integrable
  (fun y : ℝ => C / (1+|y|)^2) :=
by
  intro C
  have h : MeasureTheory.Integrable (fun y : ℝ => (1+‖y‖)^(-2:ℝ)) :=
    integrable_one_add_norm (E := ℝ) (r := (2:ℝ))
      (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)
  have h' : MeasureTheory.Integrable
    (fun y : ℝ => C * (1+|y|)^(-2:ℝ)) := by
    simpa only [Real.norm_eq_abs] using h.const_mul C
  have heq : (fun y : ℝ => C/(1+|y|)^2) =
      (fun y : ℝ => C*(1+|y|)^(-2:ℝ)) := by
    funext y
    rw [Real.rpow_neg (by positivity : 0 ≤ 1+|y|)]
    rw [div_eq_mul_inv]
    norm_num [Real.rpow_natCast]
  rw [heq]
  exact h'
end Green64Analytic.LongPrime

end

/-! ## M1NaturalExchange -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem shifted_natural_mellin_exchange
    (N σ : ℝ) (c : ℕ → ℂ) (F : ℂ → ℂ)
    (hN : 0 < N)
    (hV : Complex.VerticalIntegrable F σ)
    (hCoeff : Summable (fun n : ℕ =>
       ‖c n‖ * (((n+1:ℕ):ℝ)/N)^(-σ))) :
    (∑' n : ℕ, ∫ y : ℝ,
        (c n * (((n+1:ℕ):ℝ)/N:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
          F ((σ:ℂ)+(y:ℂ)*Complex.I)) =
    ∫ y : ℝ, ∑' n : ℕ,
        (c n * (((n+1:ℕ):ℝ)/N:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
          F ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  have hPos : ∀ n : ℕ, 0 < (((n+1:ℕ):ℝ)/N) := by
    intro n
    exact div_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) hN
  have h := infinite_mellin_exchange
    (fun n : ℕ => (((n+1:ℕ):ℝ)/N)) c σ F hPos hV hCoeff
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using h
end Green64Analytic.LongPrime

end

/-! ## M1ScaleComplex -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem complex_mellin_source_scale (x N : ℝ) (z : ℂ)
    (hx : 0 < x) (hN : 0 < N) :
    ((x/N : ℝ):ℂ)^(-z) = (N:ℂ)^z * (x:ℂ)^(-z) := by
  have hNz : (N:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hN.le]
    exact ne_of_lt Real.pi_pos
  have hInv : (((N⁻¹ : ℝ):ℂ)^(-z)) = (N:ℂ)^z := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ (-z) hNz,
      Complex.cpow_neg, inv_inv]
  calc
    ((x/N : ℝ):ℂ)^(-z) =
        ((x:ℂ)*((N⁻¹:ℝ):ℂ))^(-z) := by
          rw [div_eq_mul_inv, Complex.ofReal_mul]
    _ = (x:ℂ)^(-z) * ((N⁻¹:ℝ):ℂ)^(-z) :=
      Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hN.le) (-z)
    _ = (N:ℂ)^z * (x:ℂ)^(-z) := by rw [hInv]; ring
end Green64Analytic.LongPrime

end

/-! ## M1ScaleReal -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem real_mellin_source_scale (x N σ : ℝ) (hx : 0 < x) (hN : 0 < N) :
    (1/x)*((x/N)^(-σ)) = N^σ / x^(1+σ) := by
  have he : (x/N)^(-σ) = x^(-σ)*N^σ := by
    rw [Real.div_rpow hx.le hN.le]
    rw [Real.rpow_neg hN.le]
    exact div_inv_eq_mul _ _
  calc
    (1/x)*((x/N)^(-σ)) = x^(-1:ℝ) * (x^(-σ)*N^σ) := by
      rw [he, Real.rpow_neg_one]
      ring
    _ = (x^(-1:ℝ) * x^(-σ)) * N^σ := by ring
    _ = N^σ * x^((-1)+(-σ)) := by
      rw [← Real.rpow_add hx]
      ring
    _ = N^σ / x^(1+σ) := by
      rw [show (-1:ℝ)+(-σ) = -(1+σ) by ring]
      rw [Real.rpow_neg hx.le]
      ring
end Green64Analytic.LongPrime

end

/-! ## M1CoeffScale -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem lseries_source_weight_norm_scale (f : ℕ → ℂ) (n : ℕ)
    (N σ t : ℝ) (hN : 0 < N) :
    ‖LSeries.term f ((1:ℂ)-(t:ℂ)*Complex.I) (n+1)‖ *
      ((((n+1:ℕ):ℝ)/N)^(-σ)) =
    N^σ * ‖LSeries.term f (((1+σ:ℝ):ℂ)-(t:ℂ)*Complex.I) (n+1)‖ := by
  have hn : 0 < (((n+1:ℕ):ℝ)) := Nat.cast_pos.mpr (Nat.succ_pos n)
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp only [Nat.succ_ne_zero, if_false, Complex.sub_re,
    Complex.add_re, Complex.ofReal_re, Complex.one_re,
    Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    mul_one, Real.rpow_one]
  calc
    (‖f (n+1)‖/((n+1:ℕ):ℝ)) *
        ((((n+1:ℕ):ℝ)/N)^(-σ)) =
      ‖f (n+1)‖ * ((1/((n+1:ℕ):ℝ)) *
        (((n+1:ℕ):ℝ)/N)^(-σ)) := by ring
    _ = ‖f (n+1)‖ * (N^σ/(((n+1:ℕ):ℝ)^(1+σ))) := by
      rw [real_mellin_source_scale _ N σ hn hN]
    _ = N^σ * (‖f (n+1)‖/(((n+1:ℕ):ℝ)^(1+σ))) := by ring
end Green64Analytic.LongPrime

end

/-! ## M1TermScale -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem lseries_mellin_term_scale (f : ℕ → ℂ) (n : ℕ)
    (N : ℝ) (z s₀ : ℂ) (hN : 0 < N) :
    LSeries.term f s₀ (n+1) *
       (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z) =
    (N:ℂ)^z * LSeries.term f (s₀+z) (n+1) := by
  have hn : (n+1:ℕ) ≠ 0 := Nat.succ_ne_zero _
  have hnr : 0 < (((n+1:ℕ):ℝ)) := Nat.cast_pos.mpr (Nat.succ_pos n)
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [complex_mellin_source_scale _ N z hnr hN]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  rw [Complex.cpow_neg]
  simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_inv_rev]
  ring
end Green64Analytic.LongPrime

end

/-! ## M1LSeriesScaledTsum -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem lseries_scaled_shift_tsum (f : ℕ → ℂ)
    (N : ℝ) (z s₀ : ℂ) (hN : 0 < N)
    (hs : LSeriesSummable f (s₀+z)) :
    (∑' n : ℕ,
       LSeries.term f s₀ (n+1) *
       (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
    (N:ℂ)^z * LSeries f (s₀+z) := by
  calc
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
       (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
     ∑' n : ℕ, (N:ℂ)^z * LSeries.term f (s₀+z) (n+1) :=
      tsum_congr (fun n => lseries_mellin_term_scale f n N z s₀ hN)
    _ = (N:ℂ)^z * (∑' n : ℕ, LSeries.term f (s₀+z) (n+1)) := by
      rw [tsum_mul_left]
    _ = (N:ℂ)^z * LSeries f (s₀+z) := by
      rw [lseries_tsum_shift_one f (s₀+z) hs]
end Green64Analytic.LongPrime

end

/-! ## M1TwistSummable -/

section

open ArithmeticFunction
open scoped LSeries.notation
namespace Green64Analytic.LongPrime

theorem twisted_mangoldt_lseries_norm_shift
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      ‖LSeries.term
        ((fun n : ℕ => χ (n : ZMod q)) *
          (fun n : ℕ => (Λ n : ℂ))) s (n+1)‖) := by
  have h : LSeriesSummable
      ((fun n : ℕ => χ (n : ZMod q)) *
        (fun n : ℕ => (Λ n : ℂ))) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  exact (summable_nat_add_iff 1).2 h.norm
end Green64Analytic.LongPrime

end

/-! ## M1TwistScaled -/

section

open ArithmeticFunction
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem twisted_mangoldt_mellin_coeff_summable
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t : ℝ) (hN : 0 < N) (hσ : 0 < σ) :
    Summable (fun n : ℕ =>
      ‖LSeries.term
        ((fun k : ℕ => χ (k : ZMod q)) *
          (fun k : ℕ => (Λ k : ℂ)))
        ((1:ℂ)-(t:ℂ)*Complex.I) (n+1)‖ *
        (((n+1:ℕ):ℝ)/N)^(-σ)) := by
  let z : ℂ := ((1+σ:ℝ):ℂ)-(t:ℂ)*Complex.I
  have hz : 1 < z.re := by
    dsimp [z]
    simp
    linarith
  have hconv := twisted_mangoldt_lseries_norm_shift q χ z hz
  have hScaled := Summable.mul_left (N^σ) hconv
  exact hScaled.congr (fun n =>
    (lseries_source_weight_norm_scale
      ((fun k : ℕ => χ (k : ZMod q)) * (fun k : ℕ => (Λ k : ℂ)))
      n N σ t hN).symm)
end Green64Analytic.LongPrime

end

/-! ## M1SourceTwistExchange -/

section

open ArithmeticFunction
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem source_twisted_mangoldt_mellin_exchange
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t : ℝ) (F : ℂ → ℂ)
    (hN : 0 < N) (hσ : 0 < σ)
    (hV : Complex.VerticalIntegrable F σ) :
    let c : ℕ → ℂ := fun n => LSeries.term
      ((fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ)))
      ((1:ℂ)-(t:ℂ)*Complex.I) (n+1)
    (∑' n : ℕ, ∫ y : ℝ,
      (c n * (((n+1:ℕ):ℝ)/N:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I)) =
    ∫ y : ℝ, ∑' n : ℕ,
      (c n * (((n+1:ℕ):ℝ)/N:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  let c : ℕ → ℂ := fun n => LSeries.term
    ((fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ)))
    ((1:ℂ)-(t:ℂ)*Complex.I) (n+1)
  have hc : Summable (fun n : ℕ =>
      ‖c n‖ * (((n+1:ℕ):ℝ)/N)^(-σ)) := by
    exact twisted_mangoldt_mellin_coeff_summable q χ N σ t hN hσ
  exact shifted_natural_mellin_exchange N σ c F hN hV hc
end Green64Analytic.LongPrime

end

/-! ## M1TwistedSeries -/

section

open ArithmeticFunction
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_twisted_mangoldt_scaled_series
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t y : ℝ) (hN : 0 < N) (hσ : 0 < σ) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
      (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
        (N:ℂ)^z * LSeries f (s₀+z) := by
  let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
    (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hs : 1 < (s₀+z).re := by
    dsimp [s₀,z]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hf : LSeriesSummable f (s₀+z) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  exact lseries_scaled_shift_tsum f N z s₀ hN hf
end Green64Analytic.LongPrime

end

/-! ## M1ActualPointwise -/

section

open ArithmeticFunction
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_twisted_mangoldt_pointwise
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t y : ℝ) (hN : 0 < N) (hσ : 0 < σ) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
      (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
        (N:ℂ)^z * (-(deriv (DirichletCharacter.LFunction χ) (s₀+z)) /
                      DirichletCharacter.LFunction χ (s₀+z)) := by
  let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
    (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hs : 1 < (s₀+z).re := by
    dsimp [s₀,z]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  calc
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
      (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
        (N:ℂ)^z * LSeries f (s₀+z) :=
      actual_twisted_mangoldt_scaled_series q χ N σ t y hN hσ
    _ = (N:ℂ)^z * (-(deriv (DirichletCharacter.LFunction χ) (s₀+z)) /
           DirichletCharacter.LFunction χ (s₀+z)) := by
      rw [actual_continued_twist_vonMangoldt q χ (s₀+z) hs]
end Green64Analytic.LongPrime

end

/-! ## M1ActualIntegral -/

section

open ArithmeticFunction MeasureTheory
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem source_twisted_mangoldt_actual_integral
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t : ℝ) (F : ℂ → ℂ)
    (hN : 0 < N) (hσ : 0 < σ)
    (hV : Complex.VerticalIntegrable F σ) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    (∑' n : ℕ, ∫ y : ℝ,
      (LSeries.term f s₀ (n+1) *
       (((n+1:ℕ):ℝ)/N:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I)) =
    ∫ y : ℝ, (N:ℂ)^((σ:ℂ)+(y:ℂ)*Complex.I) *
      (-(deriv (DirichletCharacter.LFunction χ)
          (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) /
          DirichletCharacter.LFunction χ
          (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) *
       F ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
    (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  have hs := source_twisted_mangoldt_mellin_exchange
    q χ N σ t F hN hσ hV
  dsimp only [f, s₀] at *
  rw [hs]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hp := actual_twisted_mangoldt_pointwise q χ N σ t y hN hσ
  change (∑' n : ℕ, LSeries.term f s₀ (n+1) *
       (((((n+1:ℕ):ℝ)/N):ℝ):ℂ)^(-z)) =
    (N:ℂ)^z *
      (-(deriv (DirichletCharacter.LFunction χ) (s₀+z)) /
        DirichletCharacter.LFunction χ (s₀+z)) at hp
  push_cast at hp ⊢
  calc
    (∑' n : ℕ,
      (LSeries.term f s₀ (n+1) *
       (((n+1:ℂ)/(N:ℂ))^(-z))) * F z) =
      (∑' n : ℕ, LSeries.term f s₀ (n+1) *
       (((n+1:ℂ)/(N:ℂ))^(-z))) * F z := by
        rw [tsum_mul_right]
    _ = ((N:ℂ)^z *
       (-(deriv (DirichletCharacter.LFunction χ) (s₀+z)) /
        DirichletCharacter.LFunction χ (s₀+z))) * F z := by
        rw [hp]
end Green64Analytic.LongPrime

end

