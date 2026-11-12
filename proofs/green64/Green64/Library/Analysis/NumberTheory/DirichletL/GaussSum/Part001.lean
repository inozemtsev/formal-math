module

public import Green64.Library.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder -/

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

namespace GaussCRT

theorem gauss_sum_chinese_product (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψm : AddChar (ZMod m) ℂ) (ψn : AddChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
      gaussSum χm ψm * gaussSum χn ψn := by
  let e := (ZMod.chineseRemainder h).toEquiv
  let F : ZMod m × ZMod n → ℂ :=
    fun z => χm z.1 * χn z.2 * ψm z.1 * ψn z.2
  calc
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
        ∑ x : ZMod (m * n), F (e x) := rfl
    _ = ∑ z : ZMod m × ZMod n, F z := Equiv.sum_comp e F
    _ = ∑ z : ZMod m, ∑ w : ZMod n, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χm ψm * gaussSum χn ψn := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

def leftAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (z, 0))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (z + w, 0)) =
      ψ ((ZMod.chineseRemainder h).symm (z, 0)) *
        ψ ((ZMod.chineseRemainder h).symm (w, 0))
    rw [show (z + w, (0 : ZMod n)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (0, z))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (0, z + w)) =
      ψ ((ZMod.chineseRemainder h).symm (0, z)) *
        ψ ((ZMod.chineseRemainder h).symm (0, w))
    rw [show ((0 : ZMod m), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (x : ZMod (m * n)) :
    ψ x =
      leftAddChar m n h ψ ((ZMod.chineseRemainder h x).1) *
      rightAddChar m n h ψ ((ZMod.chineseRemainder h x).2) := by
  let z := ZMod.chineseRemainder h x
  have hz : (z.1, (0 : ZMod n)) + ((0 : ZMod m), z.2) = z := by
    ext <;> simp
  calc
    ψ x = ψ ((ZMod.chineseRemainder h).symm z) := by simp [z]
    _ = ψ ((ZMod.chineseRemainder h).symm (z.1, 0) +
          (ZMod.chineseRemainder h).symm (0, z.2)) := by
          rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) * ψ x) =
      gaussSum χm (leftAddChar m n h ψ) *
      gaussSum χn (rightAddChar m n h ψ) := by
  simp_rw [addChar_crt_factor m n h ψ]
  convert gauss_sum_chinese_product m n h χm χn
    (leftAddChar m n h ψ) (rightAddChar m n h ψ) using 1 ;
      congr 1 ; ext x ; ring

theorem crt_left_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    (ZMod.chineseRemainder h).symm (z, 0) =
      ((n * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (n * r * z.val)]
    simp only [ Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod m) n r, hr, one_mul,
      ZMod.natCast_zmod_val]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (n * r * z.val)]
    simp [Nat.cast_mul]

theorem leftAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := m)) ((r : ZMod m) * z) := by
  have hleft :
      leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((n * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (z, 0)) = _
    rw [crt_left_axis m n r h hr z]
  have hz : ((r : ZMod m) * z) = ((r * z.val : ℕ) : ZMod m) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hleft, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (n * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := m) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem crt_right_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    (ZMod.chineseRemainder h).symm (0, z) =
      ((m * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (m * r * z.val)]
    simp [Nat.cast_mul]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (m * r * z.val)]
    simp only [Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod n) m r, hr, one_mul,
      ZMod.natCast_zmod_val]

theorem rightAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := n)) ((r : ZMod n) * z) := by
  have hright :
      rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((m * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (0, z)) = _
    rw [crt_right_axis m n r h hr z]
  have hz : ((r : ZMod n) * z) = ((r * z.val : ℕ) : ZMod n) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hright, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (m * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := n) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem gauss_shift_cross (m n r : ℕ) [NeZero m]
    (χ : MulChar (ZMod m) ℂ)
    (hr : ((n * r : ℕ) : ZMod m) = 1) :
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  have hrprod : (n : ZMod m) * (r : ZMod m) = 1 := by
    simpa only [Nat.cast_mul] using hr
  have hur : IsUnit (r : ZMod m) :=
    IsUnit.of_mul_eq_one_right (n : ZMod m) hrprod
  have hcharprod : χ (n : ZMod m) * χ (r : ZMod m) = 1 := by
    rw [← map_mul, hrprod, map_one]
  have hshift := gaussSum_mulShift χ (ZMod.stdAddChar (N := m)) hur.unit
  have hshift' : χ (r : ZMod m) *
      gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      gaussSum χ (ZMod.stdAddChar (N := m)) := by
    simpa only [hur.unit_spec] using hshift
  calc
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
        (χ (n : ZMod m) * χ (r : ZMod m)) *
          gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) := by
            rw [hcharprod, one_mul]
    _ = χ (n : ZMod m) *
          (χ (r : ZMod m) *
            gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m))) := by ring
    _ = χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by rw [hshift']

theorem gauss_sum_crt_standard (m n r s : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n)
    (hr : ((n * r : ℕ) : ZMod m) = 1)
    (hs : ((m * s : ℕ) : ZMod n) = 1)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      (ZMod.stdAddChar (N := m * n)) x) =
      χm (n : ZMod m) * χn (m : ZMod n) *
        gaussSum χm (ZMod.stdAddChar (N := m)) *
        gaussSum χn (ZMod.stdAddChar (N := n)) := by
  have hleft : leftAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := m)).mulShift (r : ZMod m) := by
    ext z
    exact leftAddChar_std_apply m n r h hr z
  have hright : rightAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := n)).mulShift (s : ZMod n) := by
    ext z
    exact rightAddChar_std_apply m n s h hs z
  rw [gauss_sum_crt m n h χm χn (ZMod.stdAddChar (N := m * n)),
      hleft, hright,
      gauss_shift_cross m n r χm hr,
      gauss_shift_cross n m s χn hs]
  ring

end GaussCRT

open scoped Classical

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    rw [sub_add_cancel] at h
    rw [hper _ hsub, one_mul] at h
    exact h)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

@[simp] theorem quotientAddChar_mk {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) (a : A) :
    quotientAddChar I ψ hper (Ideal.Quotient.mk I a) = ψ a := rfl

theorem principal_coprime_of_bezout {A : Type*} [CommRing A]
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert hxy using 1; ring

theorem crt_left_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    calc
      x - x * v * b = x * (u * a + v * b) - x * v * b := by rw [hbez]; ring
      _ = a * (x * u) := by ring
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨x * v, by ring⟩

theorem crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring

noncomputable def rawTraceChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A) : AddChar A ℂ where
  toFun x := ψ (ι x / (ι c * lam))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, add_div, AddChar.map_add_eq_mul]

theorem rawTraceChar_period {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (x : A) (hx : x ∈ Ideal.span {c}) :
    rawTraceChar ι ψ lam c x = 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy]
  change ψ (ι (c * y) / (ι c * lam)) = 1
  rw [map_mul]
  have hfrac : ι c * ι y / (ι c * lam) = ι y / lam := by
    field_simp
  rw [hfrac]
  exact hbase y

noncomputable def traceModChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ Ideal.span {c}) ℂ :=
  quotientAddChar (Ideal.span {c}) (rawTraceChar ι ψ lam c)
    (rawTraceChar_period ι ψ lam c hc hlam hbase)

@[simp] theorem traceModChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceModChar ι ψ lam c hc hlam hbase
      (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ψ (ι x / (ι c * lam)) := rfl

noncomputable def traceProdChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  quotientAddChar ((Ideal.span {a}) * (Ideal.span {b}))
    (rawTraceChar ι ψ lam (a * b)) (by
      intro x hx
      have hx' : x ∈ Ideal.span {a * b} := by
        simpa only [Ideal.span_singleton_mul_span_singleton] using hx
      exact rawTraceChar_period ι ψ lam (a * b)
        (by simpa only [map_mul] using mul_ne_zero ha hb)
        hlam hbase x hx')

@[simp] theorem traceProdChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceProdChar ι ψ lam a b ha hb hlam hbase
      (Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) x) =
      ψ (ι x / (ι (a * b) * lam)) := rfl

theorem leftAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem rightAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem bezout_inverse_left {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {a}) b) *
      (Ideal.Quotient.mk (Ideal.span {a}) v) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change b * v - 1 ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  refine ⟨-u, ?_⟩
  calc
    b * v - 1 = b * v - (u * a + v * b) := by rw [hbez]
    _ = a * -u := by ring

theorem bezout_inverse_right {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  calc
    a * u - 1 = a * u - (u * a + v * b) := by rw [hbez]
    _ = b * -v := by ring

theorem gauss_shift_bezout_left {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {a}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']

theorem gauss_shift_bezout_right {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {b})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {b}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {b}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u)) =
      χ (Ideal.Quotient.mk (Ideal.span {b}) a) * gaussSum χ ψ := by
  let ma := Ideal.Quotient.mk (Ideal.span {b}) a
  let mu := Ideal.Quotient.mk (Ideal.span {b}) u
  have hprod : ma * mu = 1 := bezout_inverse_right hbez
  have hu : IsUnit mu := IsUnit.of_mul_eq_one_right ma hprod
  have hχ : χ ma * χ mu = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mu * gaussSum χ (ψ.mulShift mu) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mu) =
        (χ ma * χ mu) * gaussSum χ (ψ.mulShift mu) := by rw [hχ, one_mul]
    _ = χ ma * (χ mu * gaussSum χ (ψ.mulShift mu)) := by ring
    _ = χ ma * gaussSum χ ψ := by rw [hshift']

theorem gauss_sum_trace_crt {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  let e := Ideal.quotientMulEquivQuotientProd (Ideal.span {a})
    (Ideal.span {b}) (principal_coprime_of_bezout hbez)
  have h := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez) χa χb
    (traceProdChar ι ψ lam a b ha hb hlam hbase)
  rw [leftAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      rightAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      gauss_shift_bezout_left hbez χa (traceModChar ι ψ lam a ha hlam hbase),
      gauss_shift_bezout_right hbez χb (traceModChar ι ψ lam b hb hlam hbase)] at h
  calc
    _ = (χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
          gaussSum χa (traceModChar ι ψ lam a ha hlam hbase)) *
        (χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
          gaussSum χb (traceModChar ι ψ lam b hb hlam hbase)) := h
    _ = _ := by ring

theorem gauss_sum_trace_crt_of_coprime {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (a b : A)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  obtain ⟨u, v, hbez⟩ := bezout_of_principal_coprime hcop
  exact gauss_sum_trace_crt ι ψ lam hbez ha hb hlam hbase χa χb

end IdealGaussCRT

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.HeathBrownIteration -/

section

namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end SevenEighths.HeathBrownIteration

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialMarkedReserve -/

section

namespace OAI

namespace SevenEighths.InverseInitialMarkedReserve

theorem exists_reserve (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0<gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤gap/50 ∧
      0<τ ∧ τ≤gap/50 ∧ 0<π ∧ 0<eps ∧ 0<loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤ r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤ r')(hhi:r'≤ r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤ r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end SevenEighths.InverseInitialMarkedReserve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.LogarithmicControl -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hL.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hL hg he, he⟩

theorem exists_holomorphic_log_normalized {L : ℂ → ℂ} {c m : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hm : Complex.exp m = L c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hL h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = L z
  have hez : Complex.exp (g z) = L z := he hz
  have hec : Complex.exp (g c) = L c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

theorem log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq

theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

theorem three_circles {g : ℂ → ℂ} {c z : ℂ} {r R S A B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖g z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) /
      (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  let F : ℂ → ℂ := fun w ↦ g (c + Complex.exp w)
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log r < Real.log R := Real.log_lt_log hr hrR
  have hmap (w : ℂ) (hw : w.re ≤ Real.log R) : c + Complex.exp w ∈ closedBall c R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hRp)
  have hclosed : closure (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hd : DiffContOnCl ℂ F
      (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hm := hmap w (hclosed hw).2
    have hm' : c + Complex.exp w ∈ ball c S :=
      closedBall_subset_ball hRS hm
    exact ((hg _ hm').differentiableAt (isOpen_ball.mem_nhds hm')).comp w
      ((differentiableAt_const c).add (Complex.differentiable_exp w)) |>.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmap w hw.2)
  have hzn : 0 < ‖z - c‖ := hr.trans_le hzr
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzn
  have hw : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧
      (Complex.log (z - c)).re ≤ Real.log R
    simp only [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log hzn hzR⟩
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlog hw hd hbound (a := A) (b := B) ?_ ?_
  · simpa [F, Complex.exp_log hz0, Complex.log_re] using h
  · intro w hw
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hw
    simp [mem_closedBall, dist_eq_norm, hw, Complex.norm_exp, Real.exp_log hr]
  · intro w hw
    exact hb _ (hmap w (le_of_eq hw))

theorem three_circles_power_bound {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring

def uniformTheta (e : ℝ) : ℝ := 1 - Real.log (1 + e) / Real.log (200 / 49)

theorem uniformTheta_mem {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]

theorem three_circles_exponent_uniform {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1

theorem exp_sublinear_le {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))

def outerConstant (e A M : ℝ) : ℝ := (4 * M + 4 * A) / e

theorem outerConstant_ge_one {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith

theorem outer_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 4 * e)) :
    ‖g z‖ ≤ outerConstant e A M * T := by
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hb := borel_caratheodory_closedBall (by linarith : 0 ≤ 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 3 * e) (mul_pos hMp hTp) hAp
    (hg.mono (ball_subset_ball (by linarith))) hRe hc hz
  have hgap : 2 - a - 3 * e - (2 - a - 4 * e) = e := by ring
  rw [hgap] at hb
  have hfirst : 2 * (M * T) * (2 - a - 4 * e) ≤ 4 * M * T := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show 2 - a - 4 * e ≤ 2 by linarith) (show 0 ≤ 2 * M * T by positivity)]
  have hsecond : A * (2 - a - 3 * e + (2 - a - 4 * e)) ≤ 4 * A * T := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 2 - a - 3 * e + (2 - a - 4 * e) ≤ 4 by linarith) hAp
    nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * A by positivity)]
  refine hb.trans ?_
  rw [← add_div]
  unfold outerConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right he).mpr (by nlinarith)

theorem inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))

theorem logarithm_derivative_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith

theorem zero_free_disk_logarithm {L E : ℂ → ℂ} {c : ℂ} {a e A M C : ℝ}
    (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) (hC : 0 < C)
    (hL : DifferentiableOn ℂ L (ball c (2 - a - 2 * e)))
    (h0 : ∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0)
    (hpoly : ∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M)
    (hE : DifferentiableOn ℂ E (ball c (1 / 2)))
    (hEL : EqOn (Complex.exp ∘ E) L (ball c (1 / 2)))
    (hEb : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (2 - a - 2 * e)) ∧
      EqOn (Complex.exp ∘ g) L (ball c (2 - a - 2 * e)) ∧
      (∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A) ∧
      (∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * Real.log C) := by
  have hR : (1 / 2 : ℝ) < 2 - a - 2 * e := by linarith
  obtain ⟨g, hg, hge, hgc⟩ := exists_holomorphic_log_normalized
    (by linarith : 0 < 2 - a - 2 * e) hL h0
    (hEL (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgE : EqOn g E (ball c (1 / 2)) := log_eqOn_of_eq_center (by norm_num)
    (hg.mono (ball_subset_ball hR.le)) hE
    (fun z hz ↦ (hge (ball_subset_ball hR.le hz)).trans (hEL hz).symm) hgc
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro z hz
    rw [hgE (closedBall_subset_ball (by norm_num : (49 / 100 : ℝ) < 1 / 2) hz)]
    exact hEb z hz
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) := ball_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hp := hpoly z hz
    rw [← hez, Complex.norm_exp, Real.rpow_def_of_pos hC] at hp
    simpa [mul_comm] using Real.exp_le_exp.mp hp

theorem logarithmic_derivative_eq {L g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) L U)
    {z : ℂ} (hz : z ∈ U) : deriv L z / L z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : L =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdl := hd.congr_of_eventuallyEq heq
  rw [hdl.deriv]
  have hez : Complex.exp (g z) = L z := he hz
  rw [← hez]
  field_simp

theorem logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz

theorem conductor_height_scale_ge_exp (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]

theorem absorb_polynomial_constant {K p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ C : ℝ, Real.exp 1 ≤ C → K * C ^ p ≤ C ^ M := by
  let J := max 1 K
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  refine ⟨p + Real.log J + 1, by linarith, ?_⟩
  intro C hC
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  have hJC : J ≤ C ^ Real.log J := by
    rw [Real.rpow_def_of_pos hCp, ← Real.exp_log hJp]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    K * C ^ p ≤ J * C ^ p := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hCp.le _)
    _ ≤ C ^ Real.log J * C ^ p := mul_le_mul_of_nonneg_right hJC
      (Real.rpow_nonneg hCp.le _)
    _ = C ^ (p + Real.log J) := by rw [← Real.rpow_add hCp]; congr 1; ring
    _ ≤ C ^ (p + Real.log J + 1) := Real.rpow_le_rpow_of_exponent_le
      ((show (1 : ℝ) ≤ Real.exp 1 by exact Real.one_le_exp (by norm_num)).trans hC)
      (by linarith)

theorem disk_re_gt {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]

theorem same_height_mem_disk {a e t v x : ℝ} (hev : 8 * e ≤ v)
    (hx : a + v ≤ x) (hx' : x ≤ 2) :
    (x : ℂ) + (t : ℂ) * Complex.I ∈
      closedBall (2 + (t : ℂ) * Complex.I) (2 - a - 8 * e) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : (x : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I) =
      ((x - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : x - 2 ≤ 0)]
  linarith

theorem principal_regularizer_norm_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hn : ‖s - 1‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  rw [norm_div]
  exact div_le_one_of_le₀ hn (norm_nonneg _)

theorem principal_reciprocal_transfer {s Z L : ℂ} (hs : 0 ≤ s.re)
    (hL : L = ((s - 1) / (s + 1)) * Z) (h0 : L ≠ 0) : ‖Z⁻¹‖ ≤ ‖L⁻¹‖ := by
  have hf0 : (s - 1) / (s + 1) ≠ 0 := by
    intro hf
    apply h0
    rw [hL, hf, zero_mul]
  have heq : Z⁻¹ = ((s - 1) / (s + 1)) * L⁻¹ := by
    rw [hL, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (principal_regularizer_norm_le_one hs)
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.LogarithmicControl

end

end OAI

end

