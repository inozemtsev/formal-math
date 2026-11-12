module

public import Green64.Library.Weights.ActualSmallHaarJointZero
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Weights / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSmallHaarMarkedMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- True marked SMALL-state carrier is the sum over injective ordered
M-prime lists of the residue torus restricted to zeros at THOSE labels.
The equivalence keeps all slot orderings, with no M! quotient. -/
def sourceOriginalACTUALMarkedZeroEquiv434 (M : ℕ) :
    SmallState modulus M ≃
      Σ f : (Fin M ↪ P),
        {y : SmallTorus modulus // ∀ j : Fin M, y (f j) = 0} where
  toFun x := ⟨⟨x.val.2,x.property.1⟩,⟨x.val.1,x.property.2⟩⟩
  invFun z := ⟨(z.2.val, z.1),⟨z.1.injective,z.2.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    cases z with
    | mk f y =>
      rfl

/-- Any injective ordered marked list has the EXACT expected Haar
zero-coordinate mass equal to the product of reciprocal moduli.
In particular no independence is assumed: it follows from the true
finite product torus and the explicit distinct-mark condition. -/
theorem source_original_ACTUAL_SMALL_haar_injective_marks434
    (M : ℕ) (f : Fin M ↪ P) :
    (∑ y : SmallTorus modulus,
      haarAtomMass modulus *
        (if ∀ j : Fin M, y (f j) = 0 then (1:ℝ) else 0)) =
    ∏ j : Fin M, 1/(modulus (f j):ℝ) := by
  classical
  let F : Finset P :=
    (Finset.univ : Finset (Fin M)).image (fun j => (f j:P))
  have hCond (y : SmallTorus modulus) :
      (∀ p ∈ F, y p = 0) ↔ (∀ j : Fin M, y (f j) = 0) := by
    constructor
    · intro h j
      exact h (f j) (Finset.mem_image.mpr
        ⟨j,Finset.mem_univ _,rfl⟩)
    · intro h p hp
      rcases Finset.mem_image.mp hp with ⟨j,hj,hjval⟩
      rw [←hjval]
      exact h j
  have hHaar := source_original_ACTUAL_SMALL_haar_joint_zero434 modulus F
  have hCondSum :
      (∑ y : SmallTorus modulus, haarAtomMass modulus *
        (if ∀ j : Fin M, y (f j) = 0 then (1:ℝ) else 0)) =
      ∑ y : SmallTorus modulus, haarAtomMass modulus *
        (if ∀ p ∈ F, y p = 0 then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [if_congr (hCond y) rfl rfl]
  rw [hCondSum,hHaar]
  calc
    (∏ p : P, if p ∈ F then 1/(modulus p:ℝ) else 1) =
      ∏ p ∈ F,1/(modulus p:ℝ) := by
        rw [←Finset.prod_filter]
        congr 1
        ext p
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = ∏ j : Fin M,1/(modulus (f j):ℝ) := by
        exact Finset.prod_image (by
          intro i hi j hj hij
          exact f.injective hij)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallHaarFibreMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 15000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Haar mass of the genuine finite FOCK-style fibre of torus
points whose coordinates vanish at a distinct ordered mark list.
No new model: the fibre is literally the source SmallState mark
zero condition. -/
theorem source_original_ACTUAL_SMALL_injective_marks_fibre_mass434
    (M : ℕ) (f : Fin M ↪ P) :
    (∑ y : {y : SmallTorus modulus // ∀ j : Fin M, y (f j)=0},
       haarAtomMass modulus) =
    ∏ j : Fin M, 1/(modulus (f j):ℝ) := by
  classical
  let C : SmallTorus modulus → Prop := fun y => ∀ j : Fin M, y (f j)=0
  let S : Finset (SmallTorus modulus) := Finset.univ.filter C
  have h0 : (Fintype.card {y : SmallTorus modulus // C y}) = S.card := by
    exact Fintype.card_subtype C
  calc
    _ = (Fintype.card {y : SmallTorus modulus // C y}:ℝ) *
        haarAtomMass modulus := by
      dsimp only [C]
      simp
    _ = (S.card:ℝ) * haarAtomMass modulus := by
      change ((Fintype.card {y : SmallTorus modulus // C y}:ℝ) *
        haarAtomMass modulus) = _
      rw [h0]
    _ = ∑ y ∈ S, haarAtomMass modulus := by simp
    _ = ∑ y : SmallTorus modulus,
          haarAtomMass modulus *
            (if C y then (1:ℝ) else 0) := by
        change (∑ y ∈ (Finset.univ : Finset (SmallTorus modulus)).filter C,
          haarAtomMass modulus) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y hy
        change (if C y then haarAtomMass modulus else 0) =
          haarAtomMass modulus*(if C y then (1:ℝ) else 0)
        by_cases h : C y <;> simp [h]
    _ = _ := source_original_ACTUAL_SMALL_haar_injective_marks434
      modulus M f
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallHaarMarkedMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- EXACT true physical SMALL-state Haar/ordered-distinct-mark
mass, expressed as the injective falling-factorial moment of the
original reciprocal moduli. This removes the crude small-alphabet
CARDINALITY bound and uses the same Haar/V^M normalization that
appears in the SOURCE Hilbert space. -/
theorem source_original_ACTUAL_SMALL_state_mass_marked_moment434
    (M : ℕ) (V : ℝ) :
    (∑ x : SmallState modulus M, stateMass modulus M V) =
    (1/V^M) * (∑ f : Fin M ↪ P,
      ∏ j : Fin M,1/(modulus (f j):ℝ)) := by
  classical
  let e := sourceOriginalACTUALMarkedZeroEquiv434 modulus M
  have he := Fintype.sum_equiv e
    (fun _x : SmallState modulus M => stateMass modulus M V)
    (fun _ : Σ f : (Fin M ↪ P),
      {y : SmallTorus modulus // ∀ j : Fin M, y (f j)=0} =>
        haarAtomMass modulus * (1/V^M))
    (by intro x; rfl)
  rw [he,Fintype.sum_sigma]
  calc
    _ = ∑ f : Fin M ↪ P,
      (∑ y : {y : SmallTorus modulus //
        ∀ j : Fin M, y (f j)=0}, haarAtomMass modulus) * (1/V^M) := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [Finset.sum_mul]
    _ = ∑ f : Fin M ↪ P,
      (∏ j : Fin M,1/(modulus (f j):ℝ)) * (1/V^M) := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [source_original_ACTUAL_SMALL_injective_marks_fibre_mass434]
    _ = _ := by
        rw [←Finset.sum_mul]
        ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallHaarHarmonicNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Nonnegative injective ordered M-tuples form a SUBSET of all
independent M-tuples. The exact inverse-modulus moment therefore
costs no extra M! and is at most the Mth power of the harmonic sum. -/
theorem source_original_ACTUAL_SMALL_injective_moment_le_power434
    {P : Type} [Fintype P] [DecidableEq P] (M : ℕ)
    (w : P → ℝ) (hw : ∀ p,0 ≤ w p) :
    (∑ f : Fin M ↪ P, ∏ j : Fin M,w (f j)) ≤
      (∑ p : P,w p)^M := by
  classical
  letI : DecidableEq (Fin M → P) := Classical.decEq _
  let E : Finset (Fin M → P) :=
    (Finset.univ : Finset (Fin M ↪ P)).image
      (fun f => (f : Fin M → P))
  have hinj : Function.Injective (fun f : Fin M ↪ P => (f : Fin M → P)) := by
    intro f g h
    apply Function.Embedding.ext
    intro j
    exact congrArg (fun v : Fin M → P => v j) h
  have hEq : (∑ f : Fin M ↪ P, ∏ j : Fin M,w (f j)) =
      ∑ f ∈ E, ∏ j : Fin M,w (f j) := by
    simpa [E] using (Finset.sum_image
      (s := (Finset.univ : Finset (Fin M ↪ P)))
      (g := fun f : Fin M ↪ P => (f : Fin M → P))
      (f := fun f : Fin M → P => ∏ j : Fin M,w (f j))
      (by intro a ha b hb h; exact hinj h)).symm
  have hSub : (∑ f ∈ E, ∏ j : Fin M,w (f j)) ≤
      ∑ f : Fin M → P, ∏ j : Fin M,w (f j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    intro f hf hnot
    exact Finset.prod_nonneg (fun j _ => hw (f j))
  have hTensor : (∑ f : Fin M → P, ∏ j : Fin M,w (f j)) =
      (∑ p : P,w p)^M := by
    calc
      _ = ∏ _j : Fin M, (∑ p : P,w p) :=
        (Fintype.prod_sum
          (f := fun (_j : Fin M) (p : P) => w p)).symm
      _ = _ := by simp
  exact hEq.trans_le (hSub.trans_eq hTensor)

/-- ORIGINAL finite SMALL Haar/ordered-distinct-mark state mass
is at most ONE under the SOURCE harmonic normalization
V = sum_p 1/modulus(p). This removes the crude exp(sqrt L) prime
alphabet bound, uses the genuine product Haar probability, and
does NOT charge the number of marked lists separately. -/
theorem source_original_ACTUAL_SMALL_state_harmonic_mass_le_one434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (M : ℕ) (V : ℝ) (hVpos : 0 < V)
    (hV : V = ∑ p : P,1/(modulus p:ℝ)) :
    (∑ x : SmallState modulus M,stateMass modulus M V) ≤ 1 := by
  have hw (p : P) : 0 ≤ (1:ℝ)/(modulus p:ℝ) := by
    have hp : 0 < (modulus p:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos (modulus p))
    positivity
  have hMoment := source_original_ACTUAL_SMALL_injective_moment_le_power434
    M (fun p : P => 1/(modulus p:ℝ)) hw
  rw [←hV] at hMoment
  rw [source_original_ACTUAL_SMALL_state_mass_marked_moment434]
  calc
    _ ≤ (1/V^M)*(V^M) :=
      mul_le_mul_of_nonneg_left hMoment
        (by positivity : 0 ≤ (1:ℝ)/V^M)
    _ = 1 := by
      field_simp [ne_of_gt (pow_pos hVpos M)]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalCellLower -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin
/-- A nonempty original free-slot log cell of width at most one has
lower endpoint at least exp(A-1) when every label is at least exp A.
Ordered repeats are allowed; no independence or energy premise enters. -/
theorem source_original_nonempty_cell_lower
    {ι : Type} [DecidableEq ι] (F : Finset ι) (p : ι → ℕ)
    (U A : ℝ) (hF : F.Nonempty) (hp : ∀ i ∈ F, 1 ≤ p i)
    (hmin : ∀ i ∈ F, Real.exp A ≤ (p i:ℝ)) (hU : 0 < U)
    (hcell : Real.log (((∏ i ∈ F, p i : ℕ):ℝ)) ≤ Real.log U+1) :
    Real.exp (A-1) ≤ U := by
  obtain ⟨i,hi⟩ := hF
  have hprod : 1 ≤ (∏ j ∈ F, p j : ℕ) := Finset.one_le_prod hp
  have hdiv : p i ∣ (∏ j ∈ F, p j : ℕ) := Finset.dvd_prod_of_mem p hi
  have hle : p i ≤ (∏ j ∈ F, p j : ℕ) :=
    Nat.le_of_dvd (by omega) hdiv
  have hProdPos : (0:ℝ) < ((∏ j ∈ F, p j : ℕ):ℝ) := by exact_mod_cast (by omega : (0:ℕ) < ∏ j ∈ F, p j)
  have he : Real.exp A ≤ ((∏ j ∈ F, p j : ℕ):ℝ) :=
    (hmin i hi).trans (by exact_mod_cast hle)
  have hlog : A ≤ Real.log (((∏ j ∈ F, p j : ℕ):ℝ)) := by
    have hh := Real.log_le_log (Real.exp_pos A) he
    simpa only [Real.log_exp] using hh
  calc
    Real.exp (A-1) ≤ Real.exp (Real.log U) := Real.exp_le_exp.mpr (by linarith)
    _ = U := Real.exp_log hU
end Green64Analytic.CorrelationMellin

end

/-! ## SourceOriginalChebyshevElementary -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 260000

/-- Rational elementary bounds on the actual logarithm. -/
theorem source_original_log_two_bounds434 :
    (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have hl := Real.log_le_sub_one_of_pos
    (x := (1/2:ℝ)) (by norm_num)
  have hi : Real.log (1/2:ℝ) = -Real.log 2 := by
    convert (Real.log_inv (2:ℝ)) using 1 <;> norm_num
  rw [hi] at hl
  have hu := Real.log_le_sub_one_of_pos
    (x := (2:ℝ)) (by norm_num)
  constructor <;> linarith

theorem source_original_log_four_le_two434 :
    Real.log 4 ≤ 2 := by
  have h := (source_original_log_two_bounds434).2
  have hh : Real.log 4 = 2*Real.log 2 := by
    conv_lhs => rw [show (4:ℝ)=(2:ℝ)^2 by norm_num]
    rw [Real.log_pow]
    norm_num
  linarith

/-- A global elementary bound on logarithmic growth, sufficient
to make Chebyshev geometric-band errors negligible. -/
theorem source_original_log_le_two_sqrt434
    (x : ℝ) (hx : 0 ≤ x) :
    Real.log x ≤ 2*Real.sqrt x := by
  have h := Real.log_le_rpow_div (x := x) (ε := (1/2:ℝ))
    hx (by norm_num)
  rw [←Real.sqrt_eq_rpow] at h
  norm_num at h
  linarith

/-- At real arithmetic scales u≥512 the logarithm of
64u+1 is ≤u. Constants are deliberately very coarse. -/
theorem source_original_log_64u_add_one_le434
    (u : ℝ) (hu : 512 ≤ u) :
    Real.log (64*u+1) ≤ u := by
  have hx : 0 ≤ 64*u+1 := by positivity
  have hs := source_original_log_le_two_sqrt434
    (64*u+1) hx
  have hsq := Real.sq_sqrt hx
  have hroot : 0 ≤ Real.sqrt (64*u+1) :=
    Real.sqrt_nonneg _
  have hpos : 0 ≤ u := by linarith
  have hmult : 0 ≤ u*(u-512) :=
    mul_nonneg hpos (by linarith)
  have hbound : 2*Real.sqrt (64*u+1) ≤ u := by
    nlinarith
  linarith

theorem source_original_log_64u_le_two_log434
    (u : ℝ) (hu : 512 ≤ u) :
    Real.log (64*u) ≤ 2*Real.log u := by
  have hu0 : 0 < u := by linarith
  have h64 : (64:ℝ) ≤ u := by linarith
  have hh : Real.log 64 ≤ Real.log u :=
    Real.log_le_log (by norm_num) h64
  rw [Real.log_mul (by norm_num) (ne_of_gt hu0)]
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalChebyshevGeometricPositive -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 230000

/-- At every actual sufficiently large real scale u>=512,
the explicit Chebyshev lower prime-counting expression on
(u,64u] is POSITIVE, with a uniform reciprocal-log lower bound.
No PNT or Mertens import. This uses only proven explicit
Mathlib Chebyshev constants and elementary real logs. -/
theorem source_original_64block_chebyshev_positive434
    (u : ℝ) (hu : 512 ≤ u) :
    (1:ℝ)/(16*Real.log u) ≤
      (((64*u)*Real.log 2 - Real.log (64*u+1)) /
          Real.log (64*u) -
        (Real.log 4*u / Real.log (Real.sqrt u) +
          Real.sqrt u)) / (64*u) := by
  have hu0 : 0 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogv : 0 < Real.log (64*u) :=
    Real.log_pos (by nlinarith)
  have hden := source_original_log_64u_le_two_log434 u hu
  have hlog2 := (source_original_log_two_bounds434).1
  have hlog4 := source_original_log_four_le_two434
  have hlogsmall := source_original_log_64u_add_one_le434 u hu
  have hmul2 : 64*u*(1/2:ℝ) ≤ 64*u*Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hnum : 31*u ≤
      64*u*Real.log 2 - Real.log (64*u+1) := by
    linarith
  have hlow :
      31*u/(2*Real.log u) ≤
      (64*u*Real.log 2 - Real.log (64*u+1)) /
        Real.log (64*u) := by
    apply (div_le_div_iff₀ (by positivity) hlogv).2
    calc
      31*u*Real.log (64*u) ≤ 31*u*(2*Real.log u) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ (64*u*Real.log 2 - Real.log (64*u+1)) *
            (2*Real.log u) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
  have hlogroot := Real.log_sqrt (le_of_lt hu0)
  have hlogupper :
      (Real.log 4*u)/Real.log (Real.sqrt u) ≤
        4*u/Real.log u := by
    rw [hlogroot]
    apply (div_le_div_iff₀ (by positivity) hlogu).2
    have hmul4 : Real.log 4*u ≤ 2*u :=
      mul_le_mul_of_nonneg_right hlog4 hu0.le
    have hh := mul_le_mul_of_nonneg_right hmul4 hlogu.le
    linarith
  have hsqrtu : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsq : (Real.sqrt u)^2=u :=
    Real.sq_sqrt hu0.le
  have hlogsqrt := source_original_log_le_two_sqrt434 u hu0.le
  have hrootbound : Real.sqrt u ≤ 2*u/Real.log u := by
    apply (le_div_iff₀ hlogu).2
    calc
      Real.sqrt u * Real.log u ≤
          Real.sqrt u * (2*Real.sqrt u) :=
        mul_le_mul_of_nonneg_left hlogsqrt hsqrtu
      _ = 2*(Real.sqrt u)^2 := by ring
      _ = 2*u := by rw [hsq]
  have hupper :
      Real.log 4*u / Real.log (Real.sqrt u) + Real.sqrt u ≤
        6*u/Real.log u := by
    calc
      _ ≤ 4*u/Real.log u + Real.sqrt u :=
        add_le_add_left hlogupper _
      _ ≤ 4*u/Real.log u + 2*u/Real.log u :=
        add_le_add_right hrootbound _
      _ = _ := by ring
  have hscale :
      (4*u)/Real.log u ≤ (19*u)/(2*Real.log u) := by
    apply (div_le_div_iff₀ hlogu (by positivity)).2
    have hh := mul_nonneg hu0.le hlogu.le
    linarith
  have hident :
      31*u/(2*Real.log u) - 6*u/Real.log u =
        (19*u)/(2*Real.log u) := by
    field_simp [ne_of_gt hlogu]
    ring
  have hdiff : (4*u)/Real.log u ≤
      (64*u*Real.log 2 - Real.log (64*u+1)) /
          Real.log (64*u) -
        (Real.log 4*u / Real.log (Real.sqrt u) +
          Real.sqrt u) := by
    calc
      _ ≤ (19*u)/(2*Real.log u) := hscale
      _ = 31*u/(2*Real.log u) - 6*u/Real.log u :=
        hident.symm
      _ ≤ _ := sub_le_sub hlow hupper
  have hvpos : 0 < 64*u := by positivity
  have hdivide := div_le_div_of_nonneg_right hdiff hvpos.le
  have hsimpl :
      (1:ℝ)/(16*Real.log u) =
      ((4*u)/Real.log u)/(64*u) := by
    field_simp [ne_of_gt hlogu, ne_of_gt hu0]
    ring
  rw [hsimpl]
  exact hdivide
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalFiniteBigProductLongLower -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A TRUE nonempty selected tuple of independently labelled
LONG BIG primes has integer product at least exp(L^c).
This bound does not use the unrelated F1/F2 placeholders of
the previous SOURCE03 formal record, and repeated numerical
primes (at DISTINCT indices) remain legitimate.
The exact nonempty and prime-support lower-bound premises are
visible, and can be discharged from original ν membership
and the manuscript's BIG group interval definitions. -/
theorem source_original_nonempty_selected_BIG_product_lower434
    {I : Type} [Fintype I] (hNonempty : Nonempty I)
    (a : I → ℕ) (L c : ℝ)
    (hL : 0 ≤ L)
    (hMin : ∀ i : I, Real.exp (L^c) ≤ (a i:ℝ)) :
    Real.exp (L^c) ≤ ((∏ i : I, a i:ℕ):ℝ) := by
  classical
  let i0 : I := Classical.choice hNonempty
  have hExpo : 0 ≤ L^c :=
    Real.rpow_nonneg hL _
  have hOneExp : (1:ℝ) ≤ Real.exp (L^c) := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hExpo)
  have hUnit (i : I) : (1:ℝ) ≤ (a i:ℝ) :=
    hOneExp.trans (hMin i)
  have hUnitNat (i : I) : 1 ≤ a i := by
    exact_mod_cast hUnit i
  have hOneFactor : a i0 ≤ ∏ i : I, a i :=
    Finset.single_le_prod
      (s := (Finset.univ : Finset I))
      (f := a)
      (by intro i hi; exact hUnitNat i)
      (Finset.mem_univ i0)
  calc
    _ ≤ (a i0:ℝ) := hMin i0
    _ ≤ ((∏ i : I, a i:ℕ):ℝ) := by exact_mod_cast hOneFactor
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteConditionalFrameL1 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- True conditional finite character-frame L¹ bound.
Even if the retained cell probability nu is tiny, the
normalization ν⁻¹ cancels its *actual physical mass*:
 E_D |K(D,X)| ≤ card(characters),
for any X in the selected cell, provided |χ|≤1. 
This controls arbitrary state-dependent slow-phase perturbations
after multiplying by a small pointwise factor. It does not
assume SW or independence of an arbitrary function H(D). -/
theorem source_original_finite_conditional_frame_L1_bound434
    {X C : Type} [Fintype X] [Fintype C]
    (w : X → ℝ) (hw : ∀ q, 0 ≤ w q)
    (chi : X → C → ℂ)
    (hchi : ∀ q c, ‖chi q c‖ ≤ 1)
    (gate : X → Prop) (nu : ℝ)
    (hnu : 0 < nu)
    (hmass : nu = ∑ q : X, (if gate q then w q else 0))
    (p : X) (hp : gate p) :
    (∑ q : X, w q *
      ‖(if gate q ∧ gate p then
        (nu:ℂ)⁻¹ *
          (∑ c : C, star (chi q c)*chi p c)
        else 0)‖) ≤
      (Fintype.card C:ℝ) := by
  classical
  have hNuInv : (0:ℝ) ≤ nu⁻¹ := (inv_pos.mpr hnu).le
  have hchar (q : X) :
      ‖∑ c : C, star (chi q c)*chi p c‖ ≤
      (Fintype.card C:ℝ) := by
    calc
      _ ≤ ∑ c : C, ‖star (chi q c)*chi p c‖ := norm_sum_le _ _
      _ ≤ ∑ _c : C, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [norm_mul,norm_star]
        have hmul := mul_le_mul (hchi q c) (hchi p c)
          (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        simpa only [one_mul] using hmul
      _ = (Fintype.card C:ℝ) := by simp
  have hpoint (q : X) :
      w q * ‖(if gate q ∧ gate p then
          (nu:ℂ)⁻¹ * (∑ c : C, star (chi q c)*chi p c)
        else 0)‖ ≤
        (if gate q then w q else 0)*((Fintype.card C:ℝ)/nu) := by
    by_cases hq : gate q
    · simp only [hq,hp,and_self,and_true,if_pos]
      rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos hnu]
      have hv : nu⁻¹ * ‖∑ c : C, star (chi q c)*chi p c‖ ≤
          (Fintype.card C:ℝ)/nu := by
        calc
          _ ≤ nu⁻¹*(Fintype.card C:ℝ) :=
            mul_le_mul_of_nonneg_left (hchar q) hNuInv
          _ = (Fintype.card C:ℝ)/nu := by ring
      exact mul_le_mul_of_nonneg_left hv (hw q)
    · simp [hq]
  calc
    _ ≤ ∑ q : X, (if gate q then w q else 0)*
      ((Fintype.card C:ℝ)/nu) :=
        Finset.sum_le_sum (fun q hq => hpoint q)
    _ = (∑ q : X, if gate q then w q else 0)*
        ((Fintype.card C:ℝ)/nu) := by
          rw [Finset.sum_mul]
    _ = nu*((Fintype.card C:ℝ)/nu) := by rw [←hmass]
    _ = (Fintype.card C:ℝ) := by
      field_simp [ne_of_gt hnu]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDiscardedCellMass -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The true TOTAL mass of dropped cells is bounded by
the number of possible cells times the ORIGINAL retention
threshold. Works with arbitrary finite physical states
and arbitrary weights, without treating a small-probability
event as a small L² restriction operator. Crucially, the
cell index is a function of the ACTUAL state, and the candidate
family contains all realizable indices. -/
theorem source_original_finite_discarded_cell_mass_le434
    {X J : Type} [DecidableEq J]
    (states : Finset X) (candidate : Finset J)
    (idx : X → J) (mass : X → ℝ)
    (hCandidate : ∀ x ∈ states, idx x ∈ candidate)
    (xi : ℝ) (hxi : 0 ≤ xi) :
    let cellMass : J → ℝ := fun j =>
      ∑ x ∈ states, if idx x=j then mass x else 0
    let retained : Finset J :=
      candidate.filter (fun j => xi ≤ cellMass j)
    (∑ x ∈ states,
      if idx x ∈ retained then 0 else mass x) ≤
      (candidate.card:ℝ)*xi := by
  classical
  let cellMass : J → ℝ := fun j =>
    ∑ x ∈ states, if idx x=j then mass x else 0
  let retained : Finset J :=
    candidate.filter (fun j => xi ≤ cellMass j)
  let discarded : Finset J :=
    candidate.filter (fun j => ¬xi ≤ cellMass j)
  have hComplement (x : X) (hx : x ∈ states) :
      idx x ∈ discarded ↔ idx x ∉ retained := by
    simp only [discarded,retained,Finset.mem_filter,hCandidate x hx,
      true_and]
  have hPick (x : X) :
      (∑ j ∈ discarded, if idx x=j then mass x else 0) =
      if idx x ∈ discarded then mass x else 0 := by
    by_cases hc : idx x ∈ discarded
    · simp [hc]
    · simp [hc]
  have hDrop (x : X) (hx : x ∈ states) :
      (if idx x ∈ retained then 0 else mass x) =
      ∑ j ∈ discarded, if idx x=j then mass x else 0 := by
    rw [hPick]
    by_cases hkeep : idx x ∈ retained
    · have hbad : idx x ∉ discarded := by
        intro hbad
        exact (hComplement x hx).mp hbad hkeep
      simp [hkeep,hbad]
    · have hbad : idx x ∈ discarded :=
        (hComplement x hx).mpr hkeep
      simp [hkeep,hbad]
  have hRewrite :
      (∑ x ∈ states, if idx x ∈ retained then 0 else mass x) =
      ∑ j ∈ discarded, cellMass j := by
    calc
      _ = ∑ x ∈ states,
          ∑ j ∈ discarded, if idx x=j then mass x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hDrop x hx
      _ = ∑ j ∈ discarded,
          ∑ x ∈ states, if idx x=j then mass x else 0 :=
        Finset.sum_comm
      _ = ∑ j ∈ discarded, cellMass j := rfl
  have hBound (j : J) (hj : j ∈ discarded) :
      cellMass j ≤ xi := by
    exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2)
  calc
    _ = ∑ j ∈ discarded, cellMass j := hRewrite
    _ ≤ ∑ _j ∈ discarded, xi :=
      Finset.sum_le_sum (fun j hj => hBound j hj)
    _ = (discarded.card:ℝ)*xi := by simp
    _ ≤ (candidate.card:ℝ)*xi := by
      apply mul_le_mul_of_nonneg_right _ hxi
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset _ _)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact additive decomposition into GENUINELY attainable
dyadic product-log index fibers. A dyad is a partition
of physical states, not an assumption on the test.
The statement allows any dependent finite physical state type
and arbitrary complex signed summand; it incurs NO dyad-count
factor until the separate quantitative Cauchy–Schwarz bound. -/
theorem source_original_finite_dyad_partition_sum434
    {X I : Type} [Fintype X] [DecidableEq I]
    (candidate : Finset I) (dyad : X → I)
    (hCoverage : ∀ x, dyad x ∈ candidate)
    (z : X → ℂ) :
    (∑ i ∈ candidate, ∑ x : X,
      if dyad x = i then z x else 0) =
    ∑ x : X, z x := by
  classical
  calc
    _ = ∑ x : X, ∑ i ∈ candidate,
        if dyad x = i then z x else 0 :=
      Finset.sum_comm
    _ = ∑ x : X, z x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hCoverage x]

/-- The original physical weighted L² energy splits
EXACTLY over its attainable product dyads, without an
error budget, independent-test restriction or multiplicative
dyad-cardinality loss. -/
theorem source_original_finite_dyad_energy_partition434
    {X I : Type} [Fintype X] [DecidableEq I]
    (candidate : Finset I) (dyad : X → I)
    (hCoverage : ∀ x, dyad x ∈ candidate)
    (w : X → ℝ) (f : X → ℂ) :
    (∑ i ∈ candidate, ∑ x : X,
      if dyad x = i then w x*‖f x‖^2 else 0) =
    ∑ x : X, w x*‖f x‖^2 := by
  classical
  calc
    _ = ∑ x : X, ∑ i ∈ candidate,
        if dyad x = i then w x*‖f x‖^2 else 0 :=
      Finset.sum_comm
    _ = ∑ x : X, w x*‖f x‖^2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hCoverage x]

/-- The true two-ended SOURCE03 signed bilinear form can be
expanded exactly into every product-dyad PAIR, with both
dyadic masks attached to the source/target physical endpoint.
No assumption of factorization of the signed kernel
or independence of the arbitrary complex endpoint tests. -/
theorem source_original_finite_two_ended_dyad_partition434
    {X Y I J : Type}
    [Fintype X] [Fintype Y] [DecidableEq I] [DecidableEq J]
    (candidateX : Finset I) (candidateY : Finset J)
    (dyadX : X → I) (dyadY : Y → J)
    (hX : ∀ x, dyadX x ∈ candidateX)
    (hY : ∀ y, dyadY y ∈ candidateY)
    (z : X × Y → ℂ) :
    (∑ ij ∈ candidateX.product candidateY,
       ∑ xy : X × Y,
         if dyadX xy.1 = ij.1 ∧ dyadY xy.2 = ij.2
         then z xy else 0) =
    ∑ xy : X × Y, z xy := by
  classical
  calc
    _ = ∑ xy : X × Y,
      ∑ ij ∈ candidateX.product candidateY,
        if dyadX xy.1 = ij.1 ∧ dyadY xy.2 = ij.2
        then z xy else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro xy hxy
      have hMem :
          (dyadX xy.1, dyadY xy.2) ∈
            candidateX.product candidateY :=
        Finset.mem_product.mpr ⟨hX xy.1, hY xy.2⟩
      calc
        _ = ∑ ij ∈ candidateX.product candidateY,
            if (dyadX xy.1, dyadY xy.2) = ij
            then z xy else 0 := by
              apply Finset.sum_congr rfl
              intro ij hij
              cases ij with
              | mk a b => simp only [Prod.mk.injEq]
        _ = z xy := by
          rw [Finset.product_eq_sprod, Finset.sum_product]
          have inner (i : I) :
              (∑ j ∈ candidateY,
                if (dyadX xy.1,dyadY xy.2) = (i,j)
                then z xy else 0) =
              (if dyadX xy.1 = i then z xy else 0) := by
            simp only [Prod.mk.injEq]
            by_cases hi : dyadX xy.1 = i
            · simp only [hi, true_and, ite_true]
              exact Finset.sum_ite_eq_of_mem
                candidateY (dyadY xy.2) (fun _ => z xy)
                (hY xy.2)
            · simp [hi]
          calc
            _ = ∑ i ∈ candidateX,
                if dyadX xy.1 = i then z xy else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact inner i
            _ = z xy := Finset.sum_ite_eq_of_mem
              candidateX (dyadX xy.1) (fun _ => z xy)
              (hX xy.1)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteAttainableDyadSummation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- An exact quantitative bound for combining source03
physical signed bilinear estimates over an ACTUAL FINITE
set of attainable product dyad pairs. The ℓ² energies
are attached to individual SOURCE and TARGET dyads, not
replaced by a sum of global energy bounds. The only loss
is the TRUE finite candidate pair count. No sign or
character-basis independence is assumed. -/
theorem source_original_finite_attainable_dyad_sum_L2434
    {I J : Type} [DecidableEq I] [DecidableEq J]
    (candI : Finset I) (candJ : Finset J)
    (a : I → ℝ) (b : J → ℝ)
    (z : I × J → ℂ) (eps : ℝ)
    (ha : ∀ i ∈ candI, 0 ≤ a i)
    (hb : ∀ j ∈ candJ, 0 ≤ b j)
    (hEach : ∀ ij ∈ candI.product candJ,
      ‖z ij‖^2 ≤ eps^2*a ij.1*b ij.2) :
    ‖∑ ij ∈ candI.product candJ, z ij‖^2 ≤
      ((candI.product candJ).card:ℝ)*
        eps^2 * (∑ i ∈ candI, a i) *
        (∑ j ∈ candJ, b j) := by
  classical
  let S := candI.product candJ
  have hTriangle : ‖∑ ij ∈ S, z ij‖ ≤
    ∑ ij ∈ S, ‖z ij‖ := norm_sum_le _ _
  have hSquare : ‖∑ ij ∈ S, z ij‖^2 ≤
    (∑ ij ∈ S, ‖z ij‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTriangle 2
  have hCS : (∑ ij ∈ S, ‖z ij‖)^2 ≤
      (S.card:ℝ)*(∑ ij ∈ S, ‖z ij‖^2) := by
    have hCS0 := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun _ => (1:ℝ)) (fun ij => ‖z ij‖)
    simpa only [one_mul,one_pow,Finset.sum_const,
      nsmul_eq_mul,mul_one] using hCS0
  have hTensor :
      (∑ ij ∈ S, a ij.1*b ij.2) =
       (∑ i ∈ candI, a i)*(∑ j ∈ candJ, b j) := by
    dsimp [S]
    rw [Finset.sum_product]
    calc
      _ = ∑ i ∈ candI, a i*(∑ j ∈ candJ, b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = (∑ i ∈ candI, a i)*(∑ j ∈ candJ, b j) := by
        rw [Finset.sum_mul]
  have hBound :
      (∑ ij ∈ S, ‖z ij‖^2) ≤
      eps^2*(∑ i ∈ candI, a i)*(∑ j ∈ candJ,b j) := by
    calc
      _ ≤ ∑ ij ∈ S, eps^2*a ij.1*b ij.2 :=
        Finset.sum_le_sum (fun ij hmem => hEach ij hmem)
      _ = eps^2*(∑ ij ∈ S, a ij.1*b ij.2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := by rw [hTensor]; ring
  have hcard : 0 ≤ (S.card:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (∑ ij ∈ S, ‖z ij‖)^2 := hSquare
    _ ≤ (S.card:ℝ)*(∑ ij ∈ S, ‖z ij‖^2) := hCS
    _ ≤ (S.card:ℝ)*
         (eps^2*(∑ i ∈ candI,a i)*(∑ j ∈ candJ,b j)) :=
      mul_le_mul_of_nonneg_left hBound hcard
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicBadMask -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Exact original two-ended dyad mask compatibility: the complement
of the retained product-log cell predicate is exactly the original
discarded-cell predicate at each physical endpoint. This lemma
handles the Boolean masks without unfolding the huge source03
dependent free-slot probability state, so it can be reused in
the true kernel operator estimates. -/
theorem source_original_finite_dyadic_bad_mask434
    {X Y : Type}
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (activeX : X → Prop) (activeY : Y → Prop)
    (badX : X → Prop) (badY : Y → Prop)
    (hX : ∀ x, activeX x ↔ ¬badX x)
    (hY : ∀ y, activeY y ↔ ¬badY y)
    (err : X × Y → ℂ) (ab : X × Y) :
    (if dyadX ab.1 ∧ dyadY ab.2 then
      (if ¬activeX ab.1 ∨ ¬activeY ab.2
       then err ab else 0)
     else 0) =
    (if dyadX ab.1 ∧ dyadY ab.2 then
      (if badX ab.1 ∨ badY ab.2
       then (if badX ab.1 ∨ badY ab.2 then err ab else 0)
       else 0)
     else 0) := by
  classical
  have hGate : (¬activeX ab.1 ∨ ¬activeY ab.2) ↔
      (badX ab.1 ∨ badY ab.2) := by
    rw [hX ab.1, hY ab.2]
    tauto
  by_cases hd : dyadX ab.1 ∧ dyadY ab.2
  · simp only [if_pos hd]
    by_cases hb : badX ab.1 ∨ badY ab.2
    · have hn : ¬activeX ab.1 ∨ ¬activeY ab.2 :=
        hGate.mpr hb
      simp only [if_pos hn, if_pos hb]
    · have hn : ¬(¬activeX ab.1 ∨ ¬activeY ab.2) :=
        fun h => hb (hGate.mp h)
      simp only [if_neg hn, if_neg hb]
  · simp only [if_neg hd]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicGoodGateComm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The SOURCE03 original retained dyad test is exactly the
same finite physical bilinear kernel if its logical predicates
are written as active∧dyad or dyad∧active. This innocuous
equivalence is proved separately to prevent costly expansion
of the enormous dependent ν-mark definitions during C196
Lean elaboration, without changing source/target weights,
arbitrary complex tests, or the original signed error. -/
theorem source_original_finite_dyadic_good_gate_comm434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (H : X × Y → ℂ)
    (dyadX activeX : X → Prop)
    (dyadY activeY : Y → Prop) :
    (∑ xy : X × Y,
      ((wX xy.1*wY xy.2:ℝ):ℂ) * star (f xy.1) * g xy.2 *
      (if (dyadX xy.1 ∧ activeX xy.1) ∧
          (dyadY xy.2 ∧ activeY xy.2)
       then H xy else 0)) =
    (∑ xy : X × Y,
      ((wX xy.1*wY xy.2:ℝ):ℂ) * star (f xy.1) * g xy.2 *
      (if (activeX xy.1 ∧ dyadX xy.1) ∧
          (activeY xy.2 ∧ dyadY xy.2)
       then H xy else 0)) := by
  classical
  apply Finset.sum_congr rfl
  intro xy hxy
  have hPredicate :
      ((dyadX xy.1 ∧ activeX xy.1) ∧
       (dyadY xy.2 ∧ activeY xy.2)) ↔
      ((activeX xy.1 ∧ dyadX xy.1) ∧
       (activeY xy.2 ∧ dyadY xy.2)) := by tauto
  by_cases hGood :
      (dyadX xy.1 ∧ activeX xy.1) ∧
        (dyadY xy.2 ∧ activeY xy.2)
  · have hGood' := hPredicate.mp hGood
    simp only [if_pos hGood,if_pos hGood']
  · have hGood' : ¬((activeX xy.1 ∧ dyadX xy.1) ∧
       (activeY xy.2 ∧ dyadY xy.2)) :=
      fun hh => hGood (hPredicate.mpr hh)
    simp only [if_neg hGood,if_neg hGood']
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicMaskEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Restrict an arbitrary genuine source03 complex endpoint
test to an actual physical product dyad without increasing
its weighted L² energy. This is valid for any finite
nonnegative coordinate-dependent probability law. -/
theorem source_original_finite_gate_restricted_energy_le434
    {X : Type} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f : X → ℂ) (gate : X → Prop) :
    (∑ x : X,
      w x*‖if gate x then f x else 0‖^2) ≤
      ∑ x : X, w x*‖f x‖^2 := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  by_cases hg : gate x
  · simp [hg]
  · simpa [hg] using (mul_nonneg (hw x) (sq_nonneg ‖f x‖))

/-- Dyadic endpoint test restrictions can equivalently be
applied as the Boolean mask on the full TRUE
source/target bilinear kernel. There is no extra
assumption that the tests factor through the product:
gate masks inspect the original physical selected
prime products while f,g remain arbitrary functions
of ALL their endpoint prime marks. -/
theorem source_original_finite_two_ended_gate_mask_identity434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (gateX : X → Prop) (gateY : Y → Prop)
    (H : X × Y → ℂ) :
    (∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (if gateX q.1 then f q.1 else 0) *
        (if gateY q.2 then g q.2 else 0) * H q) =
    (∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if gateX q.1 ∧ gateY q.2 then H q else 0)) := by
  classical
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hx : gateX q.1
  · by_cases hy : gateY q.2
    · simp [hx,hy]
    · simp [hx,hy]
  · simp [hx]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadTestLocalization -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Convert the ORIGINAL per-dyad physical operator estimate
valid for ARBITRARY complex source/target tests into the
stronger bound with only the L² ENERGIES OF THAT DYAD.
No new cancellation hypothesis is introduced: apply the
existing operator estimate to the genuine dyad-restricted
tests f_i, g_j. Crucial for summing signed source03
major/minor arc bounds without multiplying full endpoint
energies by the number of dyads before Cauchy–Schwarz. -/
theorem source_original_finite_dyad_test_localization434
    {X Y I J : Type} [Fintype X] [Fintype Y]
    [DecidableEq I] [DecidableEq J]
    (wX : X → ℝ) (wY : Y → ℝ)
    (idxX : X → I) (idxY : Y → J)
    (i : I) (j : J)
    (f : X → ℂ) (g : Y → ℂ)
    (H : X × Y → ℂ) (eps : ℝ)
    (hOperator : ∀ (ff : X → ℂ) (gg : Y → ℂ),
       ‖(∑ q : X × Y,
           ((wX q.1*wY q.2:ℝ):ℂ) *
             star (ff q.1)*gg q.2*
             (if idxX q.1=i ∧ idxY q.2=j
              then H q else 0))‖^2 ≤
         eps^2*(∑ x : X, wX x*‖ff x‖^2)*
           (∑ y : Y, wY y*‖gg y‖^2)) :
    ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if idxX q.1=i ∧ idxY q.2=j
           then H q else 0))‖^2 ≤
      eps^2*
        (∑ x : X, if idxX x=i then wX x*‖f x‖^2 else 0)*
        (∑ y : Y, if idxY y=j then wY y*‖g y‖^2 else 0) := by
  classical
  let ff : X → ℂ := fun x =>
    if idxX x=i then f x else 0
  let gg : Y → ℂ := fun y =>
    if idxY y=j then g y else 0
  have hE1 :
      (∑ x : X, wX x*‖ff x‖^2) =
      ∑ x : X, if idxX x=i then wX x*‖f x‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : idxX x=i
    · simp [ff,h]
    · simp [ff,h]
  have hE2 :
      (∑ y : Y, wY y*‖gg y‖^2) =
      ∑ y : Y, if idxY y=j then wY y*‖g y‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : idxY y=j
    · simp [gg,h]
    · simp [gg,h]
  have hMask :
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (ff q.1)*gg q.2*
          (if idxX q.1=i ∧ idxY q.2=j
           then H q else 0)) =
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if idxX q.1=i ∧ idxY q.2=j
           then H q else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    by_cases h1 : idxX q.1=i
    · by_cases h2 : idxY q.2=j
      · simp [ff,gg,h1,h2]
      · simp [ff,gg,h1,h2]
    · simp [ff,gg,h1]
  have hBound := hOperator ff gg
  rw [hMask,hE1,hE2] at hBound
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadCutoffToExact -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A physical dyad restriction is stronger than the SOURCE03
major-arc upper cutoff. An operator estimate on the upper
cutoff therefore implies a bound with the EXACT energy of
the selected dyad, for arbitrary complex endpoint tests
and an arbitrary jointly dependent signed phase.
This is a localization lemma, NOT an arithmetic estimate. -/
theorem source_original_finite_dyad_cutoff_to_exact_L2_sq434
    {X Y I J : Type}
    [Fintype X] [Fintype Y] [DecidableEq I] [DecidableEq J]
    (wx : X → ℝ) (wy : Y → ℝ)
    (idxX : X → I) (idxY : Y → J)
    (i : I) (j : J) (cutX : X → Prop) (cutY : Y → Prop)
    (hCutX : ∀ x, idxX x = i → cutX x)
    (hCutY : ∀ y, idxY y = j → cutY y)
    (H : X × Y → ℂ) (eps : ℝ)
    (hOperator : ∀ (ff : X → ℂ) (gg : Y → ℂ),
      ‖(∑ q : X × Y,
        ((wx q.1 * wy q.2 : ℝ):ℂ) *
          star (ff q.1) * gg q.2 *
          (if cutX q.1 ∧ cutY q.2 then H q else 0))‖^2 ≤
        eps^2 * (∑ x : X, wx x * ‖ff x‖^2) *
          (∑ y : Y, wy y * ‖gg y‖^2))
    (f : X → ℂ) (g : Y → ℂ) :
    ‖(∑ q : X × Y,
      ((wx q.1 * wy q.2 : ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if idxX q.1 = i ∧ idxY q.2 = j then H q else 0))‖^2 ≤
      eps^2 *
        (∑ x : X, if idxX x = i then wx x * ‖f x‖^2 else 0) *
        (∑ y : Y, if idxY y = j then wy y * ‖g y‖^2 else 0) := by
  classical
  let ff : X → ℂ := fun x => if idxX x = i then f x else 0
  let gg : Y → ℂ := fun y => if idxY y = j then g y else 0
  have hEx :
      (∑ x : X, wx x * ‖ff x‖^2) =
        ∑ x : X, if idxX x = i then wx x * ‖f x‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hi : idxX x = i
    · simp [ff, hi]
    · simp [ff, hi]
  have hEy :
      (∑ y : Y, wy y * ‖gg y‖^2) =
        ∑ y : Y, if idxY y = j then wy y * ‖g y‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hj : idxY y = j
    · simp [gg, hj]
    · simp [gg, hj]
  have hMask :
      (∑ q : X × Y,
        ((wx q.1 * wy q.2 : ℝ):ℂ) *
          star (ff q.1) * gg q.2 *
          (if cutX q.1 ∧ cutY q.2 then H q else 0)) =
      (∑ q : X × Y,
        ((wx q.1 * wy q.2 : ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if idxX q.1 = i ∧ idxY q.2 = j then H q else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hi : idxX q.1 = i
    · by_cases hj : idxY q.2 = j
      · simp [ff, gg, hi, hj, hCutX q.1 hi, hCutY q.2 hj]
      · simp [ff, gg, hi, hj]
    · simp [ff, gg, hi]
  have hBound := hOperator ff gg
  rw [hMask, hEx, hEy] at hBound
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadOperatorGlobalize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A complete FINITE ANALYTIC dyad globalizer for the original
SOURCE03 signed physical comparison. If a genuinely uniform
per-dyad-pair bilinear operator estimate holds for ALL arbitrary
complex physical endpoint tests, then localize those tests
to that dyad, sum with the true local L² energies, recover
both full weighted energies exactly, and pay only the ACTUAL
number of attainable dyad pairs. The kernel H may be fully
dependent on both physical states and have any sign.
The substantive arithmetic per-dyad bound is EXPLICITLY
a premise, not supplied by this combinatorial lemma. -/
theorem source_original_finite_dyad_operator_globalize434
    {X Y I J : Type}
    [Fintype X] [Fintype Y] [DecidableEq I] [DecidableEq J]
    (candidateX : Finset I) (candidateY : Finset J)
    (idxX : X → I) (idxY : Y → J)
    (hCoverX : ∀ x, idxX x ∈ candidateX)
    (hCoverY : ∀ y, idxY y ∈ candidateY)
    (wx : X → ℝ) (wy : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wx x) (hwY : ∀ y, 0 ≤ wy y)
    (H : X × Y → ℂ) (eps : ℝ)
    (hOperator : ∀ ij ∈ candidateX.product candidateY,
      ∀ (ff : X → ℂ) (gg : Y → ℂ),
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) * star (ff xy.1)*gg xy.2*
          (if idxX xy.1=ij.1 ∧ idxY xy.2=ij.2
           then H xy else 0))‖^2 ≤
      eps^2*(∑ x : X, wx x*‖ff x‖^2)*
        (∑ y : Y, wy y*‖gg y‖^2))
    (f : X → ℂ) (g : Y → ℂ) :
    ‖(∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) * star (f xy.1)*g xy.2*
        H xy)‖^2 ≤
      ((candidateX.product candidateY).card:ℝ)*eps^2*
       (∑ x : X, wx x*‖f x‖^2)*
       (∑ y : Y, wy y*‖g y‖^2) := by
  classical
  let S := candidateX.product candidateY
  let z : X × Y → ℂ := fun xy =>
    ((wx xy.1*wy xy.2:ℝ):ℂ) * star (f xy.1)*g xy.2*H xy
  let es : I → ℝ := fun i =>
    ∑ x : X, if idxX x=i then wx x*‖f x‖^2 else 0
  let et : J → ℝ := fun j =>
    ∑ y : Y, if idxY y=j then wy y*‖g y‖^2 else 0
  let zpair : I × J → ℂ := fun ij =>
    ∑ xy : X × Y,
      if idxX xy.1=ij.1 ∧ idxY xy.2=ij.2
      then z xy else 0
  have hEsNN (i : I) (hi : i ∈ candidateX) :
      0 ≤ es i := by
    dsimp [es]
    apply Finset.sum_nonneg
    intro x hx
    by_cases hix : idxX x=i
    · simp only [if_pos hix]
      exact mul_nonneg (hwX x) (sq_nonneg _)
    · simp only [if_neg hix]
      exact le_refl _
  have hEtNN (j : J) (hj : j ∈ candidateY) :
      0 ≤ et j := by
    dsimp [et]
    apply Finset.sum_nonneg
    intro y hy
    by_cases hjy : idxY y=j
    · simp only [if_pos hjy]
      exact mul_nonneg (hwY y) (sq_nonneg _)
    · simp only [if_neg hjy]
      exact le_refl _
  have hEach (ij : I × J) (hmem : ij ∈ S) :
      ‖zpair ij‖^2 ≤ eps^2*es ij.1*et ij.2 := by
    have hLoc := source_original_finite_dyad_test_localization434
      wx wy idxX idxY ij.1 ij.2 f g H eps
      (hOperator ij hmem)
    have hMask :
        zpair ij =
        ∑ xy : X × Y,
          ((wx xy.1*wy xy.2:ℝ):ℂ)*
            star (f xy.1)*g xy.2*
            (if idxX xy.1=ij.1 ∧ idxY xy.2=ij.2
             then H xy else 0) := by
      apply Finset.sum_congr rfl
      intro xy hxy
      by_cases hh : idxX xy.1=ij.1 ∧ idxY xy.2=ij.2
      · simp [z,hh]
      · simp [z,hh]
    rw [hMask]
    exact hLoc
  have hSum := source_original_finite_attainable_dyad_sum_L2434
    candidateX candidateY es et zpair eps hEsNN hEtNN hEach
  have hPartition := source_original_finite_two_ended_dyad_partition434
    candidateX candidateY idxX idxY hCoverX hCoverY z
  have hEsum := source_original_finite_dyad_energy_partition434
    candidateX idxX hCoverX wx f
  have hEtsum := source_original_finite_dyad_energy_partition434
    candidateY idxY hCoverY wy g
  change ‖∑ xy : X × Y,z xy‖^2 ≤
    (S.card:ℝ)*eps^2*
     (∑ x : X, wx x*‖f x‖^2)*
     (∑ y : Y, wy y*‖g y‖^2)
  calc
    _ = ‖∑ ij ∈ S, zpair ij‖^2 :=
      congrArg (fun v : ℂ => ‖v‖^2) hPartition.symm
    _ ≤ (S.card:ℝ)*eps^2*
        (∑ i ∈ candidateX, es i)*
        (∑ j ∈ candidateY, et j) := hSum
    _ = _ := by rw [hEsum,hEtsum]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFilterDeciderInvariant -/

section

namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Exact source03 full/selected atom support independent of the
choice of Decidable proof for the very same active log-cell
predicate. This prevents a spurious syntactic obstruction
when the arithmetic primitive theorem uses integer-decision
instances and the generic complex L2 combiner uses Classical. -/
theorem source_original_finite_filter_decider_invariant434
    {α : Type} (P : α → Prop) (S : Finset α)
    (d₁ d₂ : DecidablePred P) :
    @Finset.filter α P d₁ S = @Finset.filter α P d₂ S := by
  have heq : d₁ = d₂ := Subsingleton.elim _ _
  rw [heq]

/-- The induced finite real atom-energy is invariant too. -/
theorem source_original_finite_filter_sum_decider_invariant434
    {α : Type} (P : α → Prop) (S : Finset α)
    (d₁ d₂ : DecidablePred P) (f : α → ℝ) :
    (∑ x ∈ @Finset.filter α P d₁ S, f x) =
    (∑ x ∈ @Finset.filter α P d₂ S, f x) := by
  rw [source_original_finite_filter_decider_invariant434 P S d₁ d₂]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFourMatchedDyadMasks -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A genuine finite arithmetic kernel that can be nonzero
only inside TWO DISJOINT source choices and TWO DISJOINT
target choices is the EXACT sum of FOUR masked terms.
No bound, cancellation, factorization or synthetic
probability assumption is introduced; the kernel itself
determines the support, rather than assuming every
physical state is in one of the selected rectangles. -/
theorem source_original_finite_four_matched_dyad_masks434
    {X : Type} [Fintype X]
    (F : X → ℂ) (a0 a1 b0 b1 : X → Prop)
    (hA : ∀ x, F x ≠ 0 → a0 x ∨ a1 x)
    (hB : ∀ x, F x ≠ 0 → b0 x ∨ b1 x)
    (hADisjoint : ∀ x, ¬(a0 x ∧ a1 x))
    (hBDisjoint : ∀ x, ¬(b0 x ∧ b1 x)) :
    (∑ x : X, F x) =
      (∑ x : X, if a0 x ∧ b0 x then F x else 0) +
      (∑ x : X, if a0 x ∧ b1 x then F x else 0) +
      (∑ x : X, if a1 x ∧ b0 x then F x else 0) +
      (∑ x : X, if a1 x ∧ b1 x then F x else 0) := by
  classical
  have hState (x : X) :
      F x =
        (if a0 x ∧ b0 x then F x else 0) +
        (if a0 x ∧ b1 x then F x else 0) +
        (if a1 x ∧ b0 x then F x else 0) +
        (if a1 x ∧ b1 x then F x else 0) := by
    by_cases hZero : F x = 0
    · simp [hZero]
    · by_cases ha : a0 x
      · have hna : ¬a1 x := fun ha1 =>
          hADisjoint x ⟨ha,ha1⟩
        by_cases hb : b0 x
        · have hnb : ¬b1 x := fun hb1 =>
            hBDisjoint x ⟨hb,hb1⟩
          simp [ha,hna,hb,hnb]
        · have hb1 : b1 x := (hB x hZero).resolve_left hb
          simp [ha,hna,hb,hb1]
      · have ha1 : a1 x := (hA x hZero).resolve_left ha
        by_cases hb : b0 x
        · have hnb : ¬b1 x := fun hb1 =>
            hBDisjoint x ⟨hb,hb1⟩
          simp [ha,ha1,hb,hnb]
        · have hb1 : b1 x := (hB x hZero).resolve_left hb
          simp [ha,ha1,hb,hb1]
  calc
    (∑ x : X, F x) =
        ∑ x : X, ((if a0 x ∧ b0 x then F x else 0) +
          (if a0 x ∧ b1 x then F x else 0) +
          (if a1 x ∧ b0 x then F x else 0) +
          (if a1 x ∧ b1 x then F x else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hState x
    _ = _ := by simp only [Finset.sum_add_distrib]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFourOutputWindowExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Genuine finite weighted bilinear OUTPUT prime-atom sum:
when each nonzero source coefficient lies in exactly one of
two disjoint true source windows, and likewise target, the
FULL arbitrary coupled complex phase is the exact sum of
FOUR rectangle-masked terms. No analytic bound, factorization,
or change of weights is assumed. -/
theorem source_original_finite_four_output_window_expansion434
    {I J : Type} (SI : Finset I) (SJ : Finset J)
    (a : I → ℂ) (b : J → ℂ) (phase : I → J → ℂ)
    (A0 A1 : I → Prop) (B0 B1 : J → Prop)
    (hA : ∀ i∈SI, a i ≠ 0 → A0 i ∨ A1 i)
    (hB : ∀ j∈SJ, b j ≠ 0 → B0 j ∨ B1 j)
    (hADisjoint : ∀ i∈SI, ¬(A0 i ∧ A1 i))
    (hBDisjoint : ∀ j∈SJ, ¬(B0 j ∧ B1 j)) :
    (∑ i∈SI, ∑ j∈SJ, a i*b j*phase i j) =
    (∑ i∈SI, ∑ j∈SJ,
      (if A0 i then a i else 0)*
      (if B0 j then b j else 0)*phase i j) +
    (∑ i∈SI, ∑ j∈SJ,
      (if A0 i then a i else 0)*
      (if B1 j then b j else 0)*phase i j) +
    (∑ i∈SI, ∑ j∈SJ,
      (if A1 i then a i else 0)*
      (if B0 j then b j else 0)*phase i j) +
    (∑ i∈SI, ∑ j∈SJ,
      (if A1 i then a i else 0)*
      (if B1 j then b j else 0)*phase i j) := by
  classical
  have hCutA (i : I) (hi : i∈SI) :
      a i = (if A0 i then a i else 0) +
        (if A1 i then a i else 0) := by
    by_cases h0 : A0 i
    · have h1 : ¬A1 i :=
        fun h => hADisjoint i hi ⟨h0,h⟩
      simp [h0,h1]
    · by_cases h1 : A1 i
      · simp [h0,h1]
      · have hZero : a i = 0 := by
          by_contra hNonzero
          rcases hA i hi hNonzero with hh | hh
          · exact h0 hh
          · exact h1 hh
        simp [h0,h1,hZero]
  have hCutB (j : J) (hj : j∈SJ) :
      b j = (if B0 j then b j else 0) +
        (if B1 j then b j else 0) := by
    by_cases h0 : B0 j
    · have h1 : ¬B1 j :=
        fun h => hBDisjoint j hj ⟨h0,h⟩
      simp [h0,h1]
    · by_cases h1 : B1 j
      · simp [h0,h1]
      · have hZero : b j = 0 := by
          by_contra hNonzero
          rcases hB j hj hNonzero with hh | hh
          · exact h0 hh
          · exact h1 hh
        simp [h0,h1,hZero]
  calc
    _ = ∑ i∈SI, ∑ j∈SJ,
        ((if A0 i then a i else 0) +
         (if A1 i then a i else 0)) *
        ((if B0 j then b j else 0) +
         (if B1 j then b j else 0)) * phase i j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [←hCutA i hi,←hCutB j hj]
    _ = _ := by
      simp only [add_mul,mul_add,Finset.sum_add_distrib]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFrameOperator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact operator-level factorization of the physical conditional
primitive frame: one normalized cell kernel equals analysis of an
ARBITRARY state-dependent complex input followed by character
synthesis. In particular, no independence of test H from prime
marks is assumed. This algebraic identity alone does not prove
the original signed residual is a Hoeffding survivor. -/
theorem source_original_finite_conditioned_frame_operator434
    {X C : Type} [Fintype X] [Fintype C]
    (w : X → ℝ) (chi : X → C → ℂ)
    (gate : X → Prop) (nu : ℝ)
    (f : X → ℂ) (p : X) :
    (∑ q : X, (w q:ℂ) *
      (if gate p ∧ gate q
       then (nu:ℂ)⁻¹ *
         (∑ c : C, star (chi p c) * chi q c)
       else 0) * f q) =
    (if gate p
     then (nu:ℂ)⁻¹ *
       ∑ c : C, star (chi p c) *
         ∑ q : X, (w q:ℂ) *
           (if gate q then chi q c * f q else 0)
     else 0) := by
  classical
  by_cases hp : gate p
  · simp only [hp, true_and, if_pos]
    let F : X → C → ℂ := fun q c =>
      (nu:ℂ)⁻¹ * star (chi p c) *
        ((w q:ℂ) * (if gate q then chi q c*f q else 0))
    have hrow (q : X) :
      (w q:ℂ) *
        (if gate q
         then (nu:ℂ)⁻¹ * ∑ c : C, star (chi p c)*chi q c
         else 0) * f q =
      ∑ c : C, F q c := by
      by_cases hq : gate q
      · simp only [if_pos hq, F]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c hc
        ring
      · simp [hq,F]
    calc
      (∑ q : X, (w q:ℂ) *
        (if gate q then (nu:ℂ)⁻¹ *
          (∑ c : C, star (chi p c)*chi q c)
          else 0) * f q) =
        (∑ q : X,∑ c : C,F q c) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hrow q
      _ = ∑ c : C, ∑ q : X, F q c := Finset.sum_comm
      _ = (nu:ℂ)⁻¹ *
        ∑ c : C, star (chi p c) *
          ∑ q : X, (w q:ℂ) *
            (if gate q then chi q c*f q else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        dsimp [F]
        ring
  · simp [hp]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFreedSlotFiberCard -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Sum of original first-m freed probe-slot fibre counts
equals the exact cardinal of the labelled freed pairs,
without pretending labels of equal prime VALUE are one slot. -/
theorem source_original_finite_freed_slot_fiber_card434
    {G : Type} [Fintype G] [DecidableEq G]
    (m : ℕ) (S : Finset (G × Fin m)) :
    (∑ g : G, ((Finset.univ : Finset (Fin m)).filter
      (fun j => (g,j) ∈ S)).card) = S.card := by
  classical
  calc
    _ = (∑ g : G, ∑ j : Fin m,
        if (g,j) ∈ S then (1:ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p : G × Fin m, if p ∈ S then (1:ℕ) else 0 := by
      simpa only [Finset.univ_product_univ] using
        (Finset.sum_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin m))
          (fun p : G × Fin m => if p ∈ S then (1:ℕ) else 0)).symm
    _ = S.card := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteIndependentFibreCard -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- A sharp finite factorwise FIBRE counting theorem.
If each element in a globally constrained subset T of
a genuine dependent product `∀g, Xg` lies in the
fixed fibre of the ORIGINAL group statistic Fg, then
the size of T is at most the product of the cardinalities
of those true group fibres. Thus group fibre bounds
`<=k_g!` multiply as `∏g k_g!`, rather than
using the much worse factorial of ALL slots.
No independence of the underlying complex TEST is assumed:
this lemma concerns only the size of the arithmetic fibre. -/
theorem source_original_finite_independent_fibre_card434
    {G : Type} [Fintype G] [DecidableEq G]
    (X : G → Type) [∀ g, Fintype (X g)]
    (F : ∀ g, X g → ℕ)
    (T : Finset (∀ g : G, X g))
    (a0 : ∀ g : G, X g)
    (cap : G → ℕ)
    (hFibre : ∀ a ∈ T, ∀ g, F g (a g) = F g (a0 g))
    (hCap : ∀ g,
      ((Finset.univ : Finset (X g)).filter
        (fun x => F g x = F g (a0 g))).card ≤ cap g) :
    T.card ≤ ∏ g : G, cap g := by
  classical
  let Tg : (g : G) → Finset (X g) := fun g =>
    Finset.univ.filter (fun x => F g x = F g (a0 g))
  have hSubset : T ⊆ Fintype.piFinset Tg := by
    intro a ha
    exact (Fintype.mem_piFinset).mpr (fun g =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFibre a ha g⟩)
  calc
    _ ≤ (Fintype.piFinset Tg).card :=
      Finset.card_le_card hSubset
    _ = ∏ g : G, (Tg g).card := Fintype.card_piFinset Tg
    _ ≤ ∏ g : G, cap g := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact Nat.zero_le _
      · intro g hg
        exact hCap g
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteInverseAtomL1CS -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Cauchy-Schwarz for selected physical integer coefficients
with positive original atom weights. -/
theorem source_original_finite_inverse_atom_L1_CS434
    {X : Type} (S : Finset X) (w : X → ℝ)
    (hw : ∀ x ∈ S, 0 < w x)
    (a : X → ℂ) :
    (∑ x ∈ S, ‖a x‖)^2 ≤
      (∑ x ∈ S, w x) *
      (∑ x ∈ S, ‖a x‖^2 / w x) := by
  classical
  let f : X → ℝ := fun x => Real.sqrt (w x)
  let g : X → ℝ := fun x => ‖a x‖ / Real.sqrt (w x)
  have hf (x : X) (hx : x ∈ S) : f x*g x=‖a x‖ := by
    dsimp [f,g]
    have hne : Real.sqrt (w x) ≠ 0 :=
      (Real.sqrt_pos.2 (hw x hx)).ne'
    field_simp [hne]
  have hf2 (x : X) (hx : x ∈ S) : (f x)^2=w x := by
    exact Real.sq_sqrt (hw x hx).le
  have hg2 (x : X) (hx : x ∈ S) :
      (g x)^2=‖a x‖^2/w x := by
    dsimp [g]
    rw [div_pow,Real.sq_sqrt (hw x hx).le]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S f g
  calc
    (∑ x ∈ S, ‖a x‖)^2 =
        (∑ x ∈ S, f x*g x)^2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact (hf x hx).symm
    _ ≤ (∑ x ∈ S, (f x)^2) *
          (∑ x ∈ S, (g x)^2) := hCS
    _ = (∑ x ∈ S, w x) *
          (∑ x ∈ S, ‖a x‖^2 / w x) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro x hx
        exact hf2 x hx
      · apply Finset.sum_congr rfl
        intro x hx
        exact hg2 x hx
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteNestedFilterDeciderInvariant -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Exact independently labelled source03 selected A/B
two-integer bilinear operation is invariant when Lean's
executable log-cell equality deciders are replaced by the
classical prop-deciders used in a generic finite signed
Hilbert operator lemma. The prime-atom measures, tests and
coupled kernel are otherwise identical. -/
theorem source_original_finite_nested_filter_decider_invariant434
    {α β : Type} (S : Finset α) (T : Finset β)
    (P : α → Prop) (Q : β → Prop)
    (p₁ p₂ : DecidablePred P) (q₁ q₂ : DecidablePred Q)
    (H : α → β → ℂ) :
    (∑ x ∈ @Finset.filter α P p₁ S,
      ∑ y ∈ @Finset.filter β Q q₁ T, H x y) =
    (∑ x ∈ @Finset.filter α P p₂ S,
      ∑ y ∈ @Finset.filter β Q q₂ T, H x y) := by
  rw [source_original_finite_filter_decider_invariant434 P S p₁ p₂,
    source_original_finite_filter_decider_invariant434 Q T q₁ q₂]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteOutputAtomCellMaskFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- EXACT output-atom mask pushforward for the original
SOURCE03 signed physical bilinear residual. The selected
GLOBAL jA/jB coefficient masks on the full physical atom
supports equal summation over their true filtered supports.
This is valid for an arbitrary JOINT complex Knu/RAW Fourier
kernel H(nA,nB), without factorization or changes to weights,
and preserves all complex output coefficients. -/
theorem source_original_finite_output_atom_cell_mask_fubini434
    (TA TB : Finset ℕ) (A B : ℕ → Prop)
    (aCoeff bCoeff : ℕ → ℂ) (H : ℕ → ℕ → ℂ) :
    (∑ n ∈ TA, ∑ mm ∈ TB,
      (if A n then aCoeff n else 0) *
      (if B mm then bCoeff mm else 0) * H n mm) =
    ∑ n ∈ TA.filter A, ∑ mm ∈ TB.filter B,
      aCoeff n * bCoeff mm * H n mm := by
  classical
  calc
    _ = ∑ n ∈ TA, if A n then
        (∑ mm ∈ TB, if B mm
          then aCoeff n*bCoeff mm*H n mm else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases ha : A n
      · simp only [if_pos ha]
        apply Finset.sum_congr rfl
        intro mm hmm
        by_cases hb : B mm <;> simp [hb]
      · simp [ha]
    _ = ∑ n ∈ TA.filter A, ∑ mm ∈ TB.filter B,
        aCoeff n*bCoeff mm*H n mm := by
      simp only [Finset.sum_filter]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteMaskedTwoSidedSwap -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The exact SOURCE-B/TARGET-A output ordering of the
real original signed two-integer kernel agrees with its
TARGET-A/SOURCE-B C6 selected arithmetic bound. Both active
jB/jA masks are retained, with NO loss from reindexing,
replacing real atoms, counting indices or factorizing H.
This is valid for an arbitrary JOINT complex kernel H(A,B). -/
theorem source_original_finite_masked_two_sided_swap434
    (TA TB : Finset ℕ) (activeA activeB : ℕ → Prop)
    (aCoeff bCoeff : ℕ → ℂ)
    (H : ℕ → ℕ → ℂ) :
    (∑ nB ∈ TB, ∑ nA ∈ TA,
      bCoeff nB*aCoeff nA*
        (if activeB nB ∧ activeA nA then H nA nB else 0)) =
    (∑ nA ∈ TA.filter activeA, ∑ nB ∈ TB.filter activeB,
      aCoeff nA*bCoeff nB*H nA nB) := by
  classical
  have hTerm (nB nA : ℕ) :
      bCoeff nB*aCoeff nA*
        (if activeB nB ∧ activeA nA then H nA nB else 0) =
      (if activeA nA then aCoeff nA else 0) *
      (if activeB nB then bCoeff nB else 0) *
        H nA nB := by
    by_cases ha : activeA nA
    · by_cases hb : activeB nB
      · simp [ha,hb]
        left
        exact mul_comm _ _
      · have hh : ¬(activeB nB ∧ activeA nA) :=
          fun h => hb h.1
        simp [ha,hb,hh]
    · have hh : ¬(activeB nB ∧ activeA nA) :=
        fun h => ha h.2
      simp [ha,hh]
  calc
    _ = ∑ nB ∈ TB, ∑ nA ∈ TA,
      (if activeA nA then aCoeff nA else 0) *
      (if activeB nB then bCoeff nB else 0) *
        H nA nB := by
          apply Finset.sum_congr rfl
          intro nB hnB
          apply Finset.sum_congr rfl
          intro nA hnA
          exact hTerm nB nA
    _ = ∑ nA ∈ TA, ∑ nB ∈ TB,
      (if activeA nA then aCoeff nA else 0) *
      (if activeB nB then bCoeff nB else 0) *
        H nA nB := Finset.sum_comm
    _ = _ := source_original_finite_output_atom_cell_mask_fubini434
      TA TB activeA activeB aCoeff bCoeff H
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFinitePrimitiveMinorModeBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Finite FOUR-index primitive character/cell expansion
has a VALID quantitative L² minor-arc bound from the true
per-mode C6 square-saving and the actual coefficient
L¹ mass. This uses genuine cancellation of EACH character
mode first, not the invalid triangle bound on the raw
prime kernel. The full mode costs are then finite and
may be paid from the original log saving exponent. -/
theorem source_original_finite_primitive_minor_mode_l1_square434
    {I : Type} (modes : Finset I)
    (coef mode : I → ℂ)
    (save cost : ℝ)
    (hsave : 0 ≤ save) (hcost : 0 ≤ cost)
    (hMode : ∀ i ∈ modes, ‖mode i‖^2 ≤ save)
    (hCost : (∑ i ∈ modes, ‖coef i‖) ≤ cost) :
    ‖∑ i ∈ modes, coef i*mode i‖^2 ≤ cost^2*save := by
  have hSqrt : 0 ≤ Real.sqrt save := Real.sqrt_nonneg _
  have hSqrtSq : (Real.sqrt save)^2 = save :=
    Real.sq_sqrt hsave
  have hMode' (i : I) (hi : i ∈ modes) :
      ‖mode i‖ ≤ Real.sqrt save := by
    have h := hMode i hi
    nlinarith [norm_nonneg (mode i)]
  have hTerm (i : I) (hi : i ∈ modes) :
      ‖coef i*mode i‖ ≤ ‖coef i‖*Real.sqrt save := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMode' i hi) (norm_nonneg _)
  have hTriangle :
      ‖∑ i ∈ modes, coef i*mode i‖ ≤
        cost*Real.sqrt save := by
    calc
      _ ≤ ∑ i ∈ modes, ‖coef i*mode i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ modes, ‖coef i‖*Real.sqrt save :=
        Finset.sum_le_sum (fun i hi => hTerm i hi)
      _ = (∑ i ∈ modes, ‖coef i‖)*Real.sqrt save := by
        rw [Finset.sum_mul]
      _ ≤ cost*Real.sqrt save :=
        mul_le_mul_of_nonneg_right hCost hSqrt
  have hCostSqrt : 0 ≤ cost*Real.sqrt save :=
    mul_nonneg hcost hSqrt
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hTriangle 2
  calc
    _ ≤ (cost*Real.sqrt save)^2 := hSq
    _ = cost^2*save := by rw [mul_pow,hSqrtSq]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteRareEventCS -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- A weighted L² test restricted to a GENUINELY rare finite
event has small weighted L¹ expectation. This is the precise
Cauchy–Schwarz estimate required to use an original source03
discarded GLOBAL-cell MASS bound. It does not (incorrectly)
claim the event restriction is small as an L²→L² operator
on all tests. -/
theorem source_original_finite_rare_event_CS434
    {X : Type} [Fintype X]
    (w : X → ℝ) (f : X → ℂ) (bad : X → Prop)
    (hw : ∀ x, 0 ≤ w x) :
    (∑ x : X, w x*(if bad x then ‖f x‖ else 0))^2 ≤
    (∑ x : X, w x*(if bad x then 1 else 0)) *
       (∑ x : X, w x*‖f x‖^2) := by
  classical
  let a : X → ℝ := fun x =>
    Real.sqrt (w x)*(if bad x then (1:ℝ) else 0)
  let b : X → ℝ := fun x => Real.sqrt (w x)*‖f x‖
  have hProd (x : X) :
      a x*b x =
      w x*(if bad x then ‖f x‖ else 0) := by
    by_cases h : bad x
    · simp only [a,b,if_pos h,mul_one]
      rw [←mul_assoc,←pow_two,Real.sq_sqrt (hw x)]
    · simp [a,b,h]
  have hASq (x : X) :
      (a x)^2 = w x*(if bad x then 1 else 0) := by
    by_cases h : bad x
    · simp [a,h,Real.sq_sqrt (hw x)]
    · simp [a,h]
  have hBSq (x : X) :
      (b x)^2 = w x*‖f x‖^2 := by
    simp only [b,mul_pow,Real.sq_sqrt (hw x)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset X) a b
  calc
    _ = (∑ x : X, a x*b x)^2 := by
       apply congrArg (fun t : ℝ => t^2)
       apply Finset.sum_congr rfl
       intro x hx
       exact (hProd x).symm
    _ ≤ (∑ x : X, (a x)^2) * (∑ x : X, (b x)^2) :=
      hCS
    _ = (∑ x : X, w x*(if bad x then 1 else 0)) *
       (∑ x : X, w x*‖f x‖^2) := by
       congr 1
       · apply Finset.sum_congr rfl
         intro x hx
         exact hASq x
       · apply Finset.sum_congr rfl
         intro x hx
         exact hBSq x
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteRationalSlowCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Exact finite comparison of a rational character phase
and its coupled slowly varying irrational/Mellin multiplier.
If the rational frame reproduces e(uDX/r) up to eps
and the change M(D)-M(X) *with that rational phase* costs
at most omega, their physical product-phase comparison costs
eps+omega. The scalar M(X) has unit modulus.
The kernel F(D) may be arbitrary, and the rational/slow
factors need not separate between the two BIG products. -/
theorem source_original_finite_rational_slow_combine434
    {X : Type} [Fintype X]
    (F : X → ℂ) (rat slow : X → ℂ) (p : X)
    (eps omega : ℝ)
    (hunit : ‖slow p‖ = 1)
    (hRat : ‖(∑ q : X, F q*rat q)-rat p‖ ≤ eps)
    (hSlow : ‖(∑ q : X, F q*rat q*(slow q-slow p))‖ ≤ omega) :
    ‖(∑ q : X, F q*rat q*slow q)-
      rat p*slow p‖ ≤ eps+omega := by
  classical
  have hSplit :
      (∑ q : X, F q*rat q*slow q)-rat p*slow p =
      (∑ q : X, F q*rat q*(slow q-slow p)) +
      ((∑ q : X, F q*rat q)-rat p)*slow p := by
    have hh (q : X) :
        F q*rat q*slow q =
        F q*rat q*(slow q-slow p) + F q*rat q*slow p := by
      ring
    calc
      _ = (∑ q : X, (F q*rat q*(slow q-slow p) +
                       F q*rat q*slow p))-rat p*slow p := by
            apply congrArg (fun z : ℂ => z-rat p*slow p)
            apply Finset.sum_congr rfl
            intro q hq
            exact hh q
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
  rw [hSplit]
  calc
    _ ≤ ‖∑ q : X, F q*rat q*(slow q-slow p)‖ +
         ‖((∑ q : X, F q*rat q)-rat p)*slow p‖ :=
       norm_add_le _ _
    _ = ‖∑ q : X, F q*rat q*(slow q-slow p)‖ +
        ‖((∑ q : X, F q*rat q)-rat p)‖ := by
       rw [norm_mul,hunit,mul_one]
    _ ≤ omega+eps := add_le_add hSlow hRat
    _ = eps+omega := add_comm _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteRetainedDiscardedCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Combine a TRUE source03 retained-cell signed comparison
estimate with a TRUE discarded-cell signed comparison estimate
for ALL physical states, without assuming the kernel is small
on the discarded set. The source/target tests may depend on
every physical mark and their complex phases may be coupled.
Only the exact partition of physical state PAIRS into gate and
its complement is used. The factor 2 is from (a+b)^2<=2a²+2b².
No upper-bound or probability premise is hidden in this lemma. -/
theorem source_original_finite_retained_discarded_L2_combine434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (err : X × Y → ℂ) (gate : X × Y → Prop)
    (goodBudget badBudget : ℝ)
    (hGood :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if gate q then err q else 0))‖^2 ≤
      goodBudget * (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2))
    (hBad :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if ¬gate q then err q else 0))‖^2 ≤
      badBudget * (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2)) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1) * g q.2 * err q)‖^2 ≤
       2*(goodBudget+badBudget) *
       (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let orig : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*err q
  let good : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*(if gate q then err q else 0)
  let bad : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*(if ¬gate q then err q else 0)
  have hPoint (q : X × Y) : orig q = good q+bad q := by
    by_cases hg : gate q
    · simp [orig,good,bad,hg]
    · simp [orig,good,bad,hg]
  have hSplit :
      (∑ q : X × Y, orig q) =
        (∑ q : X × Y, good q) +
        (∑ q : X × Y, bad q) := by
    calc
      _ = ∑ q : X × Y, (good q+bad q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hPoint q
      _ = _ := Finset.sum_add_distrib
  let A : ℝ := ‖∑ q : X × Y, good q‖
  let B : ℝ := ‖∑ q : X × Y, bad q‖
  have hTr : ‖∑ q : X × Y, orig q‖ ≤ A+B := by
    rw [hSplit]
    exact norm_add_le _ _
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hTr 2
  have h2 : (A+B)^2 ≤ 2*A^2+2*B^2 := by
    nlinarith [sq_nonneg (A-B)]
  have hGood' : A^2 ≤ goodBudget *
       (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2) := hGood
  have hBad' : B^2 ≤ badBudget *
       (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2) := hBad
  change ‖∑ q : X × Y, orig q‖^2 ≤ _
  calc
    _ ≤ (A+B)^2 := hSq
    _ ≤ 2*A^2+2*B^2 := h2
    _ ≤ 2*(goodBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2))+
        2*(badBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2)) := by
        nlinarith [hGood',hBad']
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicGoodBadCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- EXACT decomposition of a true dyad-restricted source03
bilinear comparison into the retained GLOBAL-cell contribution
and the discarded-cell contribution, with the dyadic mask
retained on both sides. No independence, sup-norm, or
nonnegative error hypothesis is needed: all analytic
information is supplied by already proved good/bad L2
estimates. This is the scalar operator sum, not an
unproved comparison estimate. -/
theorem source_original_finite_dyadic_active_discarded_combine434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (err : X × Y → ℂ)
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (activeX : X → Prop) (activeY : Y → Prop)
    (goodBudget badBudget : ℝ)
    (hGood :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if (dyadX q.1 ∧ activeX q.1) ∧
              (dyadY q.2 ∧ activeY q.2)
           then err q else 0))‖^2 ≤
      goodBudget * (∑ x : X, wX x*‖f x‖^2) *
        (∑ y : Y, wY y*‖g y‖^2))
    (hBad :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if dyadX q.1 ∧ dyadY q.2 then
             (if ¬activeX q.1 ∨ ¬activeY q.2
                then err q else 0)
           else 0))‖^2 ≤
      badBudget * (∑ x : X, wX x*‖f x‖^2) *
        (∑ y : Y, wY y*‖g y‖^2)) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if dyadX q.1 ∧ dyadY q.2 then err q else 0))‖^2 ≤
      2*(goodBudget+badBudget) *
        (∑ x : X, wX x*‖f x‖^2) *
        (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let gate : X × Y → Prop := fun q =>
    activeX q.1 ∧ activeY q.2
  let dyad : X × Y → Prop := fun q =>
    dyadX q.1 ∧ dyadY q.2
  let masked : X × Y → ℂ := fun q =>
    if dyad q then err q else 0
  have hGood' :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (@ite ℂ (gate q) (Classical.propDecidable (gate q)) (masked q) 0))‖^2 ≤
      goodBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2) := by
    convert hGood using 1
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hx : dyadX q.1
    · by_cases hy : dyadY q.2
      · by_cases ha : activeX q.1
        · by_cases hb : activeY q.2
          · simp [gate,dyad,masked,hx,hy,ha,hb]
          · simp [gate,dyad,masked,hx,hy,ha,hb]
        · simp [gate,dyad,masked,hx,hy,ha]
      · simp [gate,dyad,masked,hx,hy]
    · simp [gate,dyad,masked,hx]
  have hBad' :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (@ite ℂ (¬gate q) (@instDecidableNot (gate q) (Classical.propDecidable (gate q))) (masked q) 0))‖^2 ≤
      badBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2) := by
    convert hBad using 1
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hx : dyadX q.1
    · by_cases hy : dyadY q.2
      · by_cases ha : activeX q.1
        · by_cases hb : activeY q.2
          · simp [gate,dyad,masked,hx,hy,ha,hb]
          · simp [gate,dyad,masked,hx,hy,ha,hb]
        · simp [gate,dyad,masked,hx,hy,ha]
      · simp [gate,dyad,masked,hx,hy]
    · simp [gate,dyad,masked,hx]
  have hCombined :=
    source_original_finite_retained_discarded_L2_combine434
      wX wY f g masked gate goodBudget badBudget hGood' hBad'
  change
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1)*g q.2*masked q)‖^2 ≤
      2*(goodBudget+badBudget)*
       (∑ x : X, wX x*‖f x‖^2)*
       (∑ y : Y, wY y*‖g y‖^2)
  exact hCombined
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicCombineActualBad -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The finite dyad-restricted comparison combines its actual
retained and dropped regions even if the dropped bound uses a
separate unit-bounded phase H, provided H coincides with the
original signed error on the physically dropped states.
All Boolean mass restrictions are now handled at an ABSTRACT
finite type, avoiding an enormous conversion through the
dependent source03 free-slot prime-mark law. -/
theorem source_original_finite_dyadic_combine_actual_bad_phase434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (err H : X × Y → ℂ)
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (activeX : X → Prop) (activeY : Y → Prop)
    (badX : X → Prop) (badY : Y → Prop)
    (hActiveX : ∀ x, activeX x ↔ ¬badX x)
    (hActiveY : ∀ y, activeY y ↔ ¬badY y)
    (hH : ∀ q : X × Y, badX q.1 ∨ badY q.2 → H q = err q)
    (goodBudget badBudget : ℝ)
    (hGood :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if (dyadX q.1 ∧ activeX q.1) ∧
              (dyadY q.2 ∧ activeY q.2)
           then err q else 0))‖^2 ≤
      goodBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2))
    (hBad :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if dyadX q.1 ∧ dyadY q.2 then
            (if badX q.1 ∨ badY q.2 then H q else 0)
           else 0))‖^2 ≤
      badBudget*(∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2)) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if dyadX q.1 ∧ dyadY q.2 then err q else 0))‖^2 ≤
      2*(goodBudget+badBudget)*
        (∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  have hGate (q : X × Y) :
      (¬activeX q.1 ∨ ¬activeY q.2) ↔
      (badX q.1 ∨ badY q.2) := by
    rw [hActiveX q.1, hActiveY q.2]
    tauto
  have hMask (q : X × Y) :
      (if dyadX q.1 ∧ dyadY q.2 then
         (if ¬activeX q.1 ∨ ¬activeY q.2 then err q else 0)
       else 0) =
      (if dyadX q.1 ∧ dyadY q.2 then
         (if badX q.1 ∨ badY q.2 then H q else 0)
       else 0) := by
    by_cases hd : dyadX q.1 ∧ dyadY q.2
    · simp only [if_pos hd]
      by_cases hb : badX q.1 ∨ badY q.2
      · have ha : ¬activeX q.1 ∨ ¬activeY q.2 :=
          (hGate q).mpr hb
        simp only [if_pos ha, if_pos hb]
        exact (hH q hb).symm
      · have ha : ¬(¬activeX q.1 ∨ ¬activeY q.2) :=
          fun h => hb ((hGate q).mp h)
        simp only [if_neg ha, if_neg hb]
    · simp only [if_neg hd]
  have hBad' :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if dyadX q.1 ∧ dyadY q.2 then
             (if ¬activeX q.1 ∨ ¬activeY q.2
                then err q else 0)
           else 0))‖^2 ≤
      badBudget * (∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2) := by
    have hSum :
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if dyadX q.1 ∧ dyadY q.2 then
             (if ¬activeX q.1 ∨ ¬activeY q.2
                then err q else 0)
           else 0)) =
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1) * g q.2 *
          (if dyadX q.1 ∧ dyadY q.2 then
             (if badX q.1 ∨ badY q.2 then H q else 0)
           else 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hMask q]
    rw [hSum]
    exact hBad
  exact source_original_finite_dyadic_active_discarded_combine434
    wX wY f g err dyadX dyadY activeX activeY
    goodBudget badBudget hGood hBad'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadicCombineActiveFirst -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The exact original source03 finite signed dyadic
retained+discarded comparison needs good-cell masks in
the order (active∧dyad), as they arise NATURALLY from
the true GLOBAL cell probability law. The abstract
combination lemma traditionally uses (dyad∧active).
Resolve that Boolean gate interchange ONCE in a
small independent finite setting, leaving the enormous
genuine ν-dependent source03 proof to simply APPLY this
checked lemma without expensive dependent-type unfolding.
Arbitrary fully coupled signed phases and complex tests;
H=actual error on discarded states; no unproved
independence or rare-event norm assumptions. -/
theorem source_original_finite_dyadic_combine_active_first434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (err H : X × Y → ℂ)
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (activeX : X → Prop) (activeY : Y → Prop)
    (badX : X → Prop) (badY : Y → Prop)
    (hActiveX : ∀ x, activeX x ↔ ¬badX x)
    (hActiveY : ∀ y, activeY y ↔ ¬badY y)
    (hH : ∀ q : X × Y, badX q.1 ∨ badY q.2 → H q = err q)
    (goodBudget badBudget : ℝ)
    (hGood :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if (activeX q.1 ∧ dyadX q.1) ∧
              (activeY q.2 ∧ dyadY q.2)
           then err q else 0))‖^2 ≤
       goodBudget*(∑ x : X, wX x*‖f x‖^2)*
          (∑ y : Y, wY y*‖g y‖^2))
    (hBad :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if dyadX q.1 ∧ dyadY q.2 then
            (if badX q.1 ∨ badY q.2 then H q else 0)
           else 0))‖^2 ≤
       badBudget*(∑ x : X, wX x*‖f x‖^2)*
          (∑ y : Y, wY y*‖g y‖^2)) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1)*g q.2*
        (if dyadX q.1 ∧ dyadY q.2 then err q else 0))‖^2 ≤
      2*(goodBudget+badBudget)*
        (∑ x : X, wX x*‖f x‖^2)*
        (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  have hSwap :=
    source_original_finite_dyadic_good_gate_comm434
      wX wY f g err dyadX activeX dyadY activeY
  have hGoodOriginal :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if (dyadX q.1 ∧ activeX q.1) ∧
              (dyadY q.2 ∧ activeY q.2)
           then err q else 0))‖^2 ≤
       goodBudget*(∑ x : X, wX x*‖f x‖^2)*
          (∑ y : Y, wY y*‖g y‖^2) := by
    exact (congrArg (fun z : ℂ => ‖z‖^2) hSwap).le.trans hGood
  exact source_original_finite_dyadic_combine_actual_bad_phase434
    wX wY f g err H
    dyadX dyadY activeX activeY badX badY
    hActiveX hActiveY hH goodBudget badBudget
    hGoodOriginal hBad
end Green64Analytic.CorrelationSquare

end

