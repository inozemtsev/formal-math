module

public import Green64.Library.Weights.Part014
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part002

@[expose] public section

/-!
# Weights / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalFiniteDyadicCombineDecision -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Stable finite SOURCE03 dyad good/bad combination when the
actual physical ν-pattern's decidability for 'dropped source
or dropped target' is constructed by Finset-membership and
negation, whereas the abstract combination theorem uses
Classical.propDecidable. Both are extensionally the SAME if,
but not definitionally the same Lean function: this theorem
verifies the equality once on small abstract finite types,
preventing massive dependent ν-elaboration or bogus rewrite
failures. The supplied dBad is exactly the caller's native
Decidable disjunction; no mathematical predicate is altered. -/
theorem source_original_finite_dyadic_combine_any_decision434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (err H : X × Y → ℂ)
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (activeX : X → Prop) (activeY : Y → Prop)
    (badX : X → Prop) (badY : Y → Prop)
    (dBad : (q : X × Y) → Decidable (badX q.1 ∨ badY q.2))
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
            (@ite ℂ (badX q.1 ∨ badY q.2) (dBad q)
               (H q) 0)
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
  have hMask (q : X × Y) :
      (if dyadX q.1 ∧ dyadY q.2 then
          (if badX q.1 ∨ badY q.2 then H q else 0)
       else 0) =
      (if dyadX q.1 ∧ dyadY q.2 then
          (@ite ℂ (badX q.1 ∨ badY q.2) (dBad q) (H q) 0)
       else 0) := by
    by_cases hd : dyadX q.1 ∧ dyadY q.2
    · simp only [if_pos hd]
    · simp only [if_neg hd]
  have hSum :
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if dyadX q.1 ∧ dyadY q.2 then
            (if badX q.1 ∨ badY q.2 then H q else 0)
           else 0)) =
      (∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if dyadX q.1 ∧ dyadY q.2 then
            (@ite ℂ (badX q.1 ∨ badY q.2) (dBad q) (H q) 0)
           else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hMask q]
  have hBad' :
      ‖(∑ q : X × Y,
        ((wX q.1*wY q.2:ℝ):ℂ) *
          star (f q.1)*g q.2*
          (if dyadX q.1 ∧ dyadY q.2 then
            (if badX q.1 ∨ badY q.2 then H q else 0)
           else 0))‖^2 ≤
       badBudget*(∑ x : X, wX x*‖f x‖^2)*
          (∑ y : Y, wY y*‖g y‖^2) := by
    exact (congrArg (fun z : ℂ => ‖z‖^2) hSum).le.trans hBad
  apply source_original_finite_dyadic_combine_active_first434
    wX wY f g err H
    dyadX dyadY activeX activeY badX badY
    hActiveX hActiveY hH goodBudget badBudget
    hGood
  convert hBad' using 1
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hd : dyadX q.1 ∧ dyadY q.2
  · by_cases hb : badX q.1 ∨ badY q.2
    · simp [hd,hb]
    · simp [hd,hb]
  · simp [hd]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteOwnArcMajorMinorBadCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Signed original physical operator: MAJOR on each pair's own
moving arc, MINOR outside that same arc but inside ACTUAL active
GLOBAL cells, and genuinely discarded GLOBAL states. No cell
count, no factorization of the full joint kernel/test, and
discarded bad cost is paid EXACTLY ONCE. The major, minor, bad
analytic budgets are explicit premises, not surrogate proofs. -/
theorem source_original_finite_own_arc_major_minor_bad_combine434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wx : X → ℝ) (wy : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (H : X × Y → ℂ)
    (active major : X × Y → Prop)
    (hMajorActive : ∀ xy, major xy → active xy)
    (majorBudget minorBudget badBudget : ℝ)
    (hMajor :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if major xy then H xy else 0))‖^2 ≤
        majorBudget * (∑ x : X, wx x*‖f x‖^2) *
          (∑ y : Y, wy y*‖g y‖^2))
    (hMinor :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if active xy ∧ ¬major xy then H xy else 0))‖^2 ≤
        minorBudget * (∑ x : X, wx x*‖f x‖^2) *
          (∑ y : Y, wy y*‖g y‖^2))
    (hBad :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if ¬active xy then H xy else 0))‖^2 ≤
        badBudget * (∑ x : X, wx x*‖f x‖^2) *
          (∑ y : Y, wy y*‖g y‖^2)) :
    ‖(∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ)*
        star (f xy.1)*g xy.2*H xy)‖^2 ≤
      2*(2*(majorBudget+minorBudget)+badBudget) *
        (∑ x : X, wx x*‖f x‖^2) *
        (∑ y : Y, wy y*‖g y‖^2) := by
  classical
  let inside : X × Y → ℂ := fun xy =>
    if active xy then H xy else 0
  have hM (xy : X × Y) :
      (if major xy then inside xy else 0) =
        (if major xy then H xy else 0) := by
    by_cases hm : major xy
    · simp [inside,hm,hMajorActive xy hm]
    · simp [hm]
  have hN (xy : X × Y) :
      (if ¬major xy then inside xy else 0) =
        (if active xy ∧ ¬major xy then H xy else 0) := by
    by_cases hm : major xy
    · simp [hm]
    · by_cases ha : active xy <;> simp [inside,hm,ha]
  have hMGood :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if major xy then inside xy else 0))‖^2 ≤
        majorBudget*(∑ x : X,wx x*‖f x‖^2)*
          (∑ y : Y,wy y*‖g y‖^2) := by
    simpa only [hM] using hMajor
  have hNGood :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if ¬major xy then inside xy else 0))‖^2 ≤
        minorBudget*(∑ x : X,wx x*‖f x‖^2)*
          (∑ y : Y,wy y*‖g y‖^2) := by
    simpa only [hN] using hMinor
  have hInside := source_original_finite_retained_discarded_L2_combine434
    wx wy f g inside major majorBudget minorBudget hMGood hNGood
  have hActive :
      ‖(∑ xy : X × Y,
        ((wx xy.1*wy xy.2:ℝ):ℂ) *
          star (f xy.1)*g xy.2*
          (if active xy then H xy else 0))‖^2 ≤
        2*(majorBudget+minorBudget) *
          (∑ x : X, wx x*‖f x‖^2) *
          (∑ y : Y, wy y*‖g y‖^2) := hInside
  exact source_original_finite_retained_discarded_L2_combine434
    wx wy f g H active
    (2*(majorBudget+minorBudget)) badBudget hActive hBad
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedBilinearPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact SOURCE03-style weighted COMPLEX coefficient after
integrating all unselected physical coordinates. Tests remain
arbitrary full-state complex functions; this is not an assumed
product-dependent test. -/
noncomputable def sourceOriginalFiniteSelectedComplexCoefficient434
    {X I : Type} [Fintype X] [DecidableEq I]
    (project : X → I) (w : X → ℝ) (f : X → ℂ)
    (i : I) : ℂ :=
  ∑ x : X, if project x = i then (w x:ℂ)*f x else 0

/-- For a TRUE two-ended physical kernel which depends on
the original selected SOURCE and TARGET labels, arbitrary
joint dependence on those two selections H(a,b) is retained.
Only the FULL unselected marks are conditionally summed out.
This is the exact algebraic missing step before applying
the independently proved selected-prime C6 estimates to
arbitrary weighted L² physical endpoint tests.
It does NOT assert that an arbitrary joint physical kernel
H(s,t) can be factored through the selected labels. -/
theorem source_original_finite_selected_bilinear_pushforward434
    {X Y I J : Type}
    [Fintype X] [Fintype Y]
    [DecidableEq I] [DecidableEq J]
    (candidateX : Finset I) (candidateY : Finset J)
    (px : X → I) (py : Y → J)
    (hCoverX : ∀ x, px x ∈ candidateX)
    (hCoverY : ∀ y, py y ∈ candidateY)
    (wx : X → ℝ) (wy : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (H : I → J → ℂ) :
    (∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) *
        star (f xy.1)*g xy.2*H (px xy.1) (py xy.2)) =
    ∑ ij ∈ candidateX.product candidateY,
      sourceOriginalFiniteSelectedComplexCoefficient434
        px wx (fun x => star (f x)) ij.1 *
      sourceOriginalFiniteSelectedComplexCoefficient434
        py wy g ij.2 * H ij.1 ij.2 := by
  classical
  let A : I → ℂ := sourceOriginalFiniteSelectedComplexCoefficient434
    px wx (fun x => star (f x))
  let B : J → ℂ := sourceOriginalFiniteSelectedComplexCoefficient434
    py wy g
  let Z : X × Y → ℂ := fun xy =>
    ((wx xy.1:ℂ)*(wy xy.2:ℂ)) *
      star (f xy.1)*g xy.2*H (px xy.1) (py xy.2)
  have hPartition :=
    source_original_finite_two_ended_dyad_partition434
      candidateX candidateY px py hCoverX hCoverY Z
  have hTerm (ij : I × J) :
      (∑ xy : X × Y,
       if px xy.1 = ij.1 ∧ py xy.2 = ij.2 then Z xy else 0) =
       A ij.1 * B ij.2 * H ij.1 ij.2 := by
    let α : X → ℂ := fun x =>
      if px x=ij.1 then (wx x:ℂ)*star (f x) else 0
    let β : Y → ℂ := fun y =>
      if py y=ij.2 then (wy y:ℂ)*g y else 0
    have hAtom (xy : X × Y) :
        (if px xy.1=ij.1 ∧ py xy.2=ij.2
          then Z xy else 0) =
        α xy.1 * β xy.2 * H ij.1 ij.2 := by
      by_cases hx : px xy.1 = ij.1
      · by_cases hy : py xy.2 = ij.2
        · simp only [α,β,Z,if_pos hx,if_pos hy,
            if_pos (And.intro hx hy)]
          rw [hx,hy]
          ring
        · simp only [if_neg hy,α,β,if_pos hx,mul_zero,zero_mul]
          simp [hx,hy]
      · simp [α,β,hx]
    calc
      _ = ∑ xy : X × Y, α xy.1 * β xy.2 * H ij.1 ij.2 := by
        apply Finset.sum_congr rfl
        intro xy hxy
        exact hAtom xy
      _ = ∑ x : X, ∑ y : Y, α x * β y * H ij.1 ij.2 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : X, (α x * (∑ y : Y, β y)) * H ij.1 ij.2 := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          _ = (∑ y : Y, α x * β y) * H ij.1 ij.2 := by
            rw [Finset.sum_mul]
          _ = (α x * (∑ y : Y, β y)) * H ij.1 ij.2 := by
            rw [Finset.mul_sum]
      _ = (∑ x : X, α x) * (∑ y : Y, β y) *
          H ij.1 ij.2 := by
        rw [←Finset.sum_mul, ←Finset.sum_mul]
      _ = A ij.1 * B ij.2 * H ij.1 ij.2 := by
        rfl
  calc
    _ = ∑ ij ∈ candidateX.product candidateY,
       ∑ xy : X × Y,
        if px xy.1=ij.1 ∧ py xy.2=ij.2 then Z xy else 0 := by
        simpa only [Z, Complex.ofReal_mul] using hPartition.symm
    _ = ∑ ij ∈ candidateX.product candidateY,
         A ij.1 * B ij.2 * H ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hTerm ij
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedConditionalL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- SHARP conditional fibre estimate for arbitrary complex
SOURCE03-style mark-dependent tests under a genuinely
nonnegative physical harmonic measure. The event is the
inverse image of the selected PRIME-LABEL tuple, rather
than a synthetic integer product, and may have repeated
numerical primes across distinct marked slots. -/
theorem source_original_finite_selected_coefficient_fibre_L2_434
    {X I : Type} [Fintype X] [DecidableEq I]
    (project : X → I) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (f : X → ℂ) (i : I) :
    ‖sourceOriginalFiniteSelectedComplexCoefficient434
        project w f i‖^2 ≤
      (∑ x : X, if project x=i then w x else 0) *
      (∑ x : X, if project x=i
        then w x*‖f x‖^2 else 0) := by
  classical
  let event : X → Prop := fun x => project x=i
  let g : X → ℂ := fun x => if event x then f x else 0
  have hN :
      ‖sourceOriginalFiniteSelectedComplexCoefficient434
          project w f i‖ ≤
        ∑ x : X, w x*(if event x then ‖f x‖ else 0) := by
    unfold sourceOriginalFiniteSelectedComplexCoefficient434
    change ‖∑ x : X, if event x then (w x:ℂ)*f x else 0‖ ≤ _
    calc
      _ ≤ ∑ x : X, ‖if event x then (w x:ℂ)*f x else 0‖ :=
        norm_sum_le _ _
      _ = ∑ x : X, w x*(if event x then ‖f x‖ else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases he : event x
        · simp [he,norm_mul,Complex.norm_real,
            Real.norm_eq_abs,abs_of_nonneg (hw x)]
        · simp [he]
  have hCS := source_original_finite_rare_event_CS434
    w g event hw
  have hLhs :
      (∑ x : X, w x*(if event x then ‖g x‖ else 0)) =
      (∑ x : X, w x*(if event x then ‖f x‖ else 0)) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases he : event x <;> simp [g,he]
  have hMass :
      (∑ x : X, w x*(if event x then (1:ℝ) else 0)) =
      (∑ x : X, if project x=i then w x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases he : event x <;> simp [event,he]
  have hEnergy :
      (∑ x : X, w x*‖g x‖^2) =
      (∑ x : X, if project x=i
        then w x*‖f x‖^2 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases he : event x <;> simp [g,event,he]
  have hCSFinal :
      (∑ x : X, w x*(if event x then ‖f x‖ else 0))^2 ≤
      (∑ x : X, if project x=i then w x else 0) *
      (∑ x : X, if project x=i
        then w x*‖f x‖^2 else 0) := by
    calc
      _ = (∑ x : X, w x*(if event x then ‖g x‖ else 0))^2 := by
        rw [hLhs]
      _ ≤ (∑ x : X, w x*(if event x then (1:ℝ) else 0)) *
          (∑ x : X, w x*‖g x‖^2) := by
        convert hCS using 1
        · apply congrArg (fun v : ℝ => v^2)
          apply Finset.sum_congr rfl
          intro x hx
          by_cases he : event x <;> simp [he]
        · apply congrArg (fun v : ℝ =>
            v * (∑ x : X, w x*‖g x‖^2))
          apply Finset.sum_congr rfl
          intro x hx
          by_cases he : event x <;> simp [he]
      _ = _ := by rw [hMass,hEnergy]
  calc
    _ ≤ (∑ x : X, w x*(if event x then ‖f x‖ else 0))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hN 2
    _ ≤ _ := hCSFinal

/-- Genuine selected-PRIME-COORDINATE conditional expectation
is an L² CONTRACTION for arbitrary full complex mark tests,
including the zero-mass selected fibres. No pointwise
unit-bound or cardinality-of-fibres loss enters. -/
theorem source_original_finite_selected_conditional_L2_contraction434
    {X I : Type} [Fintype X] [Fintype I] [DecidableEq I]
    (project : X → I) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (f : X → ℂ) :
    (∑ i : I,
      if (∑ x : X, if project x=i then w x else 0)=0
      then 0
      else ‖sourceOriginalFiniteSelectedComplexCoefficient434
        project w f i‖^2/
          (∑ x : X, if project x=i then w x else 0)) ≤
      ∑ x : X, w x*‖f x‖^2 := by
  classical
  let mass : I → ℝ := fun i =>
    ∑ x : X, if project x=i then w x else 0
  let energy : I → ℝ := fun i =>
    ∑ x : X, if project x=i then w x*‖f x‖^2 else 0
  have hm (i : I) : 0 ≤ mass i := by
    dsimp only [mass]
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : project x=i
    · simpa only [if_pos h] using hw x
    · simp [h]
  have he (i : I) : 0 ≤ energy i := by
    dsimp only [energy]
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : project x=i
    · simp only [if_pos h]
      exact mul_nonneg (hw x) (sq_nonneg _)
    · simp [h]
  have hterm (i : I) :
      (if mass i=0 then 0 else
        ‖sourceOriginalFiniteSelectedComplexCoefficient434
          project w f i‖^2/mass i) ≤ energy i := by
    by_cases hz : mass i=0
    · simp only [if_pos hz]
      exact he i
    · have hp : 0 < mass i := lt_of_le_of_ne (hm i) (Ne.symm hz)
      simp only [if_neg hz]
      apply (div_le_iff₀ hp).mpr
      have hf := source_original_finite_selected_coefficient_fibre_L2_434
        project w hw f i
      change _ ≤ mass i*energy i at hf
      calc
        _ ≤ mass i*energy i := hf
        _ = energy i*mass i := mul_comm _ _
  change (∑ i : I, if mass i=0 then 0 else
      ‖sourceOriginalFiniteSelectedComplexCoefficient434
        project w f i‖^2 / mass i) ≤ _
  calc
    _ ≤ ∑ i : I, energy i := Finset.sum_le_sum (fun i hi => hterm i)
    _ = ∑ x : X, w x*‖f x‖^2 := by
      simp only [energy]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedFullAtomSignedCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Genuine source03 comparison Knu is supported on the true
selected jA/jB output GLOBAL cells, while RAW may initially be
expressed with masks on the FULL output prime-product atom law.
Their inverse-atom weighted L2 estimates combine with NO
output atom cardinality penalty: the selected energy is
bounded above by the original full-energy normalization.
The arithmetic Knu and RAW bounds themselves are explicit
premises, not a surrogate C6 cancellation theorem. -/
theorem source_original_finite_selected_full_atom_signed_combine434
    (TA TB : Finset ℕ) (activeA activeB : ℕ → Prop)
    (pA pB : ℕ → ℝ)
    (hpA : ∀ n ∈ TA, 0 < pA n)
    (hpB : ∀ n ∈ TB, 0 < pB n)
    (aCoeff bCoeff : ℕ → ℂ)
    (Knu SignedRaw : ℂ)
    (BK BR : ℝ) (hBK : 0 ≤ BK) (hBR : 0 ≤ BR)
    (hKnu :
      ‖Knu‖^2 ≤ BK *
        (∑ n ∈ TA.filter activeA, ‖aCoeff n‖^2/pA n) *
        (∑ n ∈ TB.filter activeB, ‖bCoeff n‖^2/pB n))
    (hRaw :
      ‖SignedRaw‖^2 ≤ BR *
        (∑ n ∈ TA, ‖aCoeff n‖^2/pA n) *
        (∑ n ∈ TB, ‖bCoeff n‖^2/pB n)) :
    ‖Knu-SignedRaw‖^2 ≤
      2*(BK+BR) *
        (∑ n ∈ TA, ‖aCoeff n‖^2/pA n) *
        (∑ n ∈ TB, ‖bCoeff n‖^2/pB n) := by
  classical
  let EA := ∑ n ∈ TA, ‖aCoeff n‖^2/pA n
  let EB := ∑ n ∈ TB, ‖bCoeff n‖^2/pB n
  let ea := ∑ n ∈ TA.filter activeA, ‖aCoeff n‖^2/pA n
  let eb := ∑ n ∈ TB.filter activeB, ‖bCoeff n‖^2/pB n
  have hTermA (n : ℕ) (hn : n∈TA) :
      0 ≤ ‖aCoeff n‖^2/pA n :=
    div_nonneg (sq_nonneg _) (hpA n hn).le
  have hTermB (n : ℕ) (hn : n∈TB) :
      0 ≤ ‖bCoeff n‖^2/pB n :=
    div_nonneg (sq_nonneg _) (hpB n hn).le
  have hEa : 0 ≤ EA :=
    Finset.sum_nonneg (fun n hn => hTermA n hn)
  have hEb : 0 ≤ EB :=
    Finset.sum_nonneg (fun n hn => hTermB n hn)
  have hSelectedA : ea ≤ EA :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n hn hnot => hTermA n hn)
  have hSelectedB : eb ≤ EB :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n hn hnot => hTermB n hn)
  have hSmallA : 0 ≤ ea :=
    Finset.sum_nonneg (fun n hn =>
      hTermA n (Finset.mem_filter.mp hn).1)
  have hSmallB : 0 ≤ eb :=
    Finset.sum_nonneg (fun n hn =>
      hTermB n (Finset.mem_filter.mp hn).1)
  have hKnuFull : ‖Knu‖^2 ≤ BK*EA*EB := by
    calc
      _ ≤ BK*ea*eb := hKnu
      _ ≤ BK*EA*eb := by
        apply mul_le_mul_of_nonneg_right _ hSmallB
        exact mul_le_mul_of_nonneg_left hSelectedA hBK
      _ ≤ BK*EA*EB := by
        apply mul_le_mul_of_nonneg_left hSelectedB
        exact mul_nonneg hBK hEa
  have hRawFull : ‖SignedRaw‖^2 ≤ BR*EA*EB := hRaw
  exact source_original_finite_signed_RAW_minus_Knu_L2_combine434
    Knu SignedRaw EA EB BK BR hEa hEb hBK hBR
    hKnuFull hRawFull
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedMarginal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Split an actual dependent physical mark tuple into the TRUE
selected slots and the complementary slots. Supports B_i may
differ, and no equality of group-specific mark counts is imposed. -/
noncomputable def sourceOriginalFiniteSelectedComplementEquiv434
    {I : Type} (B : I → Type) (s : I → Prop) :
    ((∀ i : {i : I // s i}, B i.val) ×
     (∀ i : {i : I // ¬s i}, B i.val)) ≃
       (∀ i : I, B i) where
  toFun z i := if h : s i then z.1 ⟨i,h⟩ else z.2 ⟨i,h⟩
  invFun z := (fun i => z i.val, fun i => z i.val)
  left_inv z := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      simp only [dif_neg i.property]
  right_inv z := by
    funext i
    by_cases h : s i
    · simp only [dif_pos h]
    · simp only [dif_neg h]

theorem source_original_selected_complement_apply_selected434
    {I : Type} (B : I → Type) (s : I → Prop)
    (a : ∀ i : {i : I // s i}, B i.val)
    (b : ∀ i : {i : I // ¬s i}, B i.val)
    (j : {i : I // s i}) :
    sourceOriginalFiniteSelectedComplementEquiv434 B s (a,b) j.val =
      a j := by
  simp [sourceOriginalFiniteSelectedComplementEquiv434, j.property]

theorem source_original_selected_complement_apply_rest434
    {I : Type} (B : I → Type) (s : I → Prop)
    (a : ∀ i : {i : I // s i}, B i.val)
    (b : ∀ i : {i : I // ¬s i}, B i.val)
    (j : {i : I // ¬s i}) :
    sourceOriginalFiniteSelectedComplementEquiv434 B s (a,b) j.val =
      b j := by
  simp [sourceOriginalFiniteSelectedComplementEquiv434, j.property]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedMassSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- TRUE finite SOURCE03 independent, coordinate-dependent
harmonic mass factors EXACTLY into the selected prime slots
and all complementary prime slots under the actual splitting
equivalence. Neither common prime support nor equal t_g
is assumed; repeated numerical primes remain independently
labelled, and no independent arbitrary test is introduced. -/
theorem source_original_selected_complement_product_mass434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) (s : I → Prop)
    (mu : ∀ i, B i → ℝ)
    (a : ∀ i : {i : I // s i}, B i.val)
    (b : ∀ i : {i : I // ¬s i}, B i.val) :
    (∏ i : I, mu i
      (sourceOriginalFiniteSelectedComplementEquiv434 B s (a,b) i)) =
    (∏ i : {i : I // s i}, mu i.val (a i)) *
    (∏ i : {i : I // ¬s i}, mu i.val (b i)) := by
  classical
  let y := sourceOriginalFiniteSelectedComplementEquiv434 B s (a,b)
  let f : I → ℝ := fun i => mu i (y i)
  have hsplit := Fintype.prod_subtype_mul_prod_subtype s f
  have hLeft :
      (∏ i : {i : I // s i}, f i.val) =
      (∏ i : {i : I // s i}, mu i.val (a i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (mu i.val)
      (source_original_selected_complement_apply_selected434
        B s a b i)
  have hRight :
      (∏ i : {i : I // ¬s i}, f i.val) =
      (∏ i : {i : I // ¬s i}, mu i.val (b i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (mu i.val)
      (source_original_selected_complement_apply_rest434
        B s a b i)
  calc
    _ = ∏ i : I, f i := rfl
    _ = (∏ i : {i : I // s i}, f i.val) *
        (∏ i : {i : I // ¬s i}, f i.val) := hsplit.symm
    _ = _ := by rw [hLeft,hRight]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedMarginalLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- EXACT marginal of an arbitrary independently labelled
finite physical prime-product probability law to any selected
SUBSET of genuine dependent prime coordinates. No factorization
of the TEST F and no common support B_i are assumed.
The complement is integrated out solely using the verified
normalization of each original coordinate's harmonic law.
This is a true physical push-forward identity, not a
synthetic independent distribution assumption. -/
theorem source_original_finite_selected_marginal_law434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)]
    (s : I → Prop)
    (mu : ∀ i, B i → ℝ)
    (hmu : ∀ i, ∑ b : B i, mu i b = 1)
    (F : (∀ i : {i : I // s i}, B i.val) → ℝ) :
    (∑ x : (∀ i : I, B i),
      (∏ i : I, mu i (x i)) * F (fun j => x j.val)) =
    ∑ a : (∀ i : {i : I // s i}, B i.val),
      (∏ j : {i : I // s i}, mu j.val (a j)) * F a := by
  classical
  let A := (∀ i : {i : I // s i}, B i.val)
  let R := (∀ i : {i : I // ¬s i}, B i.val)
  let E : (A × R) ≃ (∀ i : I, B i) :=
    sourceOriginalFiniteSelectedComplementEquiv434 B s
  let WA : A → ℝ := fun a =>
    ∏ j : {i : I // s i}, mu j.val (a j)
  let WR : R → ℝ := fun b =>
    ∏ j : {i : I // ¬s i}, mu j.val (b j)
  have hRest : (∑ b : R, WR b) = 1 := by
    change (∑ b : R,
       ∏ j : {i : I // ¬s i}, mu j.val (b j)) = 1
    calc
      _ = ∏ j : {i : I // ¬s i},
          ∑ v : B j.val, mu j.val v := by
        rw [Finset.prod_univ_sum]
        simp only [Fintype.piFinset_univ]
        rfl
      _ = 1 := by simp [hmu]
  have hPerm := Fintype.sum_equiv E
    (fun pr : A × R =>
      (∏ i : I, mu i (E pr i)) *
       F (fun j => E pr j.val))
    (fun x : (∀ i : I, B i) =>
      (∏ i : I, mu i (x i)) * F (fun j => x j.val))
    (fun pr => rfl)
  calc
    _ = ∑ pr : A × R,
      (∏ i : I, mu i (E pr i)) *
       F (fun j => E pr j.val) := hPerm.symm
    _ = ∑ a : A, ∑ b : R, (WA a * WR b) * F a := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hF : (fun j : {i : I // s i} =>
          E (a,b) j.val) = a := by
        funext j
        exact source_original_selected_complement_apply_selected434
          B s a b j
      rw [hF]
      exact congrArg (fun z : ℝ => z*F a)
        (source_original_selected_complement_product_mass434
          B s mu a b)
    _ = ∑ a : A, WA a * F a := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = (WA a * F a) * (∑ b : R, WR b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = WA a * F a := by rw [hRest,mul_one]
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteInjectiveMarginal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual selected slots of an injectively embedded index
type J are EXACTLY the range of that physical slot embedding,
with the original dependent prime support B_i unchanged. -/
noncomputable def sourceOriginalFiniteEmbeddingRangeEquiv434
    {I J : Type} (embed : J ↪ I) :
    J ≃ {i : I // i ∈ Set.range embed} :=
  Equiv.ofBijective
    (fun j : J => (⟨embed j, ⟨j,rfl⟩⟩ :
       {i : I // i ∈ Set.range embed}))
    ⟨(by
       intro j k hjk
       exact embed.injective (congrArg Subtype.val hjk)),
     (by
       intro z
       obtain ⟨j,hj⟩ := z.property
       refine ⟨j,?_⟩
       exact Subtype.ext hj)⟩

/-- Pushforward of the full coordinate-dependent harmonic
product law along ANY injective set of selected physical slots.
Unlike a theorem for a SUBSET index type, this retains the
genuine original selected index J (e.g. ν.1 or ν.2), including
its names and distinct prime supports and actual group-slot
locations. It is independent of the number of other physical
marks and works for arbitrary correlated observables F of
all selected slot values. -/
theorem source_original_finite_injective_marginal_law434
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (B : I → Type) [∀ i, Fintype (B i)]
    (embed : J ↪ I)
    (mu : ∀ i, B i → ℝ)
    (hmu : ∀ i, ∑ b : B i, mu i b = 1)
    (F : (∀ j : J, B (embed j)) → ℝ) :
    (∑ x : (∀ i : I, B i),
      (∏ i : I, mu i (x i)) * F (fun j => x (embed j))) =
    ∑ a : (∀ j : J, B (embed j)),
      (∏ j : J, mu (embed j) (a j)) * F a := by
  classical
  let selected : I → Prop := fun i => i ∈ Set.range embed
  letI : Fintype {i : I // selected i} := Subtype.fintype selected
  let eqv : J ≃ {i : I // selected i} :=
    sourceOriginalFiniteEmbeddingRangeEquiv434 embed
  let BC : {i : I // selected i} → Type := fun i => B i.val
  let E : (∀ j : J, B (embed j)) ≃
    (∀ k : {i : I // selected i}, B k.val) :=
    Equiv.piCongrLeft BC eqv
  let F' : (∀ k : {i : I // selected i}, B k.val) → ℝ :=
    fun v => F (fun j => v (eqv j))
  have heval (a : ∀ j : J, B (embed j)) (j : J) :
      E a (eqv j) = a j := by
    exact Equiv.piCongrLeft_apply_apply BC eqv a j
  have hCost (a : ∀ j : J, B (embed j)) :
    (∏ j : J, mu (embed j) (a j)) * F a =
    (∏ k : {i : I // selected i}, mu k.val (E a k)) *
      F' (E a) := by
    have hProd :
        (∏ j : J, mu (embed j) (a j)) =
        (∏ k : {i : I // selected i},
          mu k.val (E a k)) := by
      exact Fintype.prod_equiv eqv
        (fun j => mu (embed j) (a j))
        (fun k => mu k.val (E a k))
        (by
          intro j
          change mu (embed j) (a j) =
            mu (embed j) (E a (eqv j))
          rw [heval a j])
    have hF' : F' (E a) = F a := by
      dsimp only [F']
      congr 1
      funext j
      exact heval a j
    rw [hProd,hF']
  have hPerm := Fintype.sum_equiv E
    (fun a : (∀ j : J, B (embed j)) =>
      (∏ j : J, mu (embed j) (a j)) * F a)
    (fun v : (∀ k : {i : I // selected i}, B k.val) =>
      (∏ k : {i : I // selected i}, mu k.val (v k)) *
        F' v)
    hCost
  have hProjection (x : ∀ i : I, B i) :
      F' (fun k : {i : I // selected i} => x k.val) =
      F (fun j : J => x (embed j)) := by
    dsimp only [F',selected]
    rfl
  have hMarg := source_original_finite_selected_marginal_law434
    B selected mu hmu F'
  calc
    _ = (∑ x : (∀ i : I, B i),
      (∏ i : I, mu i (x i)) *
         F' (fun k : {i : I // selected i} => x k.val)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hProjection]
    _ = ∑ v : (∀ k : {i : I // selected i}, B k.val),
      (∏ k : {i : I // selected i}, mu k.val (v k)) * F' v :=
       (by
         convert hMarg using 1
         apply Finset.sum_congr
         · ext a
           simp
         · intro a ha
           congr 1
           apply Finset.prod_congr
           · ext i
             simp
           · intro i hi
             rfl)
    _ = _ := hPerm.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedSignedKernelFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- EXACT selected original SOURCE03 output operator identity:
summing the TRUE selected two-integer RAW-minus-primitive-Knu
kernel is the difference between the full selected primitive
expectation and the genuine signed RAW expectation originally
masked on the complete output atom supports. The kernel H may
be JOINTLY dependent on both output values and can contain any
character / four-sign / Fourier / Mellin arithmetic. No
replacement of output measures, no fake factorization, no
unproved spectral estimate. -/
theorem source_original_finite_selected_signed_kernel_fubini434
    (TA TB : Finset ℕ) (activeA activeB : ℕ → Prop)
    (aCoeff bCoeff : ℕ → ℂ)
    (H : ℕ → ℕ → ℂ) (phase : ℕ → ℂ) (σ : ℂ) :
    let AA := TA.filter activeA
    let BB := TB.filter activeB
    let Knu : ℂ := ∑ n ∈ AA, ∑ mm ∈ BB,
      aCoeff n*bCoeff mm*H n mm
    let SignedRaw : ℂ := σ*
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if activeA n then aCoeff n else 0) *
        (if activeB mm then bCoeff mm else 0) *
        phase (n*mm))
    (∑ n ∈ AA, ∑ mm ∈ BB,
      aCoeff n*bCoeff mm*(H n mm-σ*phase (n*mm))) =
      Knu-SignedRaw := by
  classical
  dsimp only
  have hMask :=
    source_original_finite_output_atom_cell_mask_fubini434
      TA TB activeA activeB aCoeff bCoeff
      (fun n mm => phase (n*mm))
  rw [hMask]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro mm hmm
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedSupportConditionalL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- SHARP actual SOURCE03 conditional L² projection onto
the genuine FINITE selected prime-product support, even
when the ambient output type I is INFINITE (in particular
I=Nat for the true original BIG source/target products).
No artificial Fintype Nat or pointwise test bound is used.
Zero-mass fibres are treated exactly. -/
theorem source_original_finite_selected_support_conditional_L2_434
    {X I : Type} [Fintype X] [DecidableEq I]
    (candidate : Finset I)
    (project : X → I) (hCover : ∀ x, project x ∈ candidate)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f : X → ℂ) :
    (∑ i ∈ candidate,
      if (∑ x : X, if project x=i then w x else 0)=0
      then 0
      else ‖sourceOriginalFiniteSelectedComplexCoefficient434
        project w f i‖^2 /
        (∑ x : X, if project x=i then w x else 0)) ≤
    ∑ x : X, w x*‖f x‖^2 := by
  classical
  let mass : I → ℝ := fun i =>
    ∑ x : X, if project x=i then w x else 0
  let energy : I → ℝ := fun i =>
    ∑ x : X, if project x=i then w x*‖f x‖^2 else 0
  have hm (i : I) : 0 ≤ mass i := by
    dsimp only [mass]
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : project x=i
    · simpa only [if_pos h] using hw x
    · simp [h]
  have he (i : I) : 0 ≤ energy i := by
    dsimp only [energy]
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : project x=i
    · simp only [if_pos h]
      exact mul_nonneg (hw x) (sq_nonneg _)
    · simp [h]
  have hterm (i : I) :
      (if mass i=0 then 0 else
        ‖sourceOriginalFiniteSelectedComplexCoefficient434
          project w f i‖^2/mass i) ≤ energy i := by
    by_cases hz : mass i=0
    · simp only [if_pos hz]
      exact he i
    · have hp : 0 < mass i :=
        lt_of_le_of_ne (hm i) (Ne.symm hz)
      simp only [if_neg hz]
      apply (div_le_iff₀ hp).mpr
      have hf :=
        source_original_finite_selected_coefficient_fibre_L2_434
          project w hw f i
      change _ ≤ mass i*energy i at hf
      calc
        _ ≤ mass i*energy i := hf
        _ = energy i*mass i := mul_comm _ _
  change (∑ i ∈ candidate,
      if mass i=0 then 0 else
        ‖sourceOriginalFiniteSelectedComplexCoefficient434
          project w f i‖^2 / mass i) ≤ _
  calc
    _ ≤ ∑ i ∈ candidate, energy i :=
      Finset.sum_le_sum (fun i hi => hterm i)
    _ = ∑ x : X, w x*‖f x‖^2 :=
      source_original_finite_dyad_energy_partition434
        candidate project hCover w f
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSelectedSupportOperatorUpgrade -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Genuine SOURCE03 finite-support L² OPERATOR upgrade.
A selected two-product kernel may depend JOINTLY on (B,A);
no tensor factorization of H is imposed. If the same
kernel has an honest weighted coefficient energy estimate
on all attainable selected integer products, it controls
arbitrary COMPLEX full-mark endpoint tests in their
original physical harmonic L² norm. No fake Fintype Nat,
no unit-bounded test substitution, no fibre-cardinality
loss and no unnormalized mass-zero terms. -/
theorem source_original_finite_selected_support_operator_upgrade434
    {X Y I J : Type} [Fintype X] [Fintype Y]
    [DecidableEq I] [DecidableEq J]
    (candidateX : Finset I) (candidateY : Finset J)
    (px : X → I) (py : Y → J)
    (hCoverX : ∀ x, px x ∈ candidateX)
    (hCoverY : ∀ y, py y ∈ candidateY)
    (wx : X → ℝ) (wy : Y → ℝ)
    (hWx : ∀ x, 0 ≤ wx x) (hWy : ∀ y, 0 ≤ wy y)
    (H : I → J → ℂ) (budget : ℝ) (hBudget : 0 ≤ budget)
    (hSelected : ∀ (a : I → ℂ) (b : J → ℂ),
      ‖(∑ ij ∈ candidateX.product candidateY,
        a ij.1 * b ij.2 * H ij.1 ij.2)‖^2 ≤
      budget *
      (∑ i ∈ candidateX,
        if (∑ x : X, if px x=i then wx x else 0)=0
        then 0
        else ‖a i‖^2 /
          (∑ x : X, if px x=i then wx x else 0)) *
      (∑ j ∈ candidateY,
        if (∑ y : Y, if py y=j then wy y else 0)=0
        then 0
        else ‖b j‖^2 /
          (∑ y : Y, if py y=j then wy y else 0)))
    (f : X → ℂ) (g : Y → ℂ) :
    ‖(∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) *
      star (f xy.1)*g xy.2*H (px xy.1) (py xy.2))‖^2 ≤
    budget * (∑ x : X, wx x*‖f x‖^2) *
      (∑ y : Y, wy y*‖g y‖^2) := by
  classical
  let a : I → ℂ := sourceOriginalFiniteSelectedComplexCoefficient434
    px wx (fun x => star (f x))
  let b : J → ℂ := sourceOriginalFiniteSelectedComplexCoefficient434
    py wy g
  let mx : I → ℝ := fun i =>
    ∑ x : X, if px x=i then wx x else 0
  let my : J → ℝ := fun j =>
    ∑ y : Y, if py y=j then wy y else 0
  let EX : ℝ := ∑ x : X, wx x*‖f x‖^2
  let EY : ℝ := ∑ y : Y, wy y*‖g y‖^2
  let AX : ℝ := ∑ i ∈ candidateX,
    if mx i=0 then 0 else ‖a i‖^2/mx i
  let BY : ℝ := ∑ j ∈ candidateY,
    if my j=0 then 0 else ‖b j‖^2/my j
  have hEX0 : 0 ≤ EX := by
    dsimp only [EX]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hWx x) (sq_nonneg _)
  have hMY0 (j : J) : 0 ≤ my j := by
    dsimp only [my]
    apply Finset.sum_nonneg
    intro y hy
    by_cases hj : py y=j
    · simpa only [if_pos hj] using hWy y
    · simp [hj]
  have hBY0 : 0 ≤ BY := by
    dsimp only [BY]
    apply Finset.sum_nonneg
    intro j hj
    by_cases hz : my j=0
    · simp only [if_pos hz]
      exact le_refl 0
    · have hmp : 0 < my j :=
        lt_of_le_of_ne (hMY0 j) (Ne.symm hz)
      simp only [if_neg hz]
      exact div_nonneg (sq_nonneg _) hmp.le
  have hAX : AX ≤ EX := by
    have hc := source_original_finite_selected_support_conditional_L2_434
      candidateX px hCoverX wx hWx (fun x => star (f x))
    change AX ≤ ∑ x : X, wx x*‖star (f x)‖^2 at hc
    simpa only [EX,norm_star] using hc
  have hBY : BY ≤ EY := by
    have hc := source_original_finite_selected_support_conditional_L2_434
      candidateY py hCoverY wy hWy g
    change BY ≤ EY at hc
    exact hc
  have hPush := source_original_finite_selected_bilinear_pushforward434
    candidateX candidateY px py hCoverX hCoverY
    wx wy f g H
  have hSmall : ‖(∑ ij ∈ candidateX.product candidateY,
      a ij.1*b ij.2*H ij.1 ij.2)‖^2 ≤ budget*AX*BY := by
    have hh := hSelected a b
    change _ ≤ budget*AX*BY at hh
    exact hh
  have hAB : budget*AX*BY ≤ budget*EX*EY := by
    calc
      budget*AX*BY ≤ budget*EX*BY :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAX hBudget) hBY0
      _ ≤ budget*EX*EY :=
        mul_le_mul_of_nonneg_left hBY (mul_nonneg hBudget hEX0)
  change ‖(∑ xy : X × Y,
    ((wx xy.1*wy xy.2:ℝ):ℂ) *
    star (f xy.1)*g xy.2*H (px xy.1) (py xy.2))‖^2 ≤
      budget*EX*EY
  rw [hPush]
  exact hSmall.trans hAB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteMatchedMassOperatorUpgrade -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Exact quantitative upgrade from a weighted two-integer
selected kernel L2 bound to arbitrary FULL endpoint-state L2
tests when both selected integer masses agree with their true
physical marginals. Only genuine attainable outputs are used;
their positive marginal atom weights remove the artificial
zero-mass branch, so NO fibre-cardinality penalty is paid.
The complex H(i,j) can be jointly coupled; no tensor
factorization, unit-input restriction or independence surrogate. -/
theorem source_original_finite_matched_mass_operator_upgrade434
    {X Y I J : Type} [Fintype X] [Fintype Y]
    [DecidableEq I] [DecidableEq J]
    (SI : Finset I) (SJ : Finset J)
    (px : X → I) (py : Y → J)
    (hCoverX : ∀ x, px x ∈ SI)
    (hCoverY : ∀ y, py y ∈ SJ)
    (wx : X → ℝ) (wy : Y → ℝ)
    (hWx : ∀ x, 0 ≤ wx x) (hWy : ∀ y, 0 ≤ wy y)
    (mx : I → ℝ) (my : J → ℝ)
    (hMX : ∀ i ∈ SI,
      (∑ x : X, if px x=i then wx x else 0) = mx i)
    (hMY : ∀ j ∈ SJ,
      (∑ y : Y, if py y=j then wy y else 0) = my j)
    (hPosX : ∀ i ∈ SI, 0 < mx i)
    (hPosY : ∀ j ∈ SJ, 0 < my j)
    (H : I → J → ℂ) (budget : ℝ) (hBudget : 0 ≤ budget)
    (hSelected : ∀ (a : I → ℂ) (b : J → ℂ),
      ‖(∑ ij ∈ SI.product SJ,
        a ij.1*b ij.2*H ij.1 ij.2)‖^2 ≤
      budget * (∑ i ∈ SI, ‖a i‖^2/mx i) *
               (∑ j ∈ SJ, ‖b j‖^2/my j))
    (f : X → ℂ) (g : Y → ℂ) :
    ‖(∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) *
        star (f xy.1)*g xy.2*H (px xy.1) (py xy.2))‖^2 ≤
      budget * (∑ x : X, wx x*‖f x‖^2) *
               (∑ y : Y, wy y*‖g y‖^2) := by
  classical
  have hOperator : ∀ (a : I → ℂ) (b : J → ℂ),
      ‖(∑ ij ∈ SI.product SJ,
        a ij.1*b ij.2*H ij.1 ij.2)‖^2 ≤
      budget *
        (∑ i ∈ SI,
          if (∑ x : X, if px x=i then wx x else 0)=0
          then 0 else ‖a i‖^2 /
            (∑ x : X, if px x=i then wx x else 0)) *
        (∑ j ∈ SJ,
          if (∑ y : Y, if py y=j then wy y else 0)=0
          then 0 else ‖b j‖^2 /
            (∑ y : Y, if py y=j then wy y else 0)) := by
    intro a b
    have hEqX :
        (∑ i ∈ SI,
          if (∑ x : X, if px x=i then wx x else 0)=0
          then 0 else ‖a i‖^2 /
            (∑ x : X, if px x=i then wx x else 0)) =
        (∑ i ∈ SI, ‖a i‖^2/mx i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : (∑ x : X, if px x=i then wx x else 0) ≠ 0 := by
        rw [hMX i hi]
        exact (hPosX i hi).ne'
      simp only [if_neg hne]
      rw [hMX i hi]
    have hEqY :
        (∑ j ∈ SJ,
          if (∑ y : Y, if py y=j then wy y else 0)=0
          then 0 else ‖b j‖^2 /
            (∑ y : Y, if py y=j then wy y else 0)) =
        (∑ j ∈ SJ, ‖b j‖^2/my j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hne : (∑ y : Y, if py y=j then wy y else 0) ≠ 0 := by
        rw [hMY j hj]
        exact (hPosY j hj).ne'
      simp only [if_neg hne]
      rw [hMY j hj]
    rw [hEqX,hEqY]
    exact hSelected a b
  exact source_original_finite_selected_support_operator_upgrade434
    SI SJ px py hCoverX hCoverY wx wy hWx hWy
    H budget hBudget hOperator f g
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSubprobabilityAtomKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Uniform original output-atom kernel saving on a RESTRICTED subprobability set implies its true
two-sided inverse-harmonic-atom weighted L2 operator estimate.
Any JOINT complex H(i,j) is allowed; it is not assumed to
factor into the endpoint tests. The selected finite supports
carry exact positive subprobability masses and no atom-cardinality
loss occurs. -/
theorem source_original_finite_subprobability_atom_kernel_operator434
    {I J : Type} (SI : Finset I) (SJ : Finset J)
    (wi : I → ℝ) (wj : J → ℝ)
    (hwi : ∀ i ∈ SI, 0 < wi i)
    (hwj : ∀ j ∈ SJ, 0 < wj j)
    (hTotalI : (∑ i ∈ SI, wi i) ≤ 1)
    (hTotalJ : (∑ j ∈ SJ, wj j) ≤ 1)
    (a : I → ℂ) (b : J → ℂ)
    (H : I → J → ℂ) (eps : ℝ) (heps : 0 ≤ eps)
    (hH : ∀ i ∈ SI, ∀ j ∈ SJ, ‖H i j‖ ≤ eps) :
    ‖(∑ i ∈ SI, ∑ j ∈ SJ, a i*b j*H i j)‖^2 ≤
      eps^2 * (∑ i ∈ SI, ‖a i‖^2 / wi i) *
              (∑ j ∈ SJ, ‖b j‖^2 / wj j) := by
  classical
  let AI := ∑ i ∈ SI, ‖a i‖
  let BJ := ∑ j ∈ SJ, ‖b j‖
  let EI := ∑ i ∈ SI, ‖a i‖^2 / wi i
  let EJ := ∑ j ∈ SJ, ‖b j‖^2 / wj j
  have hAI : 0 ≤ AI := Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hBJ : 0 ≤ BJ := Finset.sum_nonneg (fun j hj => norm_nonneg _)
  have hEI : 0 ≤ EI := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (sq_nonneg _) (hwi i hi).le
  have hEJ : 0 ≤ EJ := by
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (sq_nonneg _) (hwj j hj).le
  have hCSi : AI^2 ≤ EI := by
    have hh := source_original_finite_inverse_atom_L1_CS434
      SI wi hwi a
    calc
      _ ≤ (∑ i ∈ SI, wi i)*EI := hh
      _ ≤ 1*EI :=
        mul_le_mul_of_nonneg_right hTotalI hEI
      _ = EI := one_mul EI
  have hCSj : BJ^2 ≤ EJ := by
    have hh := source_original_finite_inverse_atom_L1_CS434
      SJ wj hwj b
    calc
      _ ≤ (∑ j ∈ SJ, wj j)*EJ := hh
      _ ≤ 1*EJ :=
        mul_le_mul_of_nonneg_right hTotalJ hEJ
      _ = EJ := one_mul EJ
  have hTerm (i : I) (hi : i ∈ SI) (j : J) (hj : j ∈ SJ) :
      ‖a i*b j*H i j‖ ≤ ‖a i‖*‖b j‖*eps := by
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hH i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hTriangle :
      ‖∑ i ∈ SI, ∑ j ∈ SJ, a i*b j*H i j‖ ≤
        ∑ i ∈ SI, ∑ j ∈ SJ, ‖a i‖*‖b j‖*eps := by
    calc
      _ ≤ ∑ i ∈ SI, ‖∑ j ∈ SJ, a i*b j*H i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ SI, ∑ j ∈ SJ, ‖a i*b j*H i j‖ :=
        Finset.sum_le_sum (fun i hi => norm_sum_le _ _)
      _ ≤ ∑ i ∈ SI, ∑ j ∈ SJ, ‖a i‖*‖b j‖*eps := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum (fun j hj => hTerm i hi j hj)
  have hFactor :
      (∑ i ∈ SI, ∑ j ∈ SJ, ‖a i‖*‖b j‖*eps) =
        AI*BJ*eps := by
    change (∑ i ∈ SI, ∑ j ∈ SJ, ‖a i‖*‖b j‖*eps) =
      (∑ i ∈ SI, ‖a i‖)*(∑ j ∈ SJ, ‖b j‖)*eps
    calc
      _ = (∑ i ∈ SI, ∑ j ∈ SJ, ‖a i‖*‖b j‖)*eps := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ = (∑ i ∈ SI, ‖a i‖*(∑ j ∈ SJ, ‖b j‖))*eps := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ((∑ i ∈ SI, ‖a i‖)*(∑ j ∈ SJ, ‖b j‖))*eps := by
        congr 1
        rw [Finset.sum_mul]
  have hGlobal :
      ‖∑ i ∈ SI, ∑ j ∈ SJ, a i*b j*H i j‖ ≤
        AI*BJ*eps := hTriangle.trans_eq hFactor
  have hSquare :
      ‖∑ i ∈ SI, ∑ j ∈ SJ, a i*b j*H i j‖^2 ≤
        (AI*BJ*eps)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hGlobal 2
  have hEnergy : AI^2*BJ^2 ≤ EI*EJ := by
    calc
      _ ≤ EI*BJ^2 :=
        mul_le_mul_of_nonneg_right hCSi (sq_nonneg _)
      _ ≤ EI*EJ :=
        mul_le_mul_of_nonneg_left hCSj hEI
  change ‖∑ i ∈ SI, ∑ j ∈ SJ, a i*b j*H i j‖^2 ≤
    eps^2*EI*EJ
  calc
    _ ≤ (AI*BJ*eps)^2 := hSquare
    _ = eps^2*(AI^2*BJ^2) := by ring
    _ ≤ eps^2*(EI*EJ) :=
      mul_le_mul_of_nonneg_left hEnergy (sq_nonneg _)
    _ = eps^2*EI*EJ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoGlobalFrameL1 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The true independent two-GLOBAL prime-label law has a
multiplicative L¹ character-frame cost, with NO independent
assumption on a subsequent complex test H(D_A,D_B).
The endpoint character kernels factor, whereas H can couple
both BIG prime groups arbitrarily. -/
theorem source_original_finite_two_global_frame_L1_bound434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (CX CY : ℝ) (hCX : 0 ≤ CX) (hCY : 0 ≤ CY)
    (pX : X) (pY : Y)
    (hX : (∑ x : X, wX x*‖KX x pX‖) ≤ CX)
    (hY : (∑ y : Y, wY y*‖KY y pY‖) ≤ CY) :
    (∑ q : X × Y,
      (wX q.1*wY q.2)*
        ‖KX q.1 pX*KY q.2 pY‖) ≤ CX*CY := by
  classical
  let A : X → ℝ := fun x => wX x*‖KX x pX‖
  let B : Y → ℝ := fun y => wY y*‖KY y pY‖
  have hB (y : Y) : 0 ≤ B y :=
    mul_nonneg (hwY y) (norm_nonneg _)
  have hBsum : 0 ≤ (∑ y : Y, B y) :=
    Finset.sum_nonneg (fun y _ => hB y)
  have hFactor :
      (∑ q : X × Y,
        (wX q.1*wY q.2)*
          ‖KX q.1 pX*KY q.2 pY‖) =
      (∑ x : X, A x)*(∑ y : Y, B y) := by
    calc
      _ = ∑ x : X, ∑ y : Y,
            (wX x*wY y)*‖KX x pX*KY y pY‖ := by
              rw [Fintype.sum_prod_type]
      _ = ∑ x : X, A x*(∑ y : Y, B y) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            dsimp [A,B]
            rw [norm_mul]
            ring
      _ = (∑ x : X, A x)*(∑ y : Y, B y) := by
           rw [Finset.sum_mul]
  rw [hFactor]
  have ha : (∑ x : X, A x) ≤ CX := hX
  have hb : (∑ y : Y, B y) ≤ CY := hY
  exact mul_le_mul ha hb hBsum hCX
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoGlobalMinorAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- A genuine two-GLOBAL pair of original finite primitive
character/cell mode families has the squared minor-arc
saving once every concrete mode has the C6 bound and
the TOTAL original weighted output coefficients have their
actual L1 budget. There is no assumption that the original
endpoint tests factor through numerical prime products.
This is the exact indexed application of the one-family
finite L1→L2 theorem to the source03 FOUR-fold expansion. -/
theorem source_original_finite_two_global_minor_mode_square434
    {IA IB : Type} (modesA : Finset IA) (modesB : Finset IB)
    (coef mode : IA → IB → ℂ)
    (save cost : ℝ)
    (hsave : 0 ≤ save) (hcost : 0 ≤ cost)
    (hMode : ∀ i ∈ modesA, ∀ j ∈ modesB,
      ‖mode i j‖^2 ≤ save)
    (hCost : (∑ i ∈ modesA, ∑ j ∈ modesB,
      ‖coef i j‖) ≤ cost) :
    ‖(∑ i ∈ modesA, ∑ j ∈ modesB,
        coef i j * mode i j)‖^2 ≤ cost^2*save := by
  have hRoot : 0 ≤ Real.sqrt save := Real.sqrt_nonneg _
  have hRootSq : (Real.sqrt save)^2 = save :=
    Real.sq_sqrt hsave
  have hNormMode (i : IA) (hi : i ∈ modesA)
      (j : IB) (hj : j ∈ modesB) :
      ‖mode i j‖ ≤ Real.sqrt save := by
    have hh := hMode i hi j hj
    nlinarith [norm_nonneg (mode i j)]
  have hTerm (i : IA) (hi : i ∈ modesA)
      (j : IB) (hj : j ∈ modesB) :
      ‖coef i j*mode i j‖ ≤
        ‖coef i j‖*Real.sqrt save := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hNormMode i hi j hj) (norm_nonneg _)
  have hEach (i : IA) (hi : i ∈ modesA) :
      ‖∑ j ∈ modesB, coef i j*mode i j‖ ≤
        ∑ j ∈ modesB, ‖coef i j‖*Real.sqrt save := by
    calc
      _ ≤ ∑ j ∈ modesB, ‖coef i j*mode i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ modesB, ‖coef i j‖*Real.sqrt save :=
        Finset.sum_le_sum (fun j hj => hTerm i hi j hj)
  have hSum :
      (∑ i ∈ modesA, ∑ j ∈ modesB,
        ‖coef i j‖*Real.sqrt save) =
      (∑ i ∈ modesA, ∑ j ∈ modesB,
        ‖coef i j‖) *Real.sqrt save := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hTri :
      ‖∑ i ∈ modesA, ∑ j ∈ modesB,
        coef i j*mode i j‖ ≤ cost*Real.sqrt save := by
    calc
      _ ≤ ∑ i ∈ modesA,
        ‖∑ j ∈ modesB, coef i j*mode i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ modesA, ∑ j ∈ modesB,
        ‖coef i j‖*Real.sqrt save :=
        Finset.sum_le_sum (fun i hi => hEach i hi)
      _ = (∑ i ∈ modesA, ∑ j ∈ modesB,
            ‖coef i j‖)*Real.sqrt save := hSum
      _ ≤ cost*Real.sqrt save :=
        mul_le_mul_of_nonneg_right hCost hRoot
  have hhSq := pow_le_pow_left₀ (norm_nonneg _) hTri 2
  calc
    _ ≤ (cost*Real.sqrt save)^2 := hhSq
    _ = cost^2*save := by rw [mul_pow,hRootSq]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoGlobalSlowKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- A rigorous TWO-GLOBAL frame perturbation estimate for a
slow *coupled* complex phase on original physical prime tuples.
Each true kernel is supported on its own matched GLOBAL
product-log cell. Inside the two cells, an arbitrary joint
multiplier phi(qA,qB) differs from its target value by at most
omega. Then integration through both kernels costs at most
their actual weighted L1 kernel mass times omega.
No separability assumption on the multiplier, no fictitious
independence assumption and NO xi^-1 pointwise kernel loss. -/
theorem source_original_finite_two_global_slow_kernel434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (gateX : X → Prop) (gateY : Y → Prop)
    (pX : X) (pY : Y)
    (hKX : ∀ q, ¬gateX q → KX q pX = 0)
    (hKY : ∀ q, ¬gateY q → KY q pY = 0)
    (phi : X × Y → ℂ) (omega C : ℝ)
    (hOmega : 0 ≤ omega)
    (hSlow : ∀ qX qY, gateX qX → gateY qY →
        ‖phi (qX,qY)-phi (pX,pY)‖ ≤ omega)
    (hL1 : (∑ q : X × Y,
       (wX q.1*wY q.2)*‖KX q.1 pX*KY q.2 pY‖) ≤ C) :
    ‖(∑ q : X × Y,
      (((wX q.1*wY q.2:ℝ):ℂ)*
        (KX q.1 pX*KY q.2 pY)) *
        (phi q-phi (pX,pY)))‖ ≤ C*omega := by
  classical
  let w : X × Y → ℝ := fun q => wX q.1*wY q.2
  let k : X × Y → ℂ := fun q => KX q.1 pX*KY q.2 pY
  let z : X × Y → ℂ := fun q =>
    (((w q:ℝ):ℂ)*k q)*(phi q-phi (pX,pY))
  have hw (q : X × Y) : 0 ≤ w q :=
    mul_nonneg (hwX q.1) (hwY q.2)
  have hpoint (q : X × Y) :
      ‖z q‖ ≤ (w q*‖k q‖)*omega := by
    by_cases hX : gateX q.1
    · by_cases hY : gateY q.2
      · have hphase := hSlow q.1 q.2 hX hY
        have hn : ‖z q‖ = (w q*‖k q‖)*
            ‖phi q-phi (pX,pY)‖ := by
          simp only [z, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (hw q)]
        rw [hn]
        exact mul_le_mul_of_nonneg_left hphase
          (mul_nonneg (hw q) (norm_nonneg _))
      · have hk : k q = 0 := by
          dsimp [k]
          rw [hKY q.2 hY]
          ring
        simp [z,hk]
    · have hk : k q = 0 := by
        dsimp [k]
        rw [hKX q.1 hX]
        ring
      simp [z,hk]
  change ‖∑ q : X × Y, z q‖ ≤ C*omega
  calc
    _ ≤ ∑ q : X × Y, ‖z q‖ := norm_sum_le _ _
    _ ≤ ∑ q : X × Y, (w q*‖k q‖)*omega :=
      Finset.sum_le_sum (fun q hq => hpoint q)
    _ = (∑ q : X × Y, w q*‖k q‖)*omega := by
      rw [Finset.sum_mul]
    _ ≤ C*omega := by
      have hh : (∑ q : X × Y, w q*‖k q‖) ≤ C := hL1
      exact mul_le_mul_of_nonneg_right hh hOmega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwistedSlowKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A uniform slow-phase perturbation estimate THROUGH the
two TRUE source03 independent GLOBAL kernels, with an entirely
COUPLED arbitrary twist H(D_A,D_B) of modulus at most one.
This avoids the INVALID approach of applying prime-character
Siegel-Walfisz to chi(p)*H(p).
It follows by applying the previously checked physical
slow-kernel lemma to ψ(D)=H(D)*(φ(D)-φ(X)): ψ(X)=0,
and the required Lipschitz difference stays ≤omega even though
H is arbitrary and state-dependent. -/
theorem source_original_finite_twisted_two_global_slow_kernel434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (gateX : X → Prop) (gateY : Y → Prop)
    (pX : X) (pY : Y)
    (hKX : ∀ q, ¬gateX q → KX q pX = 0)
    (hKY : ∀ q, ¬gateY q → KY q pY = 0)
    (phi H : X × Y → ℂ) (omega C : ℝ)
    (hOmega : 0 ≤ omega)
    (hH : ∀ q, ‖H q‖ ≤ 1)
    (hSlow : ∀ qX qY, gateX qX → gateY qY →
        ‖phi (qX,qY)-phi (pX,pY)‖ ≤ omega)
    (hL1 : (∑ q : X × Y,
       (wX q.1*wY q.2)*‖KX q.1 pX*KY q.2 pY‖) ≤ C) :
    ‖(∑ q : X × Y,
      (((wX q.1*wY q.2:ℝ):ℂ)*
        (KX q.1 pX*KY q.2 pY))*
        (H q*(phi q-phi (pX,pY))))‖ ≤ C*omega := by
  classical
  let psi : X × Y → ℂ :=
    fun q => H q*(phi q-phi (pX,pY))
  have hpsi0 : psi (pX,pY) = 0 := by
    simp [psi]
  have hpsislow (qX : X) (qY : Y)
      (hqX : gateX qX) (hqY : gateY qY) :
      ‖psi (qX,qY)-psi (pX,pY)‖ ≤ omega := by
    rw [hpsi0, sub_zero]
    dsimp [psi]
    rw [norm_mul]
    have hphi := hSlow qX qY hqX hqY
    calc
      _ ≤ (1:ℝ)*omega :=
        mul_le_mul (hH (qX,qY)) hphi
          (norm_nonneg _) (by norm_num)
      _ = omega := by ring
  have hRaw :=
    source_original_finite_two_global_slow_kernel434
      wX wY hwX hwY KX KY gateX gateY pX pY
      hKX hKY psi omega C hOmega hpsislow hL1
  convert hRaw using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro q hq
  rw [hpsi0,sub_zero]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoSidedMinorFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- A genuine finite physical two-ENDPOINT prime-label bilinear
sum, with arbitrary complex endpoint tests and a jointly
dependent oscillating phase. Window cutoffs can be encoded
by zeros of fA/fB. No assumption that tests are functions
of integer products. -/
noncomputable def sourceOriginalFiniteTwoSidedMinorBilinear434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℂ) (wY : Y → ℂ)
    (fA : X → ℂ) (fB : Y → ℂ)
    (H : X × Y → ℂ) : ℂ :=
  ∑ q : X × Y,
    wX q.1*wY q.2*fA q.1*fB q.2*H q

/-- Expansion on BOTH genuinely independent sets of physical
prime modes, while the phase H may be fully coupled.
Every endpoint test fA/fB is an arbitrary mark-dependent
function. This is the exact finite Fubini bridge between
the source03 primitive Knu factorization and C275 true
BIG/BIG physical minor arithmetic estimate. -/
theorem source_original_finite_two_sided_minor_mode_fubini434
    {X Y IA IB : Type}
    [Fintype X] [Fintype Y]
    (indicesA : Finset IA) (indicesB : Finset IB)
    (a : IA → ℂ) (b : IB → ℂ)
    (modeA : IA → X → ℂ) (modeB : IB → Y → ℂ)
    (wX : X → ℂ) (wY : Y → ℂ)
    (fA : X → ℂ) (fB : Y → ℂ)
    (H : X × Y → ℂ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wX wY
      (fun x => fA x * (∑ i ∈ indicesA, a i*modeA i x))
      (fun y => fB y * (∑ j ∈ indicesB, b j*modeB j y))
      H =
    ∑ i ∈ indicesA, ∑ j ∈ indicesB,
      (a i*b j) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wX wY
        (fun x => fA x*modeA i x)
        (fun y => fB y*modeB j y)
        H := by
  classical
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  have hpoint (q : X × Y) :
      wX q.1*wY q.2*
        (fA q.1*(∑ i ∈ indicesA, a i*modeA i q.1))*
        (fB q.2*(∑ j ∈ indicesB, b j*modeB j q.2))*H q =
      ∑ i ∈ indicesA, ∑ j ∈ indicesB,
        (a i*b j) *
        (wX q.1*wY q.2*
          (fA q.1*modeA i q.1)*
          (fB q.2*modeB j q.2)*H q) := by
    calc
      _ = (∑ i ∈ indicesA, a i*modeA i q.1) *
          (∑ j ∈ indicesB, b j*modeB j q.2) *
          (wX q.1*wY q.2*fA q.1*fB q.2*H q) := by
        ring
      _ = ∑ i ∈ indicesA, ∑ j ∈ indicesB,
        (a i*b j) *
        (wX q.1*wY q.2*
          (fA q.1*modeA i q.1)*
          (fB q.2*modeB j q.2)*H q) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ = ∑ q : X × Y,
      ∑ i ∈ indicesA, ∑ j ∈ indicesB,
        (a i*b j) *
        (wX q.1*wY q.2*
          (fA q.1*modeA i q.1)*
          (fB q.2*modeB j q.2)*H q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint q
    _ = ∑ i ∈ indicesA,
      ∑ j ∈ indicesB, ∑ q : X × Y,
        (a i*b j) *
        (wX q.1*wY q.2*
          (fA q.1*modeA i q.1)*
          (fB q.2*modeB j q.2)*H q) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i ∈ indicesA, ∑ j ∈ indicesB,
      (a i*b j) *
        (∑ q : X × Y,
         wX q.1*wY q.2*
           (fA q.1*modeA i q.1)*
           (fB q.2*modeB j q.2)*H q) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteMellinBilinearTransfer -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Exact insertion of the SOURCE03 two-product Mellin factor
into a physical signed bilinear kernel via SEPARATE endpoint
multipliers. The kernel H(x,y) may be fully coupled and
contain the actual original -k θ Fourier phase, full primitive
χA χB comparison, true GLOBAL cells, or arbitrary marks.
There is no change of kernel, no fake factorization of H
and no loss in weighted L² endpoint norms. -/
theorem source_original_finite_mellin_bilinear_transfer434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wA : X → ℂ) (wB : Y → ℂ)
    (fA : X → ℂ) (fB : Y → ℂ)
    (prodA : X → ℕ) (prodB : Y → ℕ)
    (hA : ∀ x, 0 < prodA x)
    (hB : ∀ y, 0 < prodB y)
    (H : X × Y → ℂ) (ζ : ℝ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun x => fA x*sourceOriginalPureMellinPhase434 ζ (prodA x))
      (fun y => fB y*sourceOriginalPureMellinPhase434 ζ (prodB y))
      H =
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB fA fB
      (fun q => H q *
        sourceOriginalPureMellinPhase434 ζ
          (prodA q.1*prodB q.2)) := by
  classical
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  rw [source_original_pure_mellin_product_factor434
    ζ (prodA q.1) (prodB q.2) (hA q.1) (hB q.2)]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteMatchedIcoBilinear -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- TRUE SOURCE03 integer dyadic interval [M,2M) equals the
actual C6 integer-window mask M + range(M).
No interpolation, changing window length or assuming M>0. -/
theorem source_original_ico_eq_C6_range434 (M n : ℕ) :
    n ∈ Finset.Ico M (2*M) ↔
      n ∈ (Finset.range M).image (fun i => M+i) := by
  constructor
  · intro h
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp h
    apply Finset.mem_image.mpr
    refine ⟨n-M,Finset.mem_range.mpr (by omega),?_⟩
    omega
  · intro h
    obtain ⟨i,hi,hn⟩ := Finset.mem_image.mp h
    have hlt : i < M := Finset.mem_range.mp hi
    apply Finset.mem_Ico.mpr
    constructor <;> omega
/-- Equality of a genuine MATCHED four-dyad source03 physical
prime-pair mask with the exact C6 two-sided weighted bilinear,
including arbitrary jointly coupled primitive Knu/phase kernel.
This is the bridge needed to apply checked C6 spectral saving
to the exact input rectangles of a moving output GLOBAL cell. -/
theorem source_original_finite_ico_mask_bilinear434
    {A B : Type} [Fintype A] [Fintype B]
    (wA : A → ℂ) (wB : B → ℂ)
    (DA : A → ℕ) (DB : B → ℕ)
    (M N : ℕ) (H : A × B → ℂ) :
    (∑ q : A × B,
      if DA q.1 ∈ Finset.Ico M (2*M) ∧
         DB q.2 ∈ Finset.Ico N (2*N)
      then wA q.1*wB q.2*H q else 0) =
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if DA a ∈ (Finset.range M).image
        (fun i => M+i) then (1:ℂ) else 0)
      (fun b => if DB b ∈ (Finset.range N).image
        (fun j => N+j) then (1:ℂ) else 0)
      H := by
  classical
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  apply Finset.sum_congr rfl
  intro q hq
  have heqA : (DA q.1 ∈ (Finset.range M).image
      (fun i => M+i)) ↔ DA q.1 ∈ Finset.Ico M (2*M) :=
    (source_original_ico_eq_C6_range434 M (DA q.1)).symm
  have heqB : (DB q.2 ∈ (Finset.range N).image
      (fun j => N+j)) ↔ DB q.2 ∈ Finset.Ico N (2*N) :=
    (source_original_ico_eq_C6_range434 N (DB q.2)).symm
  by_cases ha : DA q.1 ∈ Finset.Ico M (2*M)
  · by_cases hb : DB q.2 ∈ Finset.Ico N (2*N)
    · simp [ha,hb,heqA.mpr ha,heqB.mpr hb]
    · simp [ha,hb,heqA.mpr ha,heqB, hb]
  · have hna : ¬ DA q.1 ∈ (Finset.range M).image
      (fun i => M+i) := fun hn => ha (heqA.mp hn)
    simp [ha,hna]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteOutputWindowRangeIco -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- An ACTUAL source03 OUTPUT C6 dyad [M,2M) may be written
either as half-open integer interval or M+range M; the entire
two-output signed Fourier/Mellin bilinear kernel is literally
unchanged. Works for arbitrary complex coeffs and phases, not
only primitive Knu or factorized phases. -/
theorem source_original_finite_output_window_ico_range434
    (SA SB : Finset ℕ) (a b : ℕ → ℂ)
    (F : ℕ → ℕ → ℂ) (M N : ℕ) :
    (∑ n∈SA,∑ mm∈SB,
      (if n∈Finset.Ico M (2*M) then a n else 0) *
      (if mm∈Finset.Ico N (2*N) then b mm else 0) *
      F n mm) =
    (∑ n∈SA,∑ mm∈SB,
      (if n∈(Finset.range M).image (fun i => M+i)
        then a n else 0) *
      (if mm∈(Finset.range N).image (fun j => N+j)
        then b mm else 0) *
      F n mm) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro mm hmm
  have ha := source_original_ico_eq_C6_range434 M n
  have hb := source_original_ico_eq_C6_range434 N mm
  by_cases ha0 : n∈Finset.Ico M (2*M)
  · have ha1 := ha.mp ha0
    by_cases hb0 : mm∈Finset.Ico N (2*N)
    · have hb1 := hb.mp hb0
      simp [ha0,ha1,hb0,hb1]
    · have hb1 : ¬mm∈(Finset.range N).image (fun j => N+j) :=
        fun hh => hb0 (hb.mpr hh)
      simp [ha0,ha1,hb0,hb1]
  · have ha1 : ¬n∈(Finset.range M).image (fun i => M+i) :=
      fun hh => ha0 (ha.mpr hh)
    simp [ha0,ha1]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFourDyadTriangle -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Exact factor sixteen for assembling four physical
C6 dyadic rectangles. Each of the four squares is bounded
by the same K>=0. No loss of an extra power of L. -/
theorem source_original_four_dyad_triangle_square434
    (a b c d : ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ‖a‖^2 ≤ K) (hb : ‖b‖^2 ≤ K)
    (hc : ‖c‖^2 ≤ K) (hd : ‖d‖^2 ≤ K) :
    ‖a+b+c+d‖^2 ≤ 16*K := by
  have hSq : (Real.sqrt K)^2 = K := Real.sq_sqrt hK
  have hPos : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have ha' : ‖a‖ ≤ Real.sqrt K := by
    nlinarith [norm_nonneg a]
  have hb' : ‖b‖ ≤ Real.sqrt K := by
    nlinarith [norm_nonneg b]
  have hc' : ‖c‖ ≤ Real.sqrt K := by
    nlinarith [norm_nonneg c]
  have hd' : ‖d‖ ≤ Real.sqrt K := by
    nlinarith [norm_nonneg d]
  have hFirst : ‖a+b+c+d‖ ≤
      ‖a‖+‖b‖+‖c‖+‖d‖ := by
    have h1 := norm_add_le a b
    have h2 := norm_add_le (a+b) c
    have h3 := norm_add_le (a+b+c) d
    linarith
  have hTotal : ‖a+b+c+d‖ ≤ 4*Real.sqrt K := by
    linarith
  have hTotalSq := pow_le_pow_left₀ (norm_nonneg _) hTotal 2
  nlinarith [hTotalSq,hSq]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFractionalDyadicLogAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Quantitative absorption of the *true number of clipped dyads*.
If n ≤ L^d, the physical BIG lower endpoint exceeds exp(L^gamma),
and gamma*A ≥ d+B, then the original source03 Gram error
n*(K/V)*(log(u+1))^(-A) saves L^(-B), without any character
or GLOBAL-cell count factor. -/
theorem source_original_fractional_dyadic_log_absorb434
    (n u : ℕ) (L gamma d A B K V : ℝ)
    (hL : 1 ≤ L) (hgamma : 0 < gamma)
    (hA : 0 < A) (hK : 0 ≤ K) (hV : 0 < V)
    (hdyads : (n:ℝ) ≤ L^d)
    (hBIG : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (hExponent : d+B ≤ gamma*A) :
    (n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A)) ≤
      (K/V)*L^(-B) := by
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hpowPos : 0 < L^gamma := Real.rpow_pos_of_pos hLpos _
  have hlog : L^gamma ≤ Real.log ((u+1:ℕ):ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hBIG
    simpa only [Real.log_exp] using hh
  have hlogpow :
      (Real.log ((u+1:ℕ):ℝ))^(-A) ≤
        (L^gamma)^(-A) :=
    Real.rpow_le_rpow_of_nonpos hpowPos hlog (by linarith)
  have hrpow :
      (L^gamma)^(-A) = L^(-gamma*A) := by
    rw [← Real.rpow_mul hLnonneg]
    congr 1
    ring
  have hratio : 0 ≤ K/V := div_nonneg hK hV.le
  have hleft : 0 ≤ (Real.log ((u+1:ℕ):ℝ))^(-A) :=
    Real.rpow_nonneg (Real.log_nonneg
      (by
        have hh : 1 ≤ ((u+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le u)
        exact hh)) _
  have hright : 0 ≤ L^d := Real.rpow_nonneg hLnonneg _
  have hproduct :
      (n:ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A) ≤
        L^d * L^(-gamma*A) := by
    calc
      _ ≤ L^d * (L^gamma)^(-A) :=
        mul_le_mul hdyads hlogpow hleft hright
      _ = L^d * L^(-gamma*A) := by rw [hrpow]
  have hExp : d-gamma*A ≤ -B := by linarith
  have hPowBound : L^(d-gamma*A) ≤ L^(-B) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  calc
    (n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A)) =
      (K/V)*((n:ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)) := by ring
    _ ≤ (K/V)*(L^d*L^(-gamma*A)) :=
      mul_le_mul_of_nonneg_left hproduct hratio
    _ = (K/V)*L^(d-gamma*A) := by
      rw [← Real.rpow_add hLpos]
      ring
    _ ≤ (K/V)*L^(-B) :=
      mul_le_mul_of_nonneg_left hPowBound hratio
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGhostBirthFibreFactorial -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- All ordered, distinct source birth tuples with prescribed prime set.
The ordering is retained until its original 1/b! has been summed. -/
abbrev SourceOriginalGhostBirthFibre434 {P : Type} [Fintype P] [DecidableEq P]
    (b : ℕ) (s : Finset P) :=
  {f : Fin b → P // Function.Injective f ∧ Finset.univ.image f=s}

def sourceOriginalGhostBirthFibreEquiv434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (s : Finset P) :
    SourceOriginalGhostBirthFibre434 b s ≃ (Fin b ≃ ↥s) where
  toFun f := Equiv.ofBijective
    (fun i => (⟨f.1 i,by
      have hh : f.1 i ∈ Finset.univ.image f.1 := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      simpa only [f.2.2] using hh⟩:↥s))
    (by
      constructor
      · intro i j h
        exact f.2.1 (congrArg Subtype.val h)
      · intro y
        have hy : y.1 ∈ Finset.univ.image f.1 := by rw [f.2.2];exact y.2
        obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hy
        exact ⟨i,Subtype.ext he⟩)
  invFun e := ⟨fun i => (e i).1,
    (by intro i j h;exact e.injective (Subtype.ext h)),
    (by
      ext p
      constructor
      · intro hp
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
        exact (e i).2
      · intro hp
        obtain ⟨i,he⟩ := e.surjective ⟨p,hp⟩
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val he⟩)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

theorem source_original_GHOST_birth_fibre_factorial434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (s : Finset P)
    (hs : s.card=b) :
    Fintype.card (SourceOriginalGhostBirthFibre434 b s) = b.factorial := by
  rw [Fintype.card_congr (sourceOriginalGhostBirthFibreEquiv434 b s)]
  have he : Fintype.card (Fin b) = Fintype.card ↥s := by simp [hs]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq he),Fintype.card_fin]

theorem source_original_GHOST_birth_fibre_product434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (s : Finset P)
    (f : SourceOriginalGhostBirthFibre434 b s) (w : P → ℂ) :
    (∏ i : Fin b,w (f.1 i)) = ∏ p ∈ s,w p := by
  calc
    _ = ∏ p ∈ Finset.univ.image f.1,w p := by
      symm
      exact Finset.prod_image (fun i hi j hj h => f.2.1 h)
    _ = _ := congrArg (fun t : Finset P => ∏ p ∈ t,w p) f.2.2

/-- Exact cancellation of the original birth factorial against ordered
distinct witnesses, including arbitrary complex set-dependent tests.
No new factorial is inserted into E or into the Hilbert measure. -/
theorem source_original_GHOST_distinct_birth_factorial_sum434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (s : Finset P)
    (hs : s.card=b) (w : P → ℂ) (F : Finset P → ℂ) :
    (1/(b.factorial:ℂ)) *
      (∑ f : SourceOriginalGhostBirthFibre434 b s,
        (∏ i : Fin b,w (f.1 i))*F (Finset.univ.image f.1)) =
      (∏ p ∈ s,w p)*F s := by
  have hterm (f : SourceOriginalGhostBirthFibre434 b s) :
      (∏ i : Fin b,w (f.1 i))*F (Finset.univ.image f.1) =
        (∏ p ∈ s,w p)*F s := by
    rw [source_original_GHOST_birth_fibre_product434 b s f w,f.2.2]
  simp_rw [hterm]
  rw [Finset.sum_const,Finset.card_univ,source_original_GHOST_birth_fibre_factorial434 b s hs,
    nsmul_eq_mul]
  have hb : (b.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  field_simp

/-- Literal sourceGhostTerm, not a surrogate birth law: in an empty
OLD sector, summing all orders of a globally distinct fresh set cancels
its one 1/b! exactly. The signs and source birth masses stay intact. -/
theorem source_original_GHOST_empty_old_birth_fibre_exact434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (s : Finset P)
    (hs : s.card=b) (zero : P → Prop) [DecidablePred zero]
    (alpha chi gamma : ℂ) (nu : P → ℂ) (F : Finset P → ℂ) :
    (∑ f : SourceOriginalGhostBirthFibre434 b s,
      sourceGhostTerm [] zero ∅ f.1 alpha chi gamma nu *
        F (Finset.univ.image f.1)) =
      gamma^b*(∏ p ∈ s,nu p)*F s := by
  have hz : zeroOld ([]:List P) zero = ∅ := by ext i;exact Fin.elim0 i
  have hterm (f : SourceOriginalGhostBirthFibre434 b s) :
      sourceGhostTerm [] zero ∅ f.1 alpha chi gamma nu *
        F (Finset.univ.image f.1) =
      (1/(b.factorial:ℂ))*((∏ i : Fin b,(gamma*nu (f.1 i)))*
        F (Finset.univ.image f.1)) := by
    simp only [sourceGhostTerm,hz,Finset.card_empty,Nat.sub_zero,pow_zero,one_mul,
      Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  simp_rw [hterm]
  rw [←Finset.mul_sum,source_original_GHOST_distinct_birth_factorial_sum434 b s hs (fun p => gamma*nu p) F]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,hs]
end Green64Analytic.CorrelationSquare

end

end

