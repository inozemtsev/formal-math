module

public import Green64.Library.Correlation.Part037
public import Mathlib
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part047
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part042

@[expose] public section

/-!
# Correlation / Part038

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalFiniteGramSynthesisNorm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- From the exact finite C6/B31 complex Gram matrix operator
estimate to its quadratic coefficient form, with NO character
count loss: `||G a||_2 <= R ||a||_2` implies
`|<a,G a>| <= R ||a||_2^2`.
Valid for arbitrary complex Hermitian or non-Hermitian G. -/
theorem source_original_finite_gram_quadratic_from_operator434
    {C : Type} [Fintype C]
    (G : C → C → ℂ) (a : C → ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hOp :
      (∑ c : C, ‖∑ d : C, G c d*a d‖^2) ≤
        R^2*(∑ c : C, ‖a c‖^2)) :
    ‖(∑ c : C, star (a c)*
      (∑ d : C, G c d*a d))‖ ≤
        R*(∑ c : C, ‖a c‖^2) := by
  classical
  let A : ℝ := ∑ c : C, ‖a c‖^2
  let B : ℝ := ∑ c : C, ‖∑ d : C, G c d*a d‖^2
  let S : ℝ := ∑ c : C, ‖a c‖*
    ‖∑ d : C, G c d*a d‖
  have hA : 0 ≤ A := Finset.sum_nonneg
    (fun c hc => sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg
    (fun c hc => sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg
    (fun c hc => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hOp' : B ≤ R^2*A := hOp
  have hCS : S^2 ≤ A*B := by
    exact Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset C)
      (fun c => ‖a c‖)
      (fun c => ‖∑ d : C, G c d*a d‖)
  have hSq : S^2 ≤ (R*A)^2 := by
    calc
      _ ≤ A*B := hCS
      _ ≤ A*(R^2*A) := mul_le_mul_of_nonneg_left hOp' hA
      _ = (R*A)^2 := by ring
  have hBound : S ≤ R*A := by
    have hRA : 0 ≤ R*A := mul_nonneg hR hA
    nlinarith [hSq]
  have hNorm :
      ‖(∑ c : C, star (a c)*
        (∑ d : C, G c d*a d))‖ ≤ S := by
    calc
      _ ≤ ∑ c : C, ‖star (a c)*
          (∑ d : C, G c d*a d)‖ := norm_sum_le _ _
      _ = S := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [norm_mul, norm_star]
  exact hNorm.trans hBound
/-- The genuine finite SOURCE03/B31 character synthesis
on a nonnegative physical weighted source space has a sharp
L2 frame bound from its ACTUAL Gram operator L2 bound.
This is the missing Gram-to-synthesis step for arbitrary
non-factorized complex character coefficient vectors;
no card(C) loss or unexplained test independence. -/
theorem source_original_finite_gram_synthesis_frame434
    {X C : Type} [Fintype X] [Fintype C]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (chi : X → C → ℂ) (a : C → ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hOp : let G : C → C → ℂ := fun c d =>
        ∑ x : X, (w x:ℂ)*star (chi x c)*chi x d
      (∑ c : C, ‖∑ d : C, G c d*a d‖^2) ≤
        R^2*(∑ c : C, ‖a c‖^2)) :
    (∑ x : X, w x*‖∑ c : C, chi x c*a c‖^2) ≤
      R*(∑ c : C, ‖a c‖^2) := by
  classical
  let G : C → C → ℂ := fun c d =>
    ∑ x : X, (w x:ℂ)*star (chi x c)*chi x d
  let synth : X → ℂ := fun x => ∑ c : C, chi x c*a c
  let E : ℝ := ∑ x : X, w x*‖synth x‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg
    (fun x hx => mul_nonneg (hw x) (sq_nonneg _))
  have hEq (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = star z*z := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
      (Complex.normSq_eq_conj_mul_self (z := z))
  have hEnergy :
      (E:ℂ) = ∑ x : X, (w x:ℂ)*star (synth x)*synth x := by
    dsimp only [E]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Complex.ofReal_mul,hEq]
    ring
  have hPair :
      (E:ℂ) = ∑ c : C, star (a c)*
         ∑ d : C, G c d*a d := by
    calc
      _ = ∑ x : X, (w x:ℂ)*star (synth x)*synth x :=
        hEnergy
      _ = ∑ c : C, star (a c)*
         ∑ d : C, G c d*a d := by
          simpa only [synth,G] using
            source_original_finite_synthesis_gram_identity434
              w chi a a
  have hQuadratic :=
    source_original_finite_gram_quadratic_from_operator434
      G a R hR hOp
  have hNormE : ‖(E:ℂ)‖ = E := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
  change E ≤ R*(∑ c : C, ‖a c‖^2)
  calc
    E = ‖(E:ℂ)‖ := hNormE.symm
    _ = ‖∑ c : C, star (a c)*
         ∑ d : C, G c d*a d‖ :=
          congrArg (fun z : ℂ => ‖z‖) hPair
    _ ≤ _ := hQuadratic
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalGramPairing -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- An EXACT physical synthesis/Gram pairing for the SOURCE03
primitive characters at their real conductor levels, on the
original harmonic product-prime probability space and the
TRUE moving GLOBAL product-log cell. No independent-marks proxy,
hypothetical test H, or replacement character distribution. -/
theorem source_original_physical_synthesis_gram_pairing434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (a b : sourceOriginalPrimitiveFamily434 Q → ℂ) :
    (∑ p : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu p:ℂ) *
        (if sourceOriginalLiteralLogCell434 h j
             (sourceOriginalGramPrimeProduct434 S p)
         then star (sourceOriginalPhysicalGramSynthesis434 S Q a p) *
           sourceOriginalPhysicalGramSynthesis434 S Q b p
         else 0)) =
    ∑ c : sourceOriginalPrimitiveFamily434 Q, star (a c) *
      ∑ d : sourceOriginalPrimitiveFamily434 Q,
        sourceOriginalActualPrimitiveGramEntry434
          S mu h j Q c.val d.val * b d := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let w : SourceOriginalGramPrimeTuple434 S → ℝ := fun p =>
    if sourceOriginalLiteralLogCell434 h j
         (sourceOriginalGramPrimeProduct434 S p)
    then sourceOriginalGramPrimeMass434 S mu p else 0
  let chi : SourceOriginalGramPrimeTuple434 S → Fam → ℂ :=
    fun p c => c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ) :
       ZMod (c.val.1.val+1))
  have hLeft :
      (∑ p : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu p:ℂ) *
        (if sourceOriginalLiteralLogCell434 h j
             (sourceOriginalGramPrimeProduct434 S p)
         then star (sourceOriginalPhysicalGramSynthesis434 S Q a p) *
           sourceOriginalPhysicalGramSynthesis434 S Q b p
         else 0)) =
      (∑ p : SourceOriginalGramPrimeTuple434 S,
         (w p:ℂ) *
           star (∑ c : Fam, chi p c * a c) *
           (∑ d : Fam, chi p d * b d)) := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : sourceOriginalLiteralLogCell434 h j
        (sourceOriginalGramPrimeProduct434 S p)
    · simp only [if_pos hc, w,
        sourceOriginalPhysicalGramSynthesis434, chi]
      ring
    · simp [hc, w]
  have hEntry (c d : Fam) :
      (∑ p : SourceOriginalGramPrimeTuple434 S,
       (w p:ℂ)*star (chi p c)*chi p d) =
      sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c.val d.val := by
    unfold sourceOriginalActualPrimitiveGramEntry434
      sourceOriginalGramCellEntry434
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : sourceOriginalLiteralLogCell434 h j
        (sourceOriginalGramPrimeProduct434 S p)
    · simp only [w, chi, if_pos hc]
      ring
    · simp [w, hc]
  have hBase :=
    source_original_finite_synthesis_gram_identity434 w chi a b
  calc
    _ = (∑ p : SourceOriginalGramPrimeTuple434 S,
       (w p:ℂ) * star (∑ c : Fam, chi p c * a c) *
          (∑ d : Fam, chi p d * b d)) := hLeft
    _ = ∑ c : Fam, star (a c) *
         ∑ d : Fam, (∑ p : SourceOriginalGramPrimeTuple434 S,
           (w p:ℂ) * star (chi p c) * chi p d) * b d := hBase
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [hEntry c d]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFrameKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- On ACTUAL physical SOURCE03 prime-product tuples, the
single-cell primitive comparison kernel is EXACTLY the
outer-product character frame with normalization by the
real, genuine GLOBAL-cell probability. It is not an operator
bound on arbitrary tests or a new hypothesized ideal kernel. -/
theorem source_original_physical_primitive_cell_frame_kernel434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (p q : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
      (sourceOriginalGramPrimeProduct434 S p)
      (sourceOriginalGramPrimeProduct434 S q) =
    (if sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S p) ∧
        sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S q)
      then
        ((sourceOriginalRealGramCellMass434 S mu h j:ℂ)⁻¹) *
        ∑ c : sourceOriginalPrimitiveFamily434 Q,
          star (c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ) :
             ZMod (c.val.1.val+1))) *
          c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ) :
             ZMod (c.val.1.val+1))
      else 0) := by
  classical
  unfold sourceOriginalActualPrimitiveGlobalKernel434
    sourceOriginalCharacterCellKernel434
  rw [Finset.sum_singleton]
  by_cases hc :
      sourceOriginalLiteralLogCell434 h j
        (sourceOriginalGramPrimeProduct434 S p) ∧
      sourceOriginalLiteralLogCell434 h j
        (sourceOriginalGramPrimeProduct434 S q)
  · simp only [if_pos hc]
    let chars := sourceOriginalActualPrimitiveCharacters434 Q
    have hattach :
      (∑ c ∈ chars,
          star (c.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ) :
             ZMod (c.1.val+1))) *
          c.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ) :
             ZMod (c.1.val+1))) =
      (∑ c : sourceOriginalPrimitiveFamily434 Q,
          star (c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ) :
             ZMod (c.val.1.val+1))) *
          c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ) :
             ZMod (c.val.1.val+1))) := by
      simpa only [chars, sourceOriginalPrimitiveFamily434,
        Finset.univ_eq_attach] using
        (Finset.sum_attach
          (sourceOriginalActualPrimitiveCharacters434 Q)
          (fun c =>
            star (c.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ) :
              ZMod (c.1.val+1))) *
            c.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ) :
              ZMod (c.1.val+1)))).symm
    exact congrArg
      (fun z : ℂ =>
        ((sourceOriginalRealGramCellMass434 S mu h j:ℂ)⁻¹)*z)
      hattach
  · simp only [if_neg hc]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalActiveFrameKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- EXACT physical primitive-frame decomposition of the original
single GLOBAL kernel on ALL actual selected active log-product
cells, with their genuine harmonic probability nu_j and the
original two character-product arguments. This is equality of
the ORIGINAL Knu frame kernel, not a bound or assumption on it. -/
theorem source_original_physical_active_primitive_frame_kernel434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (active : Finset ℤ) (Q : ℕ)
    (p q : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalActualPrimitiveGlobalKernel434
      Q active h (sourceOriginalRealGramCellMass434 S mu h)
      (sourceOriginalGramPrimeProduct434 S p)
      (sourceOriginalGramPrimeProduct434 S q) =
    ∑ j ∈ active,
      if sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S p) ∧
         sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S q)
      then (sourceOriginalRealGramCellMass434 S mu h j:ℂ)⁻¹ *
        ∑ c : sourceOriginalPrimitiveFamily434 Q,
          star (c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
            ZMod (c.val.1.val+1))) *
          c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
            ZMod (c.val.1.val+1))
      else 0 := by
  classical
  unfold sourceOriginalActualPrimitiveGlobalKernel434
    sourceOriginalCharacterCellKernel434
  apply Finset.sum_congr rfl
  intro j hj
  have hsingle :=
    source_original_physical_primitive_cell_frame_kernel434
      S mu h j Q p q
  unfold sourceOriginalActualPrimitiveGlobalKernel434
    sourceOriginalCharacterCellKernel434 at hsingle
  simpa only [Finset.sum_singleton] using hsingle
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCharacterKernelIdentity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual original physical source03 primitive GLOBAL kernel,
applied at (D,X) to a genuine primitive character of D and averaged
over the real harmonic prime-product distribution, produces EXACTLY
the normalized character Gram matrix evaluated at X.
The kernel arguments have the ORIGINAL D-first X-second orientation,
all character conductors and the half-open log cell are unchanged.
This is the missing algebraic link to pointwise major-arc reproduction. -/
theorem source_original_actual_character_kernel_gram_action434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (p : SourceOriginalGramPrimeTuple434 S)
    (hp : sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S p))
    (e : sourceOriginalPrimitiveFamily434 Q) :
    (∑ q : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S q)
        (sourceOriginalGramPrimeProduct434 S p) *
      e.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
        ZMod (e.val.1.val+1))) =
    ∑ c : sourceOriginalPrimitiveFamily434 Q,
      (sourceOriginalActualPrimitiveGramEntry434 S mu h j Q
        c.val e.val / (sourceOriginalRealGramCellMass434 S mu h j:ℂ)) *
      c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
        ZMod (c.val.1.val+1)) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let chi : X → Fam → ℂ := fun q c =>
    c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
      ZMod (c.val.1.val+1))
  let gate : X → Prop := fun q =>
    sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S q)
  let nu : ℝ := sourceOriginalRealGramCellMass434 S mu h j
  have hp' : gate p := hp
  have hKernel (q : X) :
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S q)
        (sourceOriginalGramPrimeProduct434 S p) =
      (if gate q ∧ gate p then (nu:ℂ)⁻¹ *
        (∑ c : Fam, star (chi q c)*chi p c)
        else 0) := by
    simpa only [gate, chi, nu, Fam, X] using
      (source_original_physical_primitive_cell_frame_kernel434
        S mu h j Q q p)
  have hEntry (c : Fam) :
      (∑ q : X, (w q:ℂ) *
        (if gate q then star (chi q c)*chi q e else 0)) =
      sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c.val e.val := by
    unfold sourceOriginalActualPrimitiveGramEntry434
      sourceOriginalGramCellEntry434
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hc : gate q
    · simp only [gate, chi, w, if_pos hc]
    · simp only [gate, chi, w, if_neg hc, mul_zero]
  calc
    _ = (∑ q : X, (w q:ℂ) *
         (if gate q ∧ gate p then (nu:ℂ)⁻¹ *
           (∑ c : Fam, star (chi q c)*chi p c)
          else 0) * chi q e) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hKernel q]
    _ = ∑ c : Fam,
        ((∑ q : X, (w q:ℂ) *
          (if gate q then star (chi q c)*chi q e else 0))/(nu:ℂ)) *
        chi p c :=
      source_original_finite_character_kernel_reproduction434
        w chi gate nu p hp' e
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hEntry c]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalConditionalFrameL1 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ACTUAL original source03 one-GLOBAL primitive-character
physical frame has L¹ operator mass ≤ #true primitive chars
when evaluated at any retained target prime-tuple X.
Unlike the supremum bound Q²*xi⁻¹, this is independent of
the cell retention cutoff xi: the true normalized harmonic
mass ν_j cancels its denominator exactly.
No SW, no fake uniform prime law, no hypothetical
bound for an arbitrary state-dependent test. -/
theorem source_original_actual_primitive_global_conditional_L1_434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (Q : ℕ) (h : ℝ) (j : ℤ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMass : xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
    (p : SourceOriginalGramPrimeTuple434 S)
    (hp : sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S p)) :
    (∑ q : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu q *
      ‖sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S q)
        (sourceOriginalGramPrimeProduct434 S p)‖) ≤
    (Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let chi : X → Fam → ℂ := fun q c =>
    c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
       ZMod (c.val.1.val+1))
  let gate : X → Prop := fun q =>
    sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S q)
  let nu : ℝ := sourceOriginalRealGramCellMass434 S mu h j
  have hnu : 0 < nu := hxi.trans_le hMass
  have hw (q : X) : 0 ≤ w q :=
    source_original_physical_gram_prime_mass_nonneg434
      S mu hmu q
  have hchi (q : X) (c : Fam) : ‖chi q c‖ ≤ 1 :=
    (c.val.2.norm_le_one _)
  have hmass :
      nu = ∑ q : X, (if gate q then w q else 0) := by
    rfl
  have hpoint (q : X) :
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S q)
        (sourceOriginalGramPrimeProduct434 S p) =
      (if gate q ∧ gate p then (nu:ℂ)⁻¹ *
          ∑ c : Fam, star (chi q c)*chi p c
       else 0) := by
    simpa only [gate,nu,chi,Fam] using
      (source_original_physical_primitive_cell_frame_kernel434
        S mu h j Q q p)
  have hgeneric := source_original_finite_conditional_frame_L1_bound434
    w hw chi hchi gate nu hnu hmass p hp
  calc
    _ = ∑ q : X, w q *
         ‖(if gate q ∧ gate p then (nu:ℂ)⁻¹ *
             ∑ c : Fam, star (chi q c)*chi p c
           else 0)‖ := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hpoint q]
    _ ≤ (Fintype.card Fam:ℝ) := hgeneric
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFrameAction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The ORIGINAL physical one-GLOBAL primitive comparison kernel,
as a linear operator on ARBITRARY complex output tests f of every
true prime-labelled mark tuple, is EXACTLY conditional character
analysis followed by synthesis. No H(p) independence or mean-zero
shortcut. The physical prime-tuple mass, GLOBAL-cell test,
true primitive conductor and normalization nu_j are unchanged. -/
theorem source_original_actual_physical_frame_operator_exact434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (p : SourceOriginalGramPrimeTuple434 S) :
    (∑ q : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S p)
        (sourceOriginalGramPrimeProduct434 S q) * f q) =
    (if sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S p)
      then (sourceOriginalRealGramCellMass434 S mu h j:ℂ)⁻¹ *
        ∑ c : sourceOriginalPrimitiveFamily434 Q,
          star (c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
             ZMod (c.val.1.val+1))) *
          ∑ q : SourceOriginalGramPrimeTuple434 S,
            (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
              (if sourceOriginalLiteralLogCell434 h j
                    (sourceOriginalGramPrimeProduct434 S q)
               then c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
                    ZMod (c.val.1.val+1)) * f q
               else 0)
      else 0) := by
  classical
  let gate : SourceOriginalGramPrimeTuple434 S → Prop :=
    fun q => sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S q)
  let w : SourceOriginalGramPrimeTuple434 S → ℝ :=
    sourceOriginalGramPrimeMass434 S mu
  let chi : SourceOriginalGramPrimeTuple434 S →
      sourceOriginalPrimitiveFamily434 Q → ℂ :=
    fun q c => c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
      ZMod (c.val.1.val+1))
  let nu : ℝ := sourceOriginalRealGramCellMass434 S mu h j
  have hKernel (q : SourceOriginalGramPrimeTuple434 S) :
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S p)
        (sourceOriginalGramPrimeProduct434 S q) =
      (if gate p ∧ gate q then (nu:ℂ)⁻¹ *
          ∑ c : sourceOriginalPrimitiveFamily434 Q,
            star (chi p c) * chi q c
        else 0) := by
    simpa only [gate, chi, nu] using
      (source_original_physical_primitive_cell_frame_kernel434
        S mu h j Q p q)
  calc
    _ = (∑ q : SourceOriginalGramPrimeTuple434 S,
        (w q:ℂ) *
          (if gate p ∧ gate q then (nu:ℂ)⁻¹ *
            ∑ c : sourceOriginalPrimitiveFamily434 Q,
              star (chi p c) * chi q c
          else 0) * f q) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hKernel q]
    _ = _ := by
      simpa only [gate, chi, w, nu] using
        (source_original_finite_conditioned_frame_operator434
          w chi gate nu f p)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalSignedMinorModes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT SOURCE03 signed primitive comparison MINOR
multiplier, on the GENUINE original A/B prime-tuple
physical spaces with their independent harmonic masses,
splits into its original finite A-cell/A-character and
B-cell/B-character modes. The integer oscillating kernel
H(n,m) is ARBITRARY (it can be the true C6 phase),
and fA/fB are arbitrary fully mark-dependent tests.
The original product-window restrictions, primitive
conductor level, true output products XA/XB, and the
sign -(-1)^r are all retained. This is an algebraic
identity, NOT an assumed minor-arc saving. -/
theorem source_original_physical_signed_minor_Knu_mode_expansion434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (WA WB : Finset ℕ)
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (massA massB : ℤ → ℝ)
    (XA XB r : ℕ) (H : ℕ → ℕ → ℂ) :
    let chars := sourceOriginalActualPrimitiveCharacters434 Q
    let IA := JA.product chars
    let IB := JB.product chars
    let a : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → ℂ := fun jc =>
      sourceOriginalPrimitiveOutputCellCoefficient434
        Q hA massA jc.1 jc.2 XA
    let b : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → ℂ := fun jc =>
      sourceOriginalPrimitiveOutputCellCoefficient434
        Q hB massB jc.1 jc.2 XB
    let mA : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun jc x => sourceOriginalPrimitiveInputCellMode434
        Q hA jc.1 jc.2 (sourceOriginalGramPrimeProduct434 SA x)
    let mB : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun jc y => sourceOriginalPrimitiveInputCellMode434
        Q hB jc.1 jc.2 (sourceOriginalGramPrimeProduct434 SB y)
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun x => (sourceOriginalGramPrimeMass434 SA muA x:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun y => (sourceOriginalGramPrimeMass434 SB muB y:ℂ)
    let fAW : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun x => if sourceOriginalGramPrimeProduct434 SA x ∈ WA
        then fA x else 0
    let fBW : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun y => if sourceOriginalGramPrimeProduct434 SB y ∈ WB
        then fB y else 0
    let phase :
        SourceOriginalGramPrimeTuple434 SA ×
        SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun q => H (sourceOriginalGramPrimeProduct434 SA q.1)
                 (sourceOriginalGramPrimeProduct434 SB q.2)
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB fAW fBW
      (fun q => sourceOriginalActualPrimitiveComparisonKernel434
         Q JA JB hA hB massA massB
         (sourceOriginalGramPrimeProduct434 SA q.1) XA
         (sourceOriginalGramPrimeProduct434 SB q.2) XB r *
          phase q) =
    ∑ i ∈ IA, ∑ j ∈ IB,
      (-((-1:ℂ)^r) * a i*b j) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB
        (fun x => fAW x*mA i x)
        (fun y => fBW y*mB j y)
        phase := by
  classical
  let chars := sourceOriginalActualPrimitiveCharacters434 Q
  let IA := JA.product chars
  let IB := JB.product chars
  let a : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun jc => sourceOriginalPrimitiveOutputCellCoefficient434
      Q hA massA jc.1 jc.2 XA
  let b : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun jc => sourceOriginalPrimitiveOutputCellCoefficient434
      Q hB massB jc.1 jc.2 XB
  let mA : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun jc x => sourceOriginalPrimitiveInputCellMode434
      Q hA jc.1 jc.2 (sourceOriginalGramPrimeProduct434 SA x)
  let mB : (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun jc y => sourceOriginalPrimitiveInputCellMode434
      Q hB jc.1 jc.2 (sourceOriginalGramPrimeProduct434 SB y)
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun x => (sourceOriginalGramPrimeMass434 SA muA x:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun y => (sourceOriginalGramPrimeMass434 SB muB y:ℂ)
  let fAW : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun x => if sourceOriginalGramPrimeProduct434 SA x ∈ WA
      then fA x else 0
  let fBW : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun y => if sourceOriginalGramPrimeProduct434 SB y ∈ WB
      then fB y else 0
  let phase :
      SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun q => H (sourceOriginalGramPrimeProduct434 SA q.1)
               (sourceOriginalGramPrimeProduct434 SB q.2)
  let sig : ℂ := -((-1:ℂ)^r)
  have hKernel (q : SourceOriginalGramPrimeTuple434 SA ×
                   SourceOriginalGramPrimeTuple434 SB) :
      sourceOriginalActualPrimitiveComparisonKernel434
         Q JA JB hA hB massA massB
         (sourceOriginalGramPrimeProduct434 SA q.1) XA
         (sourceOriginalGramPrimeProduct434 SB q.2) XB r =
        sig *
        (∑ i ∈ IA, a i*mA i q.1) *
        (∑ j ∈ IB, b j*mB j q.2) := by
    exact source_original_original_signed_Knu_separated_modes434
      Q JA JB hA hB massA massB
      (sourceOriginalGramPrimeProduct434 SA q.1) XA
      (sourceOriginalGramPrimeProduct434 SB q.2) XB r
  have hFub :=
    source_original_finite_two_sided_minor_mode_fubini434
      IA IB a b mA mB wA wB fAW fBW phase
  change
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB fAW fBW
      (fun q => sourceOriginalActualPrimitiveComparisonKernel434
         Q JA JB hA hB massA massB
         (sourceOriginalGramPrimeProduct434 SA q.1) XA
         (sourceOriginalGramPrimeProduct434 SB q.2) XB r *
         phase q) =
    ∑ i ∈ IA, ∑ j ∈ IB,
      (sig*a i*b j) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB (fun x => fAW x*mA i x)
        (fun y => fBW y*mB j y) phase
  calc
    _ = sig * sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun x => fAW x*(∑ i ∈ IA, a i*mA i x))
      (fun y => fBW y*(∑ j ∈ IB, b j*mB j y))
      phase := by
      unfold sourceOriginalFiniteTwoSidedMinorBilinear434
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only
      rw [hKernel q]
      ring
    _ = sig * (∑ i ∈ IA, ∑ j ∈ IB,
      (a i*b j) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB (fun x => fAW x*mA i x)
        (fun y => fBW y*mB j y) phase) := by
      rw [hFub]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalFrameL1 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- On the ACTUAL source03 independent source/target two-GLOBAL
prime-label laws, the whole original primitive-character
pair kernel has weighted L¹ mass at most the SQUARE of the
true primitive family cardinal. Critically NO factor xi⁻¹
appears, since both real retained-cell probabilities cancel
inside their own harmonic integrations. This estimate is
needed to compare a slowly varying irrational/Mellin
multiplier, which depends jointly on both prime products. -/
theorem source_original_actual_two_global_primitive_L1_434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i p, p ∈ SA i → 0 ≤ muA i p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i p, p ∈ SB i → 0 ≤ muB i p)
    (Q : ℕ) (hA hB : ℝ) (jA jB : ℤ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
    (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
    (pA : SourceOriginalGramPrimeTuple434 SA)
    (pB : SourceOriginalGramPrimeTuple434 SB)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalGramPrimeProduct434 SA pA))
    (hCellB : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalGramPrimeProduct434 SB pB)) :
    (∑ q : SourceOriginalGramPrimeTuple434 SA ×
               SourceOriginalGramPrimeTuple434 SB,
      (sourceOriginalGramPrimeMass434 SA muA q.1 *
       sourceOriginalGramPrimeMass434 SB muB q.2) *
       ‖(sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalGramPrimeProduct434 SA pA)) *
         (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalGramPrimeProduct434 SB pB))‖) ≤
    (Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2 := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalGramPrimeProduct434 SA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalGramPrimeProduct434 SB p)
  have hwA (q : XA) : 0 ≤ wA q :=
    source_original_physical_gram_prime_mass_nonneg434
      SA muA hmuA q
  have hwB (q : XB) : 0 ≤ wB q :=
    source_original_physical_gram_prime_mass_nonneg434
      SB muB hmuB q
  have hL1A : (∑ q : XA, wA q*‖KA q pA‖) ≤
    (Fintype.card Fam:ℝ) :=
    source_original_actual_primitive_global_conditional_L1_434
      SA muA hmuA Q hA jA xi hxi hMassA pA hCellA
  have hL1B : (∑ q : XB, wB q*‖KB q pB‖) ≤
    (Fintype.card Fam:ℝ) :=
    source_original_actual_primitive_global_conditional_L1_434
      SB muB hmuB Q hB jB xi hxi hMassB pB hCellB
  have hMain := source_original_finite_two_global_frame_L1_bound434
    wA wB hwA hwB KA KB
    (Fintype.card Fam:ℝ) (Fintype.card Fam:ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    pA pB hL1A hL1B
  simpa only [XA,XB,Fam,wA,wB,KA,KB,pow_two] using hMain
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalKnu -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The finite literal physical prime-tuple, character, and
global-cell synthesis kernel. The real probability of each GLOBAL
cell is used without replacing it by a synthetic normalizer. -/
noncomputable def sourceOriginalPhysicalPrimitiveFrameKernel434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (active : Finset ℤ) (Q : ℕ)
    (p q : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  ∑ j ∈ active,
    if sourceOriginalLiteralLogCell434 h j
         (sourceOriginalGramPrimeProduct434 S p) ∧
       sourceOriginalLiteralLogCell434 h j
         (sourceOriginalGramPrimeProduct434 S q)
    then (sourceOriginalRealGramCellMass434 S mu h j:ℂ)⁻¹ *
      ∑ c : sourceOriginalPrimitiveFamily434 Q,
        star (c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
          ZMod (c.val.1.val+1))) *
        c.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
          ZMod (c.val.1.val+1))
    else 0

/-- SOURCE03 true signed two-GLOBAL comparison Knu, evaluated on
the physical labelled prime tuples, is EXACTLY the product of
the two original conditional character-frame kernels with the
same literal inclusion-exclusion sign, two active cell families,
and both true harmonic probability laws. No approximations. -/
theorem source_original_physical_two_global_Knu_identity434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (JA JB : Finset ℤ) (Q r : ℕ)
    (pA qA : SourceOriginalGramPrimeTuple434 SA)
    (pB qB : SourceOriginalGramPrimeTuple434 SB) :
    sourceOriginalActualPrimitiveComparisonKernel434 Q JA JB hA hB
      (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SA pA)
      (sourceOriginalGramPrimeProduct434 SA qA)
      (sourceOriginalGramPrimeProduct434 SB pB)
      (sourceOriginalGramPrimeProduct434 SB qB) r =
    -((-1:ℂ)^r) *
      sourceOriginalPhysicalPrimitiveFrameKernel434
        SA muA hA JA Q pA qA *
      sourceOriginalPhysicalPrimitiveFrameKernel434
        SB muB hB JB Q pB qB := by
  unfold sourceOriginalActualPrimitiveComparisonKernel434
  have hFrameA := source_original_physical_active_primitive_frame_kernel434
    SA muA hA JA Q pA qA
  have hFrameB := source_original_physical_active_primitive_frame_kernel434
    SB muB hB JB Q pB qB
  rw [hFrameA, hFrameB]
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalAction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact Fubini for a coupled input to two genuine physical
character-frame kernels. Nothing requires a product test
f(x,y)=fA(x)*fB(y); a signed scalar is carried unchanged. -/
theorem source_original_finite_two_global_signed_operator_fubini434
    {X Y : Type} [Fintype X] [Fintype Y]
    (muX : X → ℝ) (muY : Y → ℝ)
    (KA : X → X → ℂ) (KB : Y → Y → ℂ)
    (pX : X) (pY : Y) (alpha : ℂ)
    (f : X × Y → ℂ) :
    (∑ q : X × Y,
      (muX q.1:ℂ)*(muY q.2:ℂ) *
        (alpha * KA pX q.1 * KB pY q.2) * f q) =
      alpha * ∑ qX : X,
        (muX qX:ℂ)*KA pX qX *
          ∑ qY : Y, (muY qY:ℂ)*KB pY qY*f (qX,qY) := by
  classical
  calc
    _ = ∑ qX : X, ∑ qY : Y,
      (muX qX:ℂ)*(muY qY:ℂ) *
        (alpha * KA pX qX * KB pY qY) * f (qX,qY) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ qX : X, alpha *
      ((muX qX:ℂ)*KA pX qX *
        ∑ qY : Y, (muY qY:ℂ)*KB pY qY*f (qX,qY)) := by
      apply Finset.sum_congr rfl
      intro qX hx
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro qY hy
      ring
    _ = _ := by rw [Finset.mul_sum]
/-- FULL original SOURCE03 two-GLOBAL signed primitive comparison
operator on independently labelled physical BIG prime tuple spaces
is the sequential composition of the two ORIGINAL character-frame
kernels for an ARBITRARY coupled complex source test f.
It carries the exact -(-1)^r sign, the true physical harmonic
probabilities in both blocks, moving GLOBAL active cell sets,
and each primitive character's original conductor.
This is an OPERATOR identity, but it does not identify the
raw-plus-pattern residual with a Hoeffding survivor. -/
theorem source_original_actual_physical_two_global_operator_exact434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (JA JB : Finset ℤ) (Q r : ℕ)
    (pA : SourceOriginalGramPrimeTuple434 SA)
    (pB : SourceOriginalGramPrimeTuple434 SB)
    (f : SourceOriginalGramPrimeTuple434 SA ×
         SourceOriginalGramPrimeTuple434 SB → ℂ) :
    (∑ q : SourceOriginalGramPrimeTuple434 SA ×
        SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
        (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
      sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB
        (sourceOriginalRealGramCellMass434 SA muA hA)
        (sourceOriginalRealGramCellMass434 SB muB hB)
        (sourceOriginalGramPrimeProduct434 SA pA)
        (sourceOriginalGramPrimeProduct434 SA q.1)
        (sourceOriginalGramPrimeProduct434 SB pB)
        (sourceOriginalGramPrimeProduct434 SB q.2) r * f q) =
    -((-1:ℂ)^r) *
      ∑ qA : SourceOriginalGramPrimeTuple434 SA,
        (sourceOriginalGramPrimeMass434 SA muA qA:ℂ) *
        sourceOriginalPhysicalPrimitiveFrameKernel434
          SA muA hA JA Q pA qA *
        ∑ qB : SourceOriginalGramPrimeTuple434 SB,
          (sourceOriginalGramPrimeMass434 SB muB qB:ℂ) *
          sourceOriginalPhysicalPrimitiveFrameKernel434
            SB muB hB JB Q pB qB * f (qA,qB) := by
  let KA := sourceOriginalPhysicalPrimitiveFrameKernel434
    SA muA hA JA Q
  let KB := sourceOriginalPhysicalPrimitiveFrameKernel434
    SB muB hB JB Q
  let wA := sourceOriginalGramPrimeMass434 SA muA
  let wB := sourceOriginalGramPrimeMass434 SB muB
  let alpha : ℂ := -((-1:ℂ)^r)
  have hkernel
      (qA : SourceOriginalGramPrimeTuple434 SA)
      (qB : SourceOriginalGramPrimeTuple434 SB) :
      sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB
        (sourceOriginalRealGramCellMass434 SA muA hA)
        (sourceOriginalRealGramCellMass434 SB muB hB)
        (sourceOriginalGramPrimeProduct434 SA pA)
        (sourceOriginalGramPrimeProduct434 SA qA)
        (sourceOriginalGramPrimeProduct434 SB pB)
        (sourceOriginalGramPrimeProduct434 SB qB) r =
        alpha * KA pA qA * KB pB qB := by
    exact source_original_physical_two_global_Knu_identity434
      SA muA SB muB hA hB JA JB Q r pA qA pB qB
  calc
    _ = ∑ q : SourceOriginalGramPrimeTuple434 SA ×
         SourceOriginalGramPrimeTuple434 SB,
       (wA q.1:ℂ)*(wB q.2:ℂ) *
         (alpha * KA pA q.1 * KB pB q.2) * f q := by
         apply Finset.sum_congr rfl
         intro q hq
         rw [hkernel q.1 q.2]
    _ = alpha * ∑ qA : SourceOriginalGramPrimeTuple434 SA,
         (wA qA:ℂ) * KA pA qA *
         ∑ qB : SourceOriginalGramPrimeTuple434 SB,
           (wB qB:ℂ) * KB pB qB * f (qA,qB) :=
      source_original_finite_two_global_signed_operator_fubini434
        wA wB KA KB pA pB alpha f
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalWindowModeBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- EXACT equivalence of the TRUE source03 finite
two-physical-block window bilinear sum and the product
type expression used in the original Knu primitive-mode
decomposition C280. The phase H(n,m) is arbitrary.
The input fA,fB may depend on the full labelled
prime tuples. This removes the last algebraic Fubini
mismatch before inserting the quantitative C6 bound. -/
theorem source_original_physical_window_mode_bilinear_bridge434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wA : X → ℂ) (wB : Y → ℂ)
    (pA : X → ℕ) (pB : Y → ℕ)
    (fA : X → ℂ) (fB : Y → ℂ)
    (WA WB : Finset ℕ) (H : ℕ → ℕ → ℂ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun x => if pA x ∈ WA then fA x else 0)
      (fun y => if pB y ∈ WB then fB y else 0)
      (fun q => H (pA q.1) (pB q.2)) =
    ∑ x : X,
      if pA x ∈ WA then
        wA x*fA x*
          (∑ y : Y,
             if pB y ∈ WB then
               wB y*fB y*H (pA x) (pB y)
             else 0)
      else 0 := by
  classical
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hax : pA x ∈ WA
  · simp only [if_pos hax]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hby : pB y ∈ WB
    · simp only [if_pos hby]
      ring
    · simp [hby]
  · simp [hax]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalMaskedMinorModes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- EXACT original source03 physical integer-window nested
bilinear sum for ANY BOUNDED endpoint mark tests multiplied
by genuine primitive character/cell input modes. This is
the algebraic bridge from the separated-Knu coefficient
identity C280 to the authentic ν-indexed C6 physical
minor theorem C281: a dyad window cuts the endpoint
test only, without replacing either prime law or
assuming tests depend on product integers. -/
theorem source_original_physical_masked_mode_minor_fubini434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wA : X → ℂ) (wB : Y → ℂ)
    (pa : X → ℕ) (pb : Y → ℕ)
    (baseA modeA : X → ℂ) (baseB modeB : Y → ℂ)
    (WA WB : Finset ℕ) (H : ℕ → ℕ → ℂ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun x => (if pa x ∈ WA then baseA x else 0)*modeA x)
      (fun y => (if pb y ∈ WB then baseB y else 0)*modeB y)
      (fun q => H (pa q.1) (pb q.2)) =
    ∑ x : X, if pa x ∈ WA then
      wA x*(baseA x*modeA x)*
        (∑ y : Y, if pb y ∈ WB then
           wB y*(baseB y*modeB y)*H (pa x) (pb y)
          else 0)
      else 0 := by
  classical
  have hBase := source_original_physical_window_mode_bilinear_bridge434
    wA wB pa pb
    (fun x => baseA x*modeA x)
    (fun y => baseB y*modeB y)
    WA WB H
  calc
    _ = sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB
        (fun x => if pa x ∈ WA then baseA x*modeA x else 0)
        (fun y => if pb y ∈ WB then baseB y*modeB y else 0)
        (fun q => H (pa q.1) (pb q.2)) := by
      unfold sourceOriginalFiniteTwoSidedMinorBilinear434
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hx : pa q.1 ∈ WA
      · by_cases hy : pb q.2 ∈ WB
        · simp [hx,hy]
        · simp [hx,hy]
      · simp [hx]
    _ = _ := hBase
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalGramEmbedding -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Embed the ORIGINAL independently labelled auxiliary A probes
of a specific true comparison pattern into the source03 physical
Gram prime-tuple type. The value and prime support are unchanged. -/
noncomputable def sourceOriginalProbeAuxAIntoGram434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z) :
    SourceOriginalGramPrimeTuple434 (fun z : ν.1 => P z.val.1) :=
  fun z => ⟨a (Sum.inl z), by
    simpa [sourceOriginalProbeAuxPrimeSets434] using ha (Sum.inl z)⟩

noncomputable def sourceOriginalProbeAuxBIntoGram434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z) :
    SourceOriginalGramPrimeTuple434 (fun z : ν.2 => P z.val.1) :=
  fun z => ⟨a (Sum.inr z), by
    simpa [sourceOriginalProbeAuxPrimeSets434] using ha (Sum.inr z)⟩
/-- Original auxiliary comparison D_A and D_B are DEFINITIONALLY
the products of the physical labelled prime tuples above.
No replacement primes and no loss of repeated numerical values. -/
theorem source_original_probe_aux_A_gram_product434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z) :
    sourceOriginalGramPrimeProduct434
      (fun z : ν.1 => P z.val.1)
      (sourceOriginalProbeAuxAIntoGram434 m ν P a ha) =
        sourceOriginalProbeDA434 m ν a := by
  rfl

theorem source_original_probe_aux_B_gram_product434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z) :
    sourceOriginalGramPrimeProduct434
      (fun z : ν.2 => P z.val.1)
      (sourceOriginalProbeAuxBIntoGram434 m ν P a ha) =
        sourceOriginalProbeDB434 m ν a := by
  rfl
/-- Target free physical marks for pattern ν's first probe
block, exactly at the original J+ell slot indices. -/
noncomputable def sourceOriginalProbeTargetAIntoGram434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (ht : ∀ g i, target g i ∈ P g) :
    SourceOriginalGramPrimeTuple434 (fun z : ν.1 => P z.val.1) :=
  fun z =>
    ⟨target z.val.1
      (sourceOriginalProbeFreeIndex434 J ell m hmJ ν
        z.val.1 z.val.2 (Or.inl z.property)),
     ht _ _⟩

/-- Source free physical marks for pattern ν's second probe
block, with exactly the original positions and source law. -/
noncomputable def sourceOriginalProbeSourceBIntoGram434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (source : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hs : ∀ g i, source g i ∈ P g) :
    SourceOriginalGramPrimeTuple434 (fun z : ν.2 => P z.val.1) :=
  fun z =>
    ⟨source z.val.1
      (sourceOriginalProbeFreeIndex434 J ell m hmJ ν
        z.val.1 z.val.2 (Or.inr z.property)),
     hs _ _⟩
theorem source_original_probe_target_A_gram_product434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (ht : ∀ g i, target g i ∈ P g) :
    sourceOriginalGramPrimeProduct434
      (fun z : ν.1 => P z.val.1)
      (sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht) =
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target := by
  rfl

theorem source_original_probe_source_B_gram_product434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (source : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hs : ∀ g i, source g i ∈ P g) :
    sourceOriginalGramPrimeProduct434
      (fun z : ν.2 => P z.val.1)
      (sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs) =
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source := by
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualBigUnconditionalFrame -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The original moving source03 GLOBAL product-log cell has a
genuine unconditional ℓ² near-frame with any prescribed power
of L, after the ACTUAL dyadic band count has been absorbed.
All character coefficients may depend on physical output tests.
No fictional independence of the moving product cell is used. -/
theorem source_original_actual_big_frame_power_unconditional434
    (Cq : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ) (i : ι)
      (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (V : ℝ) (hV : 0 < V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (a : sourceOriginalPrimitiveFamily434 Q → ℂ),
      (∑ c : sourceOriginalPrimitiveFamily434 Q,
        ‖∑ d : sourceOriginalPrimitiveFamily434 Q,
          sourceOriginalActualPrimitiveGramEntry434
            S mu h j Q c.val d.val * a d‖^2) ≤
        (1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) *
           ((K/V)*L^(-B)))^2 *
        (∑ d : sourceOriginalPrimitiveFamily434 Q, ‖a d‖^2) := by
  obtain ⟨K,Y,hK,hGram⟩ :=
    source_original_actual_big_gram_power_unconditional434
      Cq gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hV hBand hWeight a
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let G : Fam → Fam → ℂ := fun c d =>
    sourceOriginalActualPrimitiveGramEntry434
      S mu h j Q c.val d.val
  let eps : ℝ := (K/V)*L^(-B)
  have hLpos : 0 ≤ L := by linarith
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg (div_nonneg hK hV.le)
      (Real.rpow_nonneg hLpos _)
  have hcell : sourceOriginalRealGramCellMass434 S mu h j ≤ 1 :=
    (source_original_real_gram_cell_probability434
      S mu hmu hmuPos h j).2
  have hdiag (c : Fam) : ‖G c c‖ ≤ 1 := by
    exact (source_original_actual_primitive_gram_norm_le_mass434
      S mu hmuPos h j Q hBIG c.val c.val).trans hcell
  have hoff (c d : Fam) (hne : c ≠ d) : ‖G c d‖ ≤ eps := by
    have hneVal : c.val ≠ d.val := by
      intro heq
      exact hne (Subtype.ext heq)
    have hb := hGram S mu hmu hmuPos h j Q
      c.val d.val c.property d.property hneVal i hBIG
      L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
      V hV hBand hWeight
    simpa only [G,eps] using hb
  have hframe :=
    Green64FullPhysicalE.memory_original_finite_cell_gram_schur
      G eps heps hdiag hoff a
  simpa only [G,eps,Fam] using hframe
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualBigGlobalCells -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The exact source03 original GLOBAL cells form an orthogonal
direct sum of true physical Gram blocks. For all finite active
cell families and arbitrary cell-dependent coefficient tests,
the near-frame loss depends ONLY on character count and the
physical SW saving, not on the number of GLOBAL cells. -/
theorem source_original_actual_big_global_cells_unconditional434
    (Cq : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {J ι : Type} [Fintype J] [DecidableEq J]
      [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (cell : J → ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (V : ℝ) (hV : 0 < V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (a : J → sourceOriginalPrimitiveFamily434 Q → ℂ),
      (∑ t : J,
        ∑ c : sourceOriginalPrimitiveFamily434 Q,
          ‖∑ e : sourceOriginalPrimitiveFamily434 Q,
            sourceOriginalActualPrimitiveGramEntry434
              S mu h (cell t) Q c.val e.val * a t e‖^2) ≤
      (1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)*
         ((K/V)*L^(-B)))^2 *
      (∑ t : J, ∑ e : sourceOriginalPrimitiveFamily434 Q,
         ‖a t e‖^2) := by
  obtain ⟨K,Y,hK,hFrame⟩ :=
    source_original_actual_big_frame_power_unconditional434
      Cq gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro J ι instJ instJD instI instID
    S mu hmu hmuPos h cell Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hV hBand hWeight a
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let R : ℝ :=
    (1+(Fintype.card Fam:ℝ)*((K/V)*L^(-B)))^2
  change (∑ t : J,
      ∑ c : Fam,
        ‖∑ e : Fam,
          sourceOriginalActualPrimitiveGramEntry434
             S mu h (cell t) Q c.val e.val * a t e‖^2) ≤
    R*(∑ t : J, ∑ e : Fam, ‖a t e‖^2)
  calc
    _ ≤ ∑ t : J, R*(∑ e : Fam, ‖a t e‖^2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hFrame S mu hmu hmuPos h (cell t) Q i hBIG
        L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
        V hV hBand hWeight (a t)
    _ = _ := by
      rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeFrameLoss -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact original primitive-character family size Q² is absorbed
into arbitrarily chosen Siegel–Walfisz power: for Q ≤ L^Cq
the entire Gram frame perturbation can save any L^-B.
The physical harmonic V_g normalization is not silently
replaced by 1: an explicit positive lower bound Vmin is kept. -/
theorem source_original_prime_frame_loss_absorb434
    (Q Cq : ℕ) (L B K V Vmin : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hV : Vmin ≤ V) :
    (Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) *
      ((K/V)*L^(-(B+((2*Cq:ℕ):ℝ)))) ≤
    (K/Vmin)*L^(-B) := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := hLpos.le
  have hVpos : 0 < V := hVmin.trans_le hV
  have hcard : (Fintype.card Fam:ℝ) ≤ L^(2*Cq) := by
    calc
      (Fintype.card Fam:ℝ) ≤ (Q:ℝ)^2 := by
        exact_mod_cast source_original_primitive_frame_card_le_square434 Q
      _ ≤ (L^Cq)^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      _ = L^(2*Cq) := by
        rw [← pow_mul]
        congr 1
        omega
  have hratio : K/V ≤ K/Vmin := by
    have hinv : V⁻¹ ≤ Vmin⁻¹ :=
      (inv_le_inv₀ hVpos hVmin).2 hV
    simpa only [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hinv hK)
  have hbase :
      (Fintype.card Fam:ℝ)*(K/V) ≤
        L^(2*Cq)*(K/Vmin) := by
    exact mul_le_mul hcard hratio
      (div_nonneg hK hVpos.le)
      (pow_nonneg hLnonneg _)
  have hdecay : 0 ≤ L^(-(B+((2*Cq:ℕ):ℝ))) :=
    Real.rpow_nonneg hLnonneg _
  have hpow :
      L^(2*Cq)*L^(-(B+((2*Cq:ℕ):ℝ))) = L^(-B) := by
    calc
      _ = L^((2*Cq:ℕ):ℝ)*L^(-(B+((2*Cq:ℕ):ℝ))) := by
        rw [Real.rpow_natCast]
      _ = L^(((2*Cq:ℕ):ℝ)+(-(B+((2*Cq:ℕ):ℝ)))) := by
        rw [Real.rpow_add hLpos]
      _ = L^(-B) := by congr 1; ring
  change (Fintype.card Fam:ℝ) *
    ((K/V)*L^(-(B+((2*Cq:ℕ):ℝ)))) ≤
      (K/Vmin)*L^(-B)
  calc
    _ = ((Fintype.card Fam:ℝ)*(K/V)) *
          L^(-(B+((2*Cq:ℕ):ℝ))) := by ring
    _ ≤ (L^(2*Cq)*(K/Vmin)) *
          L^(-(B+((2*Cq:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_right hbase hdecay
    _ = (K/Vmin) *
          (L^(2*Cq)*L^(-(B+((2*Cq:ℕ):ℝ)))) := by ring
    _ = (K/Vmin)*L^(-B) := by rw [hpow]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMajorSlowFourierLossAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Quantitative SOURCE03 major-arc SLOW PHASE loss from the TRUE
all-conductor primitive-character family. The original frame
has card <= Q^2; two independent GLOBAL characters therefore
cost at most Q^4 <= L^(4*Cq). When the actual Mellin/irrational
oscillation on one retained pair of cells is bounded by the
given sharp parameter scale L^(-(B+4*Cq)), the complete
two-character slow-phase cost is O(L^-B). No SW is applied
to dependent H(p), and the needed smallness conditions on
zeta, beta and the actual GLOBAL width remain explicit. -/
theorem source_original_major_slow_two_char_fourier_loss_absorb434
    (Q Cq : ℕ) (L B ζ beta R hA hB : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hR : 0 ≤ R)
    (hWidth : 0 ≤ hA+hB) (hWidthLe : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^(-(B+((4*Cq:ℕ):ℝ))))
    (hBeta : 2*Real.pi*|beta| *R ≤
      L^(-(B+((4*Cq:ℕ):ℝ)))) :
    ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2) *
      ((|ζ|+2*Real.pi*|beta| *R)*(hA+hB)) ≤
      2*L^(-B) := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let save : ℝ := L^(-(B+((4*Cq:ℕ):ℝ)))
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hCard0 : (Fintype.card Fam:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast source_original_primitive_frame_card_le_square434 Q
  have hCard :
      (Fintype.card Fam:ℝ)^2 ≤ L^((4*Cq:ℕ):ℝ) := by
    calc
      _ ≤ ((Q:ℝ)^2)^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hCard0 2
      _ = (Q:ℝ)^4 := by ring
      _ ≤ (L^Cq)^4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4
      _ = L^((4*Cq:ℕ):ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm 4 Cq]
  have hsave : 0 ≤ save := Real.rpow_nonneg hLnn _
  have hsum : |ζ|+2*Real.pi*|beta| *R ≤ 2*save := by
    dsimp [save]
    linarith
  have hsumNN : 0 ≤ |ζ|+2*Real.pi*|beta| *R := by
    positivity
  have homega :
      (|ζ|+2*Real.pi*|beta| *R)*(hA+hB) ≤ 2*save := by
    calc
      _ ≤ (2*save)*(hA+hB) :=
        mul_le_mul_of_nonneg_right hsum hWidth
      _ ≤ (2*save)*1 :=
        mul_le_mul_of_nonneg_left hWidthLe (by positivity)
      _ = 2*save := by ring
  have homegaNN : 0 ≤
      (|ζ|+2*Real.pi*|beta| *R)*(hA+hB) :=
    mul_nonneg hsumNN hWidth
  have hMul :
      ((Fintype.card Fam:ℝ)^2) *
      ((|ζ|+2*Real.pi*|beta| *R)*(hA+hB)) ≤
      L^((4*Cq:ℕ):ℝ)*(2*save) :=
    mul_le_mul hCard homega homegaNN (Real.rpow_nonneg hLnn _)
  calc
    _ ≤ L^((4*Cq:ℕ):ℝ)*(2*save) := hMul
    _ = 2*(L^((4*Cq:ℕ):ℝ)*
      L^(-(B+((4*Cq:ℕ):ℝ)))) := by dsimp [save]; ring
    _ = 2*L^(-B) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMajorWideMellinLoss -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Uniform Mellin major-arc slow-phase bound for ALL
|zeta|<=L^C4, not just |zeta|<=L^-B. The saving is
created by choosing TRUE source03 log-cell width
hA+hB<=L^(-(B+4*Cq+C4)), rather than assuming the
Mellin/Fourier frequency itself is small. The two
original primitive character families cost Q^4 and
the original beta physical oscillation is still
explicitly required <=L^C4 on the actual Rglobal.
No small zeta hypothesis, no auxiliary fake kernel. -/
theorem source_original_wide_mellin_two_char_loss_absorb434
    (Q Cq C4 : ℕ) (L B ζ beta R hA hB : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hR : 0 ≤ R)
    (hWidthNN : 0 ≤ hA+hB)
    (hWidth : hA+hB ≤ L^(-(B+(((4*Cq+C4:ℕ):ℝ)))))
    (hZeta : |ζ| ≤ L^C4)
    (hBeta : 2*Real.pi*|beta| *R ≤ L^C4) :
    ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2) *
      ((|ζ|+2*Real.pi*|beta| *R)*(hA+hB)) ≤
        2*L^(-B) := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let U : ℝ := L^C4
  let W : ℝ := L^(-(B+(((4*Cq+C4:ℕ):ℝ))))
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hCard0 : (Fintype.card Fam:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast source_original_primitive_frame_card_le_square434 Q
  have hCard :
      (Fintype.card Fam:ℝ)^2 ≤ L^((4*Cq:ℕ):ℝ) := by
    calc
      _ ≤ ((Q:ℝ)^2)^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hCard0 2
      _ = (Q:ℝ)^4 := by ring
      _ ≤ (L^Cq)^4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4
      _ = L^((4*Cq:ℕ):ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm 4 Cq]
  have hU : 0 ≤ U := pow_nonneg hLnn _
  have hW : 0 ≤ W := Real.rpow_nonneg hLnn _
  have hsumNN : 0 ≤ |ζ|+2*Real.pi*|beta| *R := by
    positivity
  have hsum : |ζ|+2*Real.pi*|beta| *R ≤ 2*U := by
    dsimp [U]
    linarith
  have hO : (|ζ|+2*Real.pi*|beta| *R)*(hA+hB) ≤
      2*U*W := by
    calc
      _ ≤ (2*U)*(hA+hB) :=
        mul_le_mul_of_nonneg_right hsum hWidthNN
      _ ≤ (2*U)*W :=
        mul_le_mul_of_nonneg_left hWidth (by positivity)
  have hONN :
      0 ≤ (|ζ|+2*Real.pi*|beta| *R)*(hA+hB) :=
    mul_nonneg hsumNN hWidthNN
  have hPower :
      L^((4*Cq:ℕ):ℝ)*U*W = L^(-B) := by
    dsimp [U,W]
    calc
      _ = L^((4*Cq:ℕ):ℝ)*L^((C4:ℝ))*
            L^(-(B+(((4*Cq+C4:ℕ):ℝ)))) := by
          simp only [Real.rpow_natCast]
      _ = L^(((4*Cq:ℕ):ℝ)+(C4:ℝ))*
            L^(-(B+(((4*Cq+C4:ℕ):ℝ)))) := by
          rw [← Real.rpow_add hLpos]
      _ = L^(((4*Cq:ℕ):ℝ)+(C4:ℝ) +
               (-(B+(((4*Cq+C4:ℕ):ℝ))))) := by
          rw [← Real.rpow_add hLpos]
      _ = L^(-B) := by
        congr 1
        push_cast
        ring
  calc
    _ ≤ L^((4*Cq:ℕ):ℝ)*(2*U*W) :=
      mul_le_mul hCard hO hONN (Real.rpow_nonneg hLnn _)
    _ = 2*(L^((4*Cq:ℕ):ℝ)*U*W) := by ring
    _ = 2*L^(-B) := by rw [hPower]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalNormalizedPrimeLoss -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- True active source03 GLOBAL-cell normalization costs at most xi^-1,
and the entire original primitive family at most Q². Both are
absorbed by the excess exponent Cxi+2*Cq in unconditional SW.
Keep the positive physical harmonic lower normalizer Vmin. -/
theorem source_original_normalized_prime_frame_loss_absorb434
    (Q Cq Cxi : ℕ) (L B K V Vmin xi : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hV : Vmin ≤ V) (hxi : 0 < xi)
    (hXi : xi⁻¹ ≤ L^Cxi) :
    (Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) *
      (((K/V)*L^(-((B+(Cxi:ℝ))+((2*Cq:ℕ):ℝ))))/xi) ≤
       (K/Vmin)*L^(-B) := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let D : ℝ := B+(Cxi:ℝ)
  have hFactor :=
    source_original_prime_frame_loss_absorb434
      Q Cq L D K V Vmin hL hQ hK hVmin hV
  have hVpos : 0 < V := hVmin.trans_le hV
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := hLpos.le
  have hRpos : 0 ≤ (K/Vmin)*L^(-(B+(Cxi:ℝ))) :=
    mul_nonneg (div_nonneg hK hVmin.le)
      (Real.rpow_nonneg hLnonneg _)
  have hInv : 0 ≤ xi⁻¹ := (inv_pos.mpr hxi).le
  have hXi' : xi⁻¹ ≤ L^(Cxi:ℝ) := by
    simpa only [Real.rpow_natCast] using hXi
  change (Fintype.card Fam:ℝ) *
    (((K/V)*L^(-(D+((2*Cq:ℕ):ℝ))))/xi) ≤ _
  calc
    _ = ((Fintype.card Fam:ℝ) *
      ((K/V)*L^(-(D+((2*Cq:ℕ):ℝ))))) * xi⁻¹ := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ ((K/Vmin)*L^(-D)) * xi⁻¹ :=
      mul_le_mul_of_nonneg_right hFactor hInv
    _ ≤ ((K/Vmin)*L^(-D)) * L^(Cxi:ℝ) :=
      mul_le_mul_of_nonneg_left hXi' (by simpa only [D] using hRpos)
    _ = (K/Vmin)*L^(-B) := by
      rw [mul_assoc, ← Real.rpow_add hLpos]
      congr 1
      dsimp [D]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUniformMellinMesh -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- An EXPLICIT uniform-Mellin SOURCE03 GLOBAL log-mesh:
hA=hB=(1/2)*L^(-(B+4*Cq+C4)). For L>=1 both cell widths
are positive; the total width is exactly the saving demanded
by C177 for ALL |zeta|<=L^C4; and reciprocal width is
2*L^(B+4*Cq+C4), a fixed polynomial in L. Therefore
the discarded-cell count increases only by this polynomial,
which can be counteracted with a suitably small xi. -/
theorem source_original_uniform_mellin_mesh_identity434
    (Cq C4 : ℕ) (L B : ℝ)
    (hL : 1 ≤ L) :
    let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    0 < h ∧ h+h = L^(-E) ∧ h⁻¹ = 2*L^E := by
  let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  have hLpos : 0 < L := by linarith
  have hPow : 0 < L^(-E) := Real.rpow_pos_of_pos hLpos _
  have hmesh : 0 < h := by dsimp [h]; positivity
  have hSum : h+h = L^(-E) := by dsimp [h]; ring
  have hInverse : (L^(-E))⁻¹ = L^E := by
    rw [Real.rpow_neg hLpos.le]
    exact inv_inv _
  have hInverseMesh : h⁻¹ = 2*L^E := by
    calc
      h⁻¹ = (L^(-E)/2)⁻¹ := rfl
      _ = 2*(L^(-E))⁻¹ := by rw [inv_div]; ring
      _ = 2*L^E := by rw [hInverse]
  exact ⟨hmesh,hSum,hInverseMesh⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUniformMellinDiscardBudget -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- EXPLICIT compatible physical GLOBAL mesh + cell-retention
threshold for the original SOURCE03 ν pattern. Let
E=B+4*Cq+C4, hA=hB=L^-E/2, and choose
xi=L^(-(2B+d+E))/(16*(M+1)).
For ANY true selected probe cardinalities nA,nB with
nA+nB <= M, the exact ORIGINAL dropped-cell coefficient
2*(nA*L^d/hA+nB*L^d/hB+4)*xi is <=L^-2B.
Thus an arbitrarily broad Mellin window |zeta|<=L^C4
can coexist with an arbitrarily small dropped-cell
L² contribution by choosing sufficiently small xi.
Only original BIG upper scale and an explicit fixed
probe-count cap are needed; the separate compatibility
xi^-1<=L^Cxi is NOT silently assumed and must be proved
from a sufficiently large L and an appropriate Cxi. -/
theorem source_original_uniform_mellin_discarded_cell_budget434
    (Cq C4 nA nB : ℕ) (L B d M : ℝ)
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hM : 0 ≤ M)
    (hCount : ((nA+nB:ℕ):ℝ) ≤ M) :
    let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    let xi : ℝ := L^(-(2*B+d+E))/(16*(M+1))
    0 < h ∧ 0 < xi ∧ h+h = L^(-E) ∧
      2*((nA:ℝ)*L^d/h+(nB:ℝ)*L^d/h+4)*xi ≤
      L^(-(2*B)) := by
  let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  let W : ℝ := L^(-(2*B+d+E))
  let T : ℝ := L^(-(2*B))
  let den : ℝ := 16*(M+1)
  let xi : ℝ := W/den
  have hLpos : 0 < L := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hden : 0 < den := by dsimp [den]; linarith
  have hW : 0 < W := Real.rpow_pos_of_pos hLpos _
  have hT : 0 < T := Real.rpow_pos_of_pos hLpos _
  have hxi : 0 < xi := div_pos hW hden
  obtain ⟨hh,hwidth,hInv⟩ :=
    source_original_uniform_mellin_mesh_identity434 Cq C4 L B hL
  have hWidth : h+h = L^(-E) := hwidth
  have hinv : h⁻¹ = 2*L^E := hInv
  have hPower : L^d*L^E*W = T := by
    dsimp [W,T]
    calc
      _ = L^(d+E+(-(2*B+d+E))) := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      _ = L^(-(2*B)) := by
        congr 1
        ring
  have hWLeT : W ≤ T := by
    dsimp [W,T]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  let n : ℝ := ((nA+nB:ℕ):ℝ)
  have hN : (nA:ℝ)+(nB:ℝ) = n := by
    dsimp [n]
    push_cast
    ring
  have hBoundNumerator :
      4*n*T+8*W ≤ den*T := by
    have hNBound : n*T ≤ M*T :=
      mul_le_mul_of_nonneg_right hCount hT.le
    have hLow : 4*n*T+8*W ≤ (4*M+8)*T := by
      nlinarith [hNBound,hWLeT]
    have hHigh : (4*M+8)*T ≤ den*T := by
      dsimp [den]
      nlinarith [mul_nonneg hM hT.le, hT.le]
    exact hLow.trans hHigh
  have hExpr :
      2*((nA:ℝ)*L^d/h+(nB:ℝ)*L^d/h+4)*xi =
        (4*n*T+8*W)/den := by
    calc
      _ = (4*((nA:ℝ)+(nB:ℝ))*(L^d*L^E*W)+8*W)/den := by
        dsimp [xi]
        simp only [div_eq_mul_inv,hinv]
        ring
      _ = (4*n*T+8*W)/den := by rw [hPower,hN]
  have hBound :
      (4*n*T+8*W)/den ≤ T := by
    apply (div_le_iff₀ hden).2
    convert hBoundNumerator using 1 <;> ring
  exact ⟨hh,hxi,hWidth,hExpr.trans_le hBound⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUniformMellinRetentionCap -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The EXPLICIT threshold xi from C181 is also compatible
with the quantitative SOURCE03 Siegel–Walfisz retention
hypothesis xi^-1 <= L^Cxi, for any sufficiently large L
relative to the fixed number M of selected probe slots.
It suffices to choose Cxi >= 2B+d+B+4*Cq+C4+1.
No hidden small-mass hypothesis is needed for such a
choice, and dependence of the large-x threshold on fixed
probe cardinalities is allowed by the original construction. -/
theorem source_original_uniform_mellin_retention_inverse_cap434
    (Cq C4 Cxi : ℕ) (L B d M : ℝ)
    (hL : 16*(M+1) ≤ L)
    (hM : 0 ≤ M)
    (hExponent :
       2*B+d+(B+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (Cxi:ℝ)) :
    let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
    let xi : ℝ := L^(-(2*B+d+E))/(16*(M+1))
    0 < xi ∧ xi⁻¹ ≤ L^Cxi := by
  let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
  let A : ℝ := 2*B+d+E
  let den : ℝ := 16*(M+1)
  let xi : ℝ := L^(-A)/den
  have hDen : 0 < den := by dsimp [den]; linarith
  have hLp : 0 < L := lt_of_lt_of_le hDen hL
  have hLone : 1 ≤ L := by linarith
  have hXi : 0 < xi :=
    div_pos (Real.rpow_pos_of_pos hLp _) hDen
  have hInv : xi⁻¹ = den*L^A := by
    dsimp [xi]
    calc
      _ = den*(L^(-A))⁻¹ := by rw [inv_div]; ring
      _ = den*L^A := by
        rw [Real.rpow_neg hLp.le, inv_inv]
  have hAplus : A+1 ≤ (Cxi:ℝ) := hExponent
  have hLarge : den ≤ L := hL
  have hPowNN : 0 ≤ L^A := Real.rpow_nonneg hLp.le _
  have hUpper :
      den*L^A ≤ L^(A+1) := by
    calc
      _ ≤ L*L^A := mul_le_mul_of_nonneg_right hLarge hPowNN
      _ = L^(A+1) := by
        conv_rhs => rw [Real.rpow_add hLp]
        simp only [Real.rpow_one, pow_one]
        ring
  have hUpper' : L^(A+1) ≤ L^Cxi := by
    convert (Real.rpow_le_rpow_of_exponent_le hLone hAplus) using 1
    rw [Real.rpow_natCast]
  exact ⟨hXi, by rw [hInv]; exact hUpper.trans hUpper'⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUniformMellinFullParameterSchedule -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- ONE explicit SOURCE03 original parameter schedule discharges
BOTH the true all-retained Mellin width condition and the
physical dropped-cell L² budget, and the genuine lower
retention-mass hypothesis xi^-1 <= L^Cxi.
No extra 'there exists tiny xi' or 'width can be chosen'
assumption. An arbitrary fixed ν-pattern with at most
M actually selected prime labels uses exactly this schedule.
Still requires a genuine selected BIG interval and the
irrational-beta major-arc condition from C179. -/
theorem source_original_uniform_mellin_full_parameter_schedule434
    (Cq C4 Cxi nA nB : ℕ) (L B d M : ℝ)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hL : 16*(M+1) ≤ L)
    (hCount : ((nA+nB:ℕ):ℝ) ≤ M)
    (hExponent :
      2*B+d+(B+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (Cxi:ℝ)) :
    let E : ℝ := B+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    let xi : ℝ := L^(-(2*B+d+E))/(16*(M+1))
    0 < h ∧ 0 < xi ∧
      h+h ≤ L^(-E) ∧ xi⁻¹ ≤ L^Cxi ∧
      2*((nA:ℝ)*L^d/h+(nB:ℝ)*L^d/h+4)*xi ≤
        L^(-(2*B)) := by
  have hLone : 1 ≤ L := by nlinarith
  obtain ⟨hh,hxi,hwidth,hDrop⟩ :=
    source_original_uniform_mellin_discarded_cell_budget434
      Cq C4 nA nB L B d M hLone hB hd hM hCount
  obtain ⟨hxi',hInverse⟩ :=
    source_original_uniform_mellin_retention_inverse_cap434
      Cq C4 Cxi L B d M hL hM hExponent
  exact ⟨hh,hxi,le_of_eq hwidth,hInverse,hDrop⟩
end Green64Analytic.CorrelationSquare

end

