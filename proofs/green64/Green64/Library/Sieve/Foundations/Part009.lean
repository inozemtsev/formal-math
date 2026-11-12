module

public import Green64.Library.Weights.Part117
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part105
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Weights.Part106

@[expose] public section

/-!
# Sieve / Foundations / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalQSelectedSkipPiSplit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- The genuine original Q primes selected by the exact B590 Boolean
allocation δ, with the ORIGINAL dependent source Q membership at each
original ordered slot. No repeated prime restriction is imposed. -/
abbrev paritySourceQSelected434
    (n : ℕ) (Q : Fin n → Finset ℕ) (δ : Fin n → Bool) : Type :=
  (i : {i : Fin n // δ i = true}) → {q : ℕ // q ∈ Q i.val}

/-- A FULL labelled original source Q tuple is EXACTLY a selected-prime
tuple and an ORIGINAL B509 `OrderedQSkip` tuple, given δ. This is a
bijection, with neither factorial nor physical weight changes. -/
noncomputable def paritySourceQAllSelectedSkipEquiv434
    {n : ℕ} (Q : Fin n → Finset ℕ) (δ : Fin n → Bool) :
    ((i : Fin n) → {q : ℕ // q ∈ Q i}) ≃
      (paritySourceQSelected434 n Q δ × OrderedQSkip n Q δ) where
  toFun p := (fun i => p i.val, fun i => p i.val)
  invFun x i := if h : δ i = true then x.1 ⟨i,h⟩ else x.2 ⟨i,h⟩
  left_inv p := by
    funext i
    by_cases h : δ i = true
    · simp [h]
    · simp [h]
  right_inv x := by
    rcases x with ⟨a,b⟩
    apply Prod.ext
    · funext i
      have hi := i.property
      simp [hi]
    · funext i
      have hi := i.property
      simp [hi]

/-- Every complete original source Q-assignment sum whose complex
amplitude separates between selected δ=true slots and skipped δ=false
slots factors EXACTLY into a selected-prime sum times an original
`OrderedQSkip` prime sum. This is the finite factorisation needed
AFTER Parity's Fourier gate separation, not a claim about the raw smooth
gate weights (which still depend on both tuples). -/
theorem parity_source_Q_full_factor_selected_skipped434
    {n : ℕ} (Q : Fin n → Finset ℕ) (δ : Fin n → Bool)
    (A : paritySourceQSelected434 n Q δ → ℂ)
    (B : OrderedQSkip n Q δ → ℂ) :
    (∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
      A (fun i => p i.val) * B (fun i => p i.val)) =
    (∑ a : paritySourceQSelected434 n Q δ, A a) *
      (∑ b : OrderedQSkip n Q δ, B b) := by
  let Φ := paritySourceQAllSelectedSkipEquiv434 Q δ
  calc
    (∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
      A (fun i => p i.val) * B (fun i => p i.val)) =
      ∑ x : paritySourceQSelected434 n Q δ × OrderedQSkip n Q δ,
        A x.1 * B x.2 := by
      apply Fintype.sum_equiv Φ
      intro p
      rfl
    _ = (∑ a : paritySourceQSelected434 n Q δ, A a) *
      (∑ b : OrderedQSkip n Q δ, B b) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalFourierSelectedResidual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 33000

/-- The LITERAL source Fourier character contribution from the δ=true
prime slots. Unlike the original skipped B509 residual, it is a function
ONLY of the selected Q prime assignment, with all original
`sourceSlotFrequency` values and repeated prime factors retained. -/
def paritySourceQSelectedFourierPhase434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (a : paritySourceQSelected434 n Q δ) : ℂ :=
  ∏ i : {i : Fin n // δ i = true},
    ((Real.fourierChar
      (Real.log ((a i).val : ℝ) * sourceSlotFrequency s ξ δ i.val) : Circle) : ℂ)

/-- The ORIGINAL selected prime factors of the full Q Fourier product
equal precisely the independent selected-Q phase; they cannot depend
on any skipped Q-prime value. This is the exact separation needed to
extract a Fourier coefficient a_e AFTER the B590 smooth gate is Fourier
transformed. -/
theorem parity_source_selected_fourier_phase_depends_only_selected434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    paritySourceAllocatedSlotFourierPhase434 s ξ δ p =
      paritySourceQSelectedFourierPhase434 s ξ δ (fun i => p i.val) := by
  classical
  let f : Fin n → ℂ := fun i =>
    ((Real.fourierChar
      (Real.log ((p i).val : ℝ) * sourceSlotFrequency s ξ δ i) : Circle) : ℂ)
  unfold paritySourceAllocatedSlotFourierPhase434
    paritySourceQSelectedFourierPhase434
  exact Finset.prod_subtype
    (s := Finset.univ.filter (fun i : Fin n => δ i = true))
    (p := fun i : Fin n => δ i = true)
    (by intro i; simp) f

/-- The complete native SOURCE Q Fourier/factorial weight is exactly
an independent selected-Q phase times the already original B509
unselected Q phase. This factorisation is literal for each FULL Q tuple,
with no estimate and no branch-weight assumption. -/
theorem parity_source_full_fourier_factorial_as_selected_skip434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r d : ℕ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    sourceActualSortedFactorial r d *
      paritySourceFullSlotFourierPhase434 s ξ δ p =
      paritySourceQSelectedFourierPhase434 s ξ δ (fun i => p i.val) *
        (sourceActualSortedFactorial r d *
          orderedSkipPhase (δ := δ) s ξ (fun i => p i.val)) := by
  rw [parity_source_full_slot_fourier_factorial_split434,
    parity_source_selected_fourier_phase_depends_only_selected434]

/-- Exact ORIGINAL finite source full-Q Fourier sum =
selected-source Fourier coefficient SUM × original B509 skipped-source
Fourier sum, BEFORE Fourier-gate integration. This is a true algebraic
factorization over ALL original labelled Q-prime choices, including
repetition, made possible by the exact δ-partition equivalence. -/
theorem parity_source_full_fourier_factorial_sum_selected_skip434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (r d : ℕ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool) :
    (∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
      sourceActualSortedFactorial r d *
        paritySourceFullSlotFourierPhase434 s ξ δ p) =
    (∑ a : paritySourceQSelected434 n Q δ,
      paritySourceQSelectedFourierPhase434 s ξ δ a) *
      (∑ b : OrderedQSkip n Q δ,
        sourceActualSortedFactorial r d * orderedSkipPhase s ξ b) := by
  let A : paritySourceQSelected434 n Q δ → ℂ :=
    paritySourceQSelectedFourierPhase434 s ξ δ
  let B : OrderedQSkip n Q δ → ℂ :=
    fun b => sourceActualSortedFactorial r d * orderedSkipPhase s ξ b
  calc
    (∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
      sourceActualSortedFactorial r d *
        paritySourceFullSlotFourierPhase434 s ξ δ p) =
      ∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
        A (fun i => p i.val) * B (fun i => p i.val) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact parity_source_full_fourier_factorial_as_selected_skip434
          r d s ξ δ p
    _ = (∑ a : paritySourceQSelected434 n Q δ, A a) *
        (∑ b : OrderedQSkip n Q δ, B b) :=
          parity_source_Q_full_factor_selected_skipped434 Q δ A B
end Green64Analytic.Parity

end

end

/-! ## OriginalB509SelectedResidual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 34000

/-- Exact finite support of the ORIGINAL B509 unsmoothed
`orderedSkipProduct` endpoint map. This is NOT a numerical truncation:
all unselected Q primes, including repeats, contribute to its image. -/
def paritySourceB509SkipEndpointSupport434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool) : Finset ℕ :=
  (Finset.univ : Finset (OrderedQSkip n Q δ)).image orderedSkipProduct

/-- The NATIVE `sourceEndpointFibre` of the ORIGINAL B509 skipped Q
primes has EXACT total mass equal to the underlying labelled prime
sum, for arbitrary frequencies/complex phases, no collision loss.
Every endpoint collision remains inside the fibre with its full
factorial and Fourier phase; no source data is discarded. -/
theorem parity_source_B509_skip_endpoint_total_exact434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool)
    (r d : ℕ) (s ξ : Fin n → ℝ) :
    (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q := Q) δ,
      sourceEndpointFibre (Finset.univ : Finset (OrderedQSkip n Q δ))
        orderedSkipProduct
        (fun a => sourceActualSortedFactorial r d * orderedSkipPhase s ξ a) h) =
      ∑ a : OrderedQSkip n Q δ,
        sourceActualSortedFactorial r d * orderedSkipPhase s ξ a := by
  let S : Finset (OrderedQSkip n Q δ) := Finset.univ
  let f : OrderedQSkip n Q δ → ℂ :=
    fun a => sourceActualSortedFactorial r d * orderedSkipPhase s ξ a
  have hReindex := Finset.sum_image'
    (s := S) (g := orderedSkipProduct)
    (f := fun h => sourceEndpointFibre S orderedSkipProduct f h)
    f (by intro a ha; rfl)
  simpa only [paritySourceB509SkipEndpointSupport434,S,f,sourceEndpointFibre]
    using hReindex

/-- Concrete TRUE actual B509 `sourceNativePrimeCore.residual` has the
same endpoint fibre as the frozen SOURCE code, and summing its exact
physical `h`-support equals the true skip-prime Fourier/factorial sum.
This restores the literal residual factor in Parity(4.7) without assuming
an analytically favourable residual or an artificial injected endpoint. -/
theorem parity_actual_B509_native_prime_core_residual_total434
    (r d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    let Q := sourceActualSortedQ r d L band slot
    let s := sourceActualSortedFrequencyScales r d L band slot
    let F := sourceNativePrimeCore r d L band slot δ ξ
      K alpha q χ σ₀ σ₁
    (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q := Q) δ,
      F.residual h) =
    ∑ a : OrderedQSkip (sourceOrderedLabels r
      (sourceActualSortedScales r d L) band slot).length Q δ,
      sourceActualSortedFactorial r d * orderedSkipPhase s
        ξ a := by
  dsimp only
  exact parity_source_B509_skip_endpoint_total_exact434 δ r d
    (sourceActualSortedFrequencyScales r d L band slot)
    ξ
end Green64Analytic.Parity

end

end

/-! ## ActualB509FullSelectedResidual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 33000

/-- The FULL ORIGINAL Q-prime Fourier/factorial source sum factors at
EVERY actual moving Q depth, mark and Boolean allocation δ as
  [selected-only Fourier sum] × [true B509 source residual sum over h].
The right factor is EXACTLY `sourceNativePrimeCore.residual` for any
actual α, K, q, χ and Mellin frequencies: no assumed endpoint
injectivity, no altered 20! and no discarded Q-prime multiplicity.
This is the exact finite Fourier algebra required for Parity(4.7),
BEFORE smooth gate Fourier integration, original reserved H and TypeII. -/
theorem parity_actual_B509_original_fullQ_selected_native_residual_factor434
    (r d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    let Q := sourceActualSortedQ r d L band slot
    let s := sourceActualSortedFrequencyScales r d L band slot
    let F := sourceNativePrimeCore r d L band slot δ ξ K alpha q χ σ₀ σ₁
    (∑ p : (i : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) band slot).length) →
        {z : ℕ // z ∈ Q i},
      sourceActualSortedFactorial r d *
        paritySourceFullSlotFourierPhase434 s ξ δ p) =
      (∑ a : paritySourceQSelected434
        (sourceOrderedLabels r (sourceActualSortedScales r d L)
          band slot).length Q δ,
        paritySourceQSelectedFourierPhase434 s ξ δ a) *
      (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q := Q) δ,
        F.residual h) := by
  dsimp only
  let Q := sourceActualSortedQ r d L band slot
  let s := sourceActualSortedFrequencyScales r d L band slot
  let F := sourceNativePrimeCore r d L band slot δ ξ K alpha q χ σ₀ σ₁
  have hSplit := parity_source_full_fourier_factorial_sum_selected_skip434
    Q r d s ξ δ
  have hSkip := parity_actual_B509_native_prime_core_residual_total434
    r d L band slot δ ξ K alpha q χ σ₀ σ₁
  dsimp only at hSkip
  calc
    _ = (∑ a : paritySourceQSelected434
          (sourceOrderedLabels r (sourceActualSortedScales r d L)
            band slot).length Q δ,
          paritySourceQSelectedFourierPhase434 s ξ δ a) *
        (∑ b : OrderedQSkip
          (sourceOrderedLabels r (sourceActualSortedScales r d L)
            band slot).length Q δ,
          sourceActualSortedFactorial r d * orderedSkipPhase s ξ b) := hSplit
    _ = _ := by rw [←hSkip]
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedFourierEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- Actual SOURCE allocated-e selected Q-prime product on the SELECTED
δ=true dependent prime tuple. No skipped-prime information appears. -/
def paritySourceQSelectedPrimeProduct434
    {n : ℕ} {Q : Fin n → Finset ℕ} {δ : Fin n → Bool}
    (a : paritySourceQSelected434 n Q δ) : ℕ :=
  ∏ i : {i : Fin n // δ i = true}, (a i).val

/-- Original Fourier-separated selected e-side source coefficient for
fixed real frequencies and allocation δ, grouped EXACTLY by integer e.
It is the literal `sourceEndpointFibre` of the selected prime tuple and
`sourceSlotFrequency` Fourier characters; it has no dependence on skipped
Q primes or on B509 residual endpoint h. This is the algebraic a_e-side
FIBRE before remaining original Fourier kernels/branch integration. -/
def paritySourceQSelectedFourierEFibre434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool)
    (s ξ : Fin n → ℝ) (e : ℕ) : ℂ :=
  sourceEndpointFibre
    (Finset.univ : Finset (paritySourceQSelected434 n Q δ))
    paritySourceQSelectedPrimeProduct434
    (paritySourceQSelectedFourierPhase434 s ξ δ) e

/-- True exact source selected e support: every contributing selected
Q-prime tuple has e in the literal finite image of its prime product. -/
def paritySourceQSelectedESupport434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool) : Finset ℕ :=
  (Finset.univ : Finset (paritySourceQSelected434 n Q δ)).image
    paritySourceQSelectedPrimeProduct434

/-- The ORIGINAL selected-side source Fourier amplitude is exactly
its sum over the actual selected integer e fibres, with no loss at
repeated-prime products and no restriction on real Fourier frequencies. -/
theorem parity_source_selected_fourier_e_fibre_reindex434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool)
    (s ξ : Fin n → ℝ) :
    (∑ a : paritySourceQSelected434 n Q δ,
      paritySourceQSelectedFourierPhase434 s ξ δ a) =
    ∑ e ∈ paritySourceQSelectedESupport434 (Q := Q) δ,
      paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e := by
  let S : Finset (paritySourceQSelected434 n Q δ) := Finset.univ
  let w : paritySourceQSelected434 n Q δ → ℂ :=
    paritySourceQSelectedFourierPhase434 (Q := Q) s ξ δ
  let g := (paritySourceQSelectedPrimeProduct434 :
    paritySourceQSelected434 n Q δ → ℕ)
  have hReindex := Finset.sum_image'
    (s := S) (g := g)
    (f := fun e => sourceEndpointFibre S g w e)
    w (by intro a ha; rfl)
  simpa only [paritySourceQSelectedESupport434,
    paritySourceQSelectedFourierEFibre434,S,g,w,sourceEndpointFibre] using hReindex.symm

/-- Literal FULL original B509 Q-prime Fourier/factorial sum at fixed
δ and ξ = sum over exact selected integer e-source coefficients times
the sum over the original `sourceNativePrimeCore.residual(h)` physical
h endpoint range. This is the exact finite **a_e side × residual side**
source interface for Parity (4.7), BEFORE Fourier gate transforms and
reserved-prime/P-group bookkeeping. -/
theorem parity_actual_B509_original_fullQ_e_fibre_native_residual_factor434
    (r d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    let Q := sourceActualSortedQ r d L band slot
    let s := sourceActualSortedFrequencyScales r d L band slot
    let F := sourceNativePrimeCore r d L band slot δ ξ K alpha q χ σ₀ σ₁
    (∑ p : (i : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) band slot).length) →
        {z : ℕ // z ∈ Q i},
      sourceActualSortedFactorial r d *
        paritySourceFullSlotFourierPhase434 s ξ δ p) =
      (∑ e ∈ paritySourceQSelectedESupport434 (Q := Q) δ,
        paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e) *
      (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q := Q) δ,
        F.residual h) := by
  dsimp only
  have hOriginal := parity_actual_B509_original_fullQ_selected_native_residual_factor434
    r d L band slot δ ξ K alpha q χ σ₀ σ₁
  dsimp only at hOriginal
  rw [hOriginal]
  rw [parity_source_selected_fourier_e_fibre_reindex434]
end Green64Analytic.Parity

end

end

/-! ## ActualSelectedFourierEFibreBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 30000

/-- The true original selected δ=true source Q-prime endpoint has at
most `(r!)^(d+1)` preimages for any integer e. Distinct real Q bands
and all 20 original marks are respected; repeated primes contribute
their true factorial orbit counts rather than being assumed distinct.
This is the key exact combinatorial Parity(4.9) selected-a_e bound. -/
theorem parity_actual_source_selected_e_collision_le_factorials434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (e : ℕ) :
    let n := (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length
    let Q := sourceActualSortedQ r d L band slot
    sourceEndpointCollisionCount
      (Finset.univ : Finset (paritySourceQSelected434 n Q δ))
      paritySourceQSelectedPrimeProduct434 e ≤ r.factorial^(d+1) := by
  dsimp only
  let n := (sourceOrderedLabels r (sourceActualSortedScales r d L)
    band slot).length
  let T := {z : Fin n // δ z = true}
  let Q := sourceActualSortedQ r d L band slot
  let label := fun z : Fin n =>
    (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) band slot z).val.1
  have hPrime : ∀ j p, p ∈ sourceOriginalQActualBands r d L j → p.Prime :=
    source_original_Q_actual_prime r d L
  have hDisj : ∀ j k p, p ∈ sourceOriginalQActualBands r d L j →
      p ∈ sourceOriginalQActualBands r d L k → j=k :=
    source_original_Q_actual_all_disjoint r d L hr hL
  have hSame (z : T) : Q z.val = sourceOriginalQActualBands r d L (label z.val) := rfl
  have hCollision := source_labelled_slot_collision_card_le_of_finset T
    (fun z : T => Q z.val) (fun z : T => label z.val)
    (sourceOriginalQActualBands r d L)
    (Finset.univ : Finset (paritySourceQSelected434 n Q δ))
    e hSame hPrime hDisj
  have hTerm (j : Fin (d+1)) :
      Fintype.card {z : T // label z.val=j} ≤ r := by
    let F : {z : T // label z.val=j} → Fin r := fun z =>
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L)
        band slot z.val.val).val.2
    have hinj : Function.Injective F := by
      intro z w he
      apply Subtype.ext
      apply Subtype.ext
      apply (sourceSortedLabelEquiv r
        (sourceActualSortedScales r d L) band slot).injective
      exact Subtype.ext (Prod.ext (z.property.trans w.property.symm) he)
    calc
      Fintype.card {z : T // label z.val=j} ≤ Fintype.card (Fin r) :=
        Fintype.card_le_of_injective F hinj
      _ = r := Fintype.card_fin _
  have hEq : (paritySourceQSelectedPrimeProduct434 :
        paritySourceQSelected434 n Q δ → ℕ) =
      (fun a => ∏ z : T, (a z).val) := rfl
  rw [hEq]
  calc
    sourceEndpointCollisionCount
      (Finset.univ : Finset (paritySourceQSelected434 n Q δ))
      (fun a => ∏ z : T, (a z).val) e ≤
      ∏ j : Fin (d+1), (Fintype.card {z : T // label z.val=j}).factorial :=
        hCollision
    _ ≤ ∏ _j : Fin (d+1), r.factorial := by
      apply Finset.prod_le_prod₀
      · intro j hj; exact Nat.zero_le _
      · intro j hj
        exact Nat.factorial_le (hTerm j)
    _ = r.factorial^(d+1) := by simp

/-- The native B509 selected Fourier phase has norm ONE, for arbitrary
real ξ and all source selected prime assignments. -/
theorem parity_source_selected_fourier_phase_norm_one434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (a : paritySourceQSelected434 n Q δ) :
    ‖paritySourceQSelectedFourierPhase434 s ξ δ a‖ = 1 := by
  simp [paritySourceQSelectedFourierPhase434,norm_prod]

/-- Exact original Parity(4.9) source arithmetic coefficient bound for
every actual r20 sorted-Q selected e-fibre at FIXED δ, ξ:
    norm a_e(e) <= (20!)^(j_x+1).
This is derived from true Q-band uniqueness and the unit Fourier phase;
there is no assumed factorisation-count estimate. The historical a_e
still has to include the other Fourier gate, reserved prime and physical
amplitude, so this theorem concerns its precise selected Q-source fibre. -/
theorem parity_actual_source_selected_fourier_e_fibre_norm_le_factorials434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → ℝ)
    (e : ℕ) :
    let Q := sourceActualSortedQ r d L band slot
    let s := sourceActualSortedFrequencyScales r d L band slot
    ‖paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e‖ ≤
      (r.factorial : ℝ)^(d+1) := by
  dsimp only
  let n := (sourceOrderedLabels r (sourceActualSortedScales r d L)
    band slot).length
  let Q := sourceActualSortedQ r d L band slot
  let s := sourceActualSortedFrequencyScales r d L band slot
  let S := (Finset.univ : Finset (paritySourceQSelected434 n Q δ))
  have hBound := source_endpoint_fibre_norm_le S
    paritySourceQSelectedPrimeProduct434
    (paritySourceQSelectedFourierPhase434 s ξ δ) e 1 (by
      intro a ha he
      simp only [parity_source_selected_fourier_phase_norm_one434,le_refl])
  have hCount : (sourceEndpointCollisionCount S
      paritySourceQSelectedPrimeProduct434 e : ℝ) ≤
      (r.factorial : ℝ)^(d+1) := by
    exact_mod_cast parity_actual_source_selected_e_collision_le_factorials434
      r d L hr hL band slot δ e
  change ‖sourceEndpointFibre S paritySourceQSelectedPrimeProduct434
    (paritySourceQSelectedFourierPhase434 s ξ δ) e‖ ≤ _
  calc
    _ ≤ (sourceEndpointCollisionCount S
      paritySourceQSelectedPrimeProduct434 e : ℝ) * 1 := hBound
    _ ≤ (r.factorial : ℝ)^(d+1) := by simpa using hCount
end Green64Analytic.Parity

end

end

/-! ## OriginalACompleteLabelledSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- The ACTUAL historical `sourceOriginalOrdinaryCoefficient` is
EXACTLY the full sum over ALL original labelled Q-prime choices with
the precise product gate, weighted by the ORIGINAL per-band factorial.
The equality uses the already formalized canonical-orbit-iff-product,
which handles repeated primes, not a synthetic orbit replacement.
This is the original *unsmoothed* source coefficient, not Parity (4.7)
post-Fourier a_e. -/
theorem parity_source_original_ordinary_coefficient_full_labelled434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b=c) :
    sourceOriginalOrdinaryCoefficient r Q v =
      ∑ f : ((b : B) → Fin r → {q : ℕ // q ∈ Q b}),
        if (∏ b : B, ∏ i : Fin r, (f b i).val)=v then
          (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) else 0 := by
  have hOrbit : sourceOriginalFullQOrbitAt r Q v =
      (Finset.univ : Finset ((b : B) → Fin r → {q : ℕ // q ∈ Q b})).filter
        (fun f => (∏ b : B, ∏ i : Fin r, (f b i).val)=v) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact source_original_full_Q_canonical_orbit_iff_product
      r Q v f hPrime hDisjoint
  rw [source_original_full_Q_coefficient_finite_sampling
    r Q v hPrime hDisjoint]
  rw [hOrbit,Finset.sum_filter]

/-- The full HISTORICAL `sourceOriginalA`, including its original
W1(P,u), the EXACT multiplicity-counted odd-parity projector and the
true complete Q factorial orbit, is the literal full prime-labelled
finite sum with an exact product gate. This makes the true native source
arithmetic ready for the B590 smooth allocation branch and B509 Fourier
factorization without duplicate factorial normalizations. -/
theorem parity_source_original_A_full_labelled_orbit_exact434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (u : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b=c) :
    sourceOriginalA r Q P u =
      ∑ f : ((b : B) → Fin r → {q : ℕ // q ∈ Q b}),
        if (∏ b : B, ∏ i : Fin r, (f b i).val) =
          sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u then
          (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
            sourceOriginalW1 P u *
            ((1-(-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion P) u)/2)
        else 0 := by
  let v := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  have hCoefficient := parity_source_original_ordinary_coefficient_full_labelled434
    r Q v hPrime hDisjoint
  unfold sourceOriginalA sourceOriginalA0
  rw [hCoefficient]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB509PointwiseEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 33000

/-- EXACT full original Q-prime B509 native Fourier/factorial source
coefficient at ONE fixed selected integer e. The selected-endpoint
function uses only original δ=true Q primes, while all original
δ=false Q primes remain INSIDE the same summation and retain the B509
normalizer and `sourceSlotFrequency`; repeated primes are not ignored. -/
def paritySourceFullQFourierFixedEFibre434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r d : ℕ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool) (e : ℕ) : ℂ :=
  sourceEndpointFibre
    (Finset.univ : Finset ((i : Fin n) → {q : ℕ // q ∈ Q i}))
    (fun p => paritySourceQSelectedPrimeProduct434 (δ := δ) (fun i => p i.val))
    (fun p => sourceActualSortedFactorial r d *
      paritySourceFullSlotFourierPhase434 s ξ δ p) e

/-- SOURCE Parity(4.7) a_e × B509 skipped-Q residual identity at each
**individual integer e**, rather than only after summing over all e.
It is a literal EXACT finite equality, using actual `sourceEndpointFibre`
of the original complete labelled Q tuple and a true selected/skip Pi
bijection. No assumptions about disjoint selected primes, endpoint
uniqueness or artificial cancellation; no analytic TypeII bound claimed. -/
theorem parity_source_full_fourier_fixed_e_selected_skip_factor434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r d : ℕ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool) (e : ℕ) :
    paritySourceFullQFourierFixedEFibre434 (Q := Q) r d s ξ δ e =
      paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e *
        (∑ b : OrderedQSkip n Q δ,
          sourceActualSortedFactorial r d * orderedSkipPhase s ξ b) := by
  classical
  let A : paritySourceQSelected434 n Q δ → ℂ :=
    fun a => if paritySourceQSelectedPrimeProduct434 a = e then
      paritySourceQSelectedFourierPhase434 s ξ δ a else 0
  let B : OrderedQSkip n Q δ → ℂ :=
    fun b => sourceActualSortedFactorial r d * orderedSkipPhase s ξ b
  have hFull : paritySourceFullQFourierFixedEFibre434 (Q := Q) r d s ξ δ e =
      ∑ p : (i : Fin n) → {q : ℕ // q ∈ Q i},
        A (fun i => p i.val) * B (fun i => p i.val) := by
    unfold paritySourceFullQFourierFixedEFibre434 sourceEndpointFibre
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hE : paritySourceQSelectedPrimeProduct434 (δ := δ) (fun i => p i.val)=e
    · simp only [hE,ite_true,A]
      exact parity_source_full_fourier_factorial_as_selected_skip434
        r d s ξ δ p
    · simp [A,hE]
  have hSelected : (∑ a : paritySourceQSelected434 n Q δ, A a) =
      paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e := by
    unfold paritySourceQSelectedFourierEFibre434 sourceEndpointFibre
    rw [Finset.sum_filter]
  calc
    _ = (∑ a : paritySourceQSelected434 n Q δ, A a) *
        (∑ b : OrderedQSkip n Q δ, B b) :=
          hFull.trans (parity_source_Q_full_factor_selected_skipped434 Q δ A B)
    _ = _ := by rw [hSelected]

/-- Exact pointwise SOURCE factor with the actual B509
`sourceNativePrimeCore.residual` at ANY original moving r,d band/slot,
for all Q-characters, K, α, Mellin phases and selected integer e. The
coefficient on the left is the true COMPLETE labelled native B509 full
Fourier/factorial fibre at this e, not a proxy with missing Q phases. -/
theorem parity_actual_B509_original_pointwise_e_fibre_native_factor434
    (r d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L)
      band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (e : ℕ) :
    let Q := sourceActualSortedQ r d L band slot
    let s := sourceActualSortedFrequencyScales r d L band slot
    let F := sourceNativePrimeCore r d L band slot δ ξ K alpha q χ σ₀ σ₁
    paritySourceFullQFourierFixedEFibre434 (Q := Q) r d s ξ δ e =
      paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e *
        (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q := Q) δ,
          F.residual h) := by
  dsimp only
  have hFactor := parity_source_full_fourier_fixed_e_selected_skip_factor434
    (Q := sourceActualSortedQ r d L band slot) r d
    (sourceActualSortedFrequencyScales r d L band slot) ξ δ e
  have hResidual := parity_actual_B509_native_prime_core_residual_total434
    r d L band slot δ ξ K alpha q χ σ₀ σ₁
  dsimp only at hResidual
  rw [hFactor, hResidual]
end Green64Analytic.Parity

end

end

/-! ## ActualSelectedFourierESupport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 35000

/-- A nonzero native selected-Q Fourier coefficient at integer e has
an actual original selected prime assignment witness with that EXACT
integer product. This does NOT assume noncancellation of Fourier phases;
nonzero finite sum merely implies a nonempty original source fibre. -/
theorem parity_source_selected_fourier_e_fibre_nonzero_support434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool)
    (s ξ : Fin n → ℝ) (e : ℕ)
    (hNonzero : paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e ≠ 0) :
    e ∈ paritySourceQSelectedESupport434 (Q := Q) δ := by
  by_contra hNot
  have hZero : paritySourceQSelectedFourierEFibre434 (Q := Q) δ s ξ e = 0 := by
    unfold paritySourceQSelectedFourierEFibre434 sourceEndpointFibre
    apply Finset.sum_eq_zero
    intro a ha
    have hMatch := (Finset.mem_filter.mp ha).2
    have hSupport : e ∈ paritySourceQSelectedESupport434 (Q := Q) δ :=
      Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hMatch⟩
    exact (hNot hSupport).elim
  exact hNonzero hZero

/-- EVERY selected original Q-prime tuple from the true dynamic r20
moving Q-bands is eventually an ODD positive selected e-product;
original factorial/source repeated primes are kept, no assumption of
squarefreeness or unit modulo arbitrary k. -/
theorem parity_eventually_actual_selected_prime_product_odd434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (a : paritySourceQSelected434
          (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length
          (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot) δ),
      Odd (paritySourceQSelectedPrimeProduct434 a) := by
  filter_upwards [parity_eventually_actual_sorted_Q_slot_prime_floor434] with L hQ
  refine ⟨hQ.1,?_⟩
  intro band slot δ a
  unfold paritySourceQSelectedPrimeProduct434
  apply Finset.prod_induction (p := Odd)
  · intro x y hx hy
    exact hx.mul hy
  · decide
  · intro i hi
    have hp := hQ.2 band slot i.val (a i).val (a i).property
    exact hp.1.odd_of_ne_two (by omega)

/-- Every original P-band prime is absent from the ORIGINAL selected
Q-prime e-product, using actual Q/P disjointness, not assumed P-coprimality.
The statement preserves all selected slot multiplicities. -/
theorem parity_actual_source_selected_e_no_P_divisor434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (a : paritySourceQSelected434
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
        band slot).length (sourceActualSortedQ 20 d L band slot) δ)
    (g : sourceOriginalPAllGroupType 20 L) (q : ℕ)
    (hq : q ∈ sourceOriginalPAllActualBands 20 L g) :
    ¬q ∣ paritySourceQSelectedPrimeProduct434 a := by
  let T := {i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length // δ i = true}
  have hPrime := source_original_P_all_actual_band_prime 20 L g q hq
  unfold paritySourceQSelectedPrimeProduct434
  apply source_original_prime_not_dvd_finset_product
    q hPrime (fun i : T => (a i).val) Finset.univ
  intro i hi hDvd
  let j := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
    band slot i.val).val.1
  have hQ : (a i).val ∈ sourceOriginalQActualBands 20 d L j := (a i).property
  have hPrimeQ := source_original_Q_actual_prime 20 d L j (a i).val hQ
  have hEq := (Nat.prime_dvd_prime_iff_eq hPrime hPrimeQ).mp hDvd
  exact source_original_Q_actual_all_P_disjoint 20 d L (by norm_num)
    hL j g q (hEq ▸ hQ) hq

/-- For EVERY nonzero selected e-side Fourier coefficient in the actual
original r20 moving Q geometry, e is odd, positive, invertible mod2,
its full original P-multiplicity exponent is ZERO, and multiplication
by e cannot change original source W1. Unlike the older full-tuple
support theorem, this applies DIRECTLY to the independent selected-only
fixed-frequency `a_e` source coefficient. -/
theorem parity_eventually_actual_selected_fourier_e_support434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (e : ℕ),
      paritySourceQSelectedFourierEFibre434
        (Q := sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        δ (sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot) ξ e ≠ 0 →
      Odd e ∧ 0 < e ∧ IsUnit (e : ZMod 2) ∧
      sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) e = 0 ∧
      ∀ v : ℕ, v ≠ 0 →
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (e*v) =
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v := by
  filter_upwards [parity_eventually_actual_selected_prime_product_odd434]
    with L hOdd
  refine ⟨hOdd.1,?_⟩
  intro band slot δ ξ e hCoefficient
  have hS := parity_source_selected_fourier_e_fibre_nonzero_support434
    δ (sourceActualSortedFrequencyScales 20
      (sourceOriginalLiteralDepth 20 L) L band slot) ξ e hCoefficient
  obtain ⟨a,ha,hProduct⟩ := Finset.mem_image.mp hS
  have heOdd : Odd e := by
    rw [←hProduct]
    exact hOdd.2 band slot δ a
  have hePos := heOdd.pos
  have hLPos : 0 < L := by linarith [hOdd.1]
  let P := sourceOriginalPAllActualBands 20 L
  have hPPrime : ∀ g p, p ∈ P g → p.Prime := by
    intro g p hp
    exact source_original_P_all_actual_band_prime 20 L g p hp
  have hNoP : ∀ g p, p ∈ P g → ¬p ∣ e := by
    intro g p hp
    rw [←hProduct]
    exact parity_actual_source_selected_e_no_P_divisor434
      (sourceOriginalLiteralDepth 20 L) L hLPos band slot δ a g p hp
  have hNoAll : ∀ p ∈ Finset.univ.biUnion P, ¬p ∣ e := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hNoP g p hpg
  have hParity : sourceOriginalPParityExponent
      (Finset.univ.biUnion P) e = 0 := by
    have hh := source_original_P_multiplicity_nonP_mul
      (Finset.univ.biUnion P) e 1 hePos.ne' (by norm_num) hNoAll
    simpa [sourceOriginalPParityExponent] using hh
  refine ⟨heOdd,hePos,
    (ZMod.isUnit_iff_coprime _ 2).mpr
      (Nat.coprime_two_right.mpr heOdd),hParity,?_⟩
  intro v hv
  exact source_original_W1_nonP_mul P e v hPPrime hNoP
end Green64Analytic.Parity

end

end

/-! ## OriginalXACompleteLabelledSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 34000

/-- The FULL HISTORICAL original `sourceOriginalXA`, on the precise
`u ∈ range(floor(2*x)+1)` carrier, is exactly a double finite sum over
EVERY original labelled complete Q-prime assignment in every band.
The original factorial per band, source W1 mark, multiplicity-counted
P-parity projector and original Psi((u:ℝ)/x) survive LITERALLY.
The only gate on the inner assignment is its exact full Q product
`sourceOriginalOrdinaryPart(Pall,u)`; repeated Q primes are retained.
This establishes the actual source arithmetic from which the smooth
allocation must start, NOT a new surrogate `sourceOriginalXA`. -/
theorem parity_source_original_XA_complete_labelled_exact434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Psi : ℝ → ℝ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b=c) :
    sourceOriginalXA r Q P x Psi =
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        ∑ f : ((b : B) → Fin r → {q : ℕ // q ∈ Q b}),
          if (∏ b : B, ∏ i : Fin r, (f b i).val) =
            sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u then
            (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
              sourceOriginalW1 P u *
              ((1-(-1:ℝ)^sourceOriginalPParityExponent
                (Finset.univ.biUnion P) u)/2) * Psi ((u:ℝ)/x)
          else 0 := by
  unfold sourceOriginalXA
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_source_original_A_full_labelled_orbit_exact434
    r Q P u hPrime hDisjoint]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> ring
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalACompleteLabelled -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 30000

/-- The LITERAL actual original r=20 `sourceOriginalA`, with every Q
band `sourceOriginalQActualBands 20 d L` and original actual P groups,
is the exact ALL-Q-labelled product-gated finite sum. Prime support and
cross-band disjointness are PROVED source theorems for real L>0; no
additional user assumption, no source A replacement, no squarefree
restriction, and the `20!` normalization is kept unchanged. -/
theorem parity_actual_original_A_all_Q_labelled_exact434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) :
    sourceOriginalA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u =
    ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      if (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
        sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((1-(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2)
      else 0 := by
  have hPrime : ∀ b p, p ∈ sourceOriginalQActualBands 20 d L b → p.Prime :=
    source_original_Q_actual_prime 20 d L
  have hDisjoint : ∀ b c p, p ∈ sourceOriginalQActualBands 20 d L b →
      p ∈ sourceOriginalQActualBands 20 d L c → b=c :=
    source_original_Q_actual_all_disjoint 20 d L (by norm_num) hL
  exact parity_source_original_A_full_labelled_orbit_exact434 20
    (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u hPrime hDisjoint

/-- The COMPLETE literal actual SOURCE `sourceOriginalXA` using its
original finite u cutoff, original Ψ((u:ℝ)/x), marked W1 and
multiplicity parity, and all 20 labelled prime slots per source Q band,
is exactly a DOUBLE finite sum over original complete Q assignments.
This exact identity is valid for every d (including moving depth) and
L>0 without any presumed Parity TypeII or E4.1 correlation estimate. -/
theorem parity_actual_original_XA_all_Q_labelled_exact434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (x : ℝ) (Psi : ℝ → ℝ) :
    sourceOriginalXA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi =
    ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        if (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
          sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
          (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((1-(-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2) *
            Psi ((u:ℝ)/x)
        else 0 := by
  have hPrime : ∀ b p, p ∈ sourceOriginalQActualBands 20 d L b → p.Prime :=
    source_original_Q_actual_prime 20 d L
  have hDisjoint : ∀ b c p, p ∈ sourceOriginalQActualBands 20 d L b →
      p ∈ sourceOriginalQActualBands 20 d L c → b=c :=
    source_original_Q_actual_all_disjoint 20 d L (by norm_num) hL
  exact parity_source_original_XA_complete_labelled_exact434 20
    (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) x Psi hPrime hDisjoint
end Green64Analytic.Parity

end

end

/-! ## OriginalAAllocationDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 34000

/-- The ORIGINAL source-A weight of a complete labelled Q-tuple,
with no loss of 20! factorials, original W1 or P parity. -/
def parityActualOriginalAFullTupleWeight434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) : ℝ :=
  if (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
    (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2)
  else 0

/-- The exact total buffered B590 mass of all labelled assignments
for the ACTUAL remaining sorted Q slots after a reserved Q prime. -/
def parityActualOriginalAFullTupleAllocationMass434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) : ℝ :=
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  ∑ δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool,
    parityOriginalQAllocationBranchWeight434 20 E s δ (fun i => (p i).val)

/-- EXACT ORIGINAL SOURCE arithmetic discrepancy after inserting the
true B590 buffered f0/f1 gates and summing ALL assignments, at any
original Q-band, reserved prime, E and u. No claim of partition mass 1:
the non-unit buffer is retained as the EXPLICIT source-mapping error.
This is the missing starting point for the Parity (4.7) source equality. -/
theorem parity_actual_original_A_full_Q_buffered_allocation_defect434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) :
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u -
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          parityActualOriginalAFullTupleAllocationMass434 d L E band slot f =
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          (1 - parityActualOriginalAFullTupleAllocationMass434 d L E band slot f) := by
  rw [parity_actual_original_A_all_Q_labelled_exact434 d L hL u]
  change (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f) -
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          parityActualOriginalAFullTupleAllocationMass434 d L E band slot f) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  ring


/-- Original SOURCE XA restricted to precisely its historical real Ψ
and full u cutoff, but multiplied by the complete true B590 allocation
mass of each original labelled Q tuple. This is a defined descendant,
not a replacement definition of `sourceOriginalXA`. -/
def parityActualOriginalXAWithAllocationMass434
    (d : ℕ) (L E x : ℝ) (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f *
        parityActualOriginalAFullTupleAllocationMass434 d L E band slot f) *
      Psi ((u:ℝ)/x)

/-- Literal source-XA error of applying all B590 buffered gates,
including the u=0 endpoint: exactly original weights times (1-mass).
This is not an error bound. Its quantity is the outstanding source
allocation defect that must be bounded BEFORE historical a_e(4.7). -/
def parityActualOriginalXAAllocationDefect434
    (d : ℕ) (L E x : ℝ) (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f *
        (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) *
      Psi ((u:ℝ)/x)

/-- The ACTUAL `sourceOriginalXA` splits into its entire original
B590-allocated physical sum and a literal, unestimated buffer defect;
all actual P/Q bands, labelled multiplicities, full u carrier and
original Ψ persist. No assumption of total allocation mass 1. -/
theorem parity_actual_source_XA_eq_allocated_plus_exact_buffer_defect434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (Psi : ℝ → ℝ) (band : Fin (d+1)) (slot : Fin 20) :
    sourceOriginalXA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi =
      parityActualOriginalXAWithAllocationMass434 d L E x Psi band slot +
        parityActualOriginalXAAllocationDefect434 d L E x Psi band slot := by
  unfold sourceOriginalXA parityActualOriginalXAWithAllocationMass434
    parityActualOriginalXAAllocationDefect434
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hA := parity_actual_original_A_full_Q_buffered_allocation_defect434
    d L E hL u band slot
  have hEq : sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u =
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          parityActualOriginalAFullTupleAllocationMass434 d L E band slot f) +
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) := by
    linarith only [hA]
  rw [hEq]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualBufferedMassPositive -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Physical actual B590 allocation coefficients for every ordered
remaining Q assignment are nonnegative and at most one; the source
smoothTransition and exact compact B590 bump are used directly. -/
theorem parity_original_Q_actual_buffered_branch_between_zero_one434
    {n : ℕ} (r : ℕ) (E : ℝ)
    (s : Fin n → ℝ) (δ : Fin n → Bool) (p : Fin n → ℕ) :
    0 ≤ parityOriginalQAllocationBranchWeight434 r E s δ p ∧
    parityOriginalQAllocationBranchWeight434 r E s δ p ≤ 1 := by
  unfold parityOriginalQAllocationBranchWeight434
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    exact (source_buffered_gate_bounds r (δ i) _).1
  · apply Finset.prod_le_one₀
    · intro i hi
      exact (source_buffered_gate_bounds r (δ i) _).1
    · intro i hi
      exact (source_buffered_gate_bounds r (δ i) _).2

/-- The total B590 physical assignment mass in the real
`sourceOriginalXA` full Q-fibre is always nonnegative, even when the
original buffer creates leakage. This does not falsely assert mass=1. -/
theorem parity_actual_original_A_full_tuple_allocation_mass_nonneg434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    0 ≤ parityActualOriginalAFullTupleAllocationMass434 d L E band slot f := by
  unfold parityActualOriginalAFullTupleAllocationMass434
  apply Finset.sum_nonneg
  intro δ hδ
  exact (parity_original_Q_actual_buffered_branch_between_zero_one434
    20 E _ δ _).1


/-- In the literal source A the entire W1 times multiplicity-parity
factorial-labelled Q tuple weight is nonnegative. This is independent
of its true selected/skipped B590 Fourier decomposition. -/
theorem parity_actual_original_A_full_tuple_weight_nonneg434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    0 ≤ parityActualOriginalAFullTupleWeight434 d L u f := by
  unfold parityActualOriginalAFullTupleWeight434
  split_ifs
  · have hW := source_original_W1_nonneg
        (sourceOriginalPAllActualBands 20 L) u
    have hpar :
        0 ≤ ((1-(-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2) := by
      have hn : (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ≤ 1 := by
        have h := le_abs_self ((-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
        simpa using h
      exact div_nonneg (sub_nonneg.mpr hn) (by norm_num)
    have hfactor : 0 ≤
      (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) := by
      positivity
    exact mul_nonneg (mul_nonneg hfactor hW) hpar
  · exact le_refl _
end Green64Analytic.Parity

end

end

/-! ## OriginalBufferDecisionTree -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Decision tree of the ACTUAL original B590 f0/f1 buffered gates:
`t pref` is the exact logarithmic residual argument determined by
previously selected Q slots. Its specialization to the native ordered
Q scales and assigned prime tuple is the next source-mapping step. -/
def parityOriginalBufferedDecisionMass434 (r : ℕ) (t : List Bool → ℝ) :
    ℕ → List Bool → ℝ
  | 0, _ => 1
  | n+1, pref =>
      sourceBufferedGateReal r false (t pref) *
        parityOriginalBufferedDecisionMass434 r t n (pref ++ [false]) +
      sourceBufferedGateReal r true (t pref) *
        parityOriginalBufferedDecisionMass434 r t n (pref ++ [true])

/-- Each true B590 decision-tree mass is a subprobability measure,
because the f0+f1 sum is the compact buffer rho, not necessarily 1. -/
theorem parity_original_buffered_decision_mass_between_zero_one434
    (r : ℕ) (t : List Bool → ℝ) (n : ℕ) (pref : List Bool) :
    0 ≤ parityOriginalBufferedDecisionMass434 r t n pref ∧
    parityOriginalBufferedDecisionMass434 r t n pref ≤ 1 := by
  induction n generalizing pref with
  | zero => simp [parityOriginalBufferedDecisionMass434]
  | succ n ih =>
      have hF := source_buffered_gate_bounds r false (t pref)
      have hT := source_buffered_gate_bounds r true (t pref)
      have hR := (sourceAllocationBuffer r).le_one (x := t pref)
      have hL := ih (pref ++ [false])
      have hU := ih (pref ++ [true])
      constructor
      · simp only [parityOriginalBufferedDecisionMass434]
        exact add_nonneg (mul_nonneg hF.1 hL.1) (mul_nonneg hT.1 hU.1)
      · calc
          parityOriginalBufferedDecisionMass434 r t (n+1) pref ≤
              sourceBufferedGateReal r false (t pref) +
              sourceBufferedGateReal r true (t pref) := by
                simp only [parityOriginalBufferedDecisionMass434]
                exact add_le_add
                  (mul_le_of_le_one_right hF.1 hL.2)
                  (mul_le_of_le_one_right hT.1 hU.2)
          _ = sourceAllocationBuffer r (t pref) := source_buffered_gate_partition r (t pref)
          _ ≤ 1 := hR

/-- Exact local leakage identity: the missing mass consists of the
physical buffer cut at this pref plus losses propagated down both
true f0/f1 children. No distribution or asymptotic is assumed. -/
theorem parity_original_buffered_decision_loss_recursion434
    (r : ℕ) (t : List Bool → ℝ) (n : ℕ) (pref : List Bool) :
    1 - parityOriginalBufferedDecisionMass434 r t (n+1) pref =
      (1 - sourceAllocationBuffer r (t pref)) +
        sourceBufferedGateReal r false (t pref) *
          (1 - parityOriginalBufferedDecisionMass434 r t n (pref ++ [false])) +
        sourceBufferedGateReal r true (t pref) *
          (1 - parityOriginalBufferedDecisionMass434 r t n (pref ++ [true])) := by
  rw [← source_buffered_gate_partition r (t pref)]
  simp only [parityOriginalBufferedDecisionMass434]
  ring

/-- The source buffer loses no mass if every reachable pref residual
lies in the ORIGINAL B590 interior region |t| ≤ 4(r+1). This is a
proper conditional geometric criterion, not an assertion that all
original Q tuples satisfy the criterion. -/
theorem parity_original_buffered_decision_interior_mass_one434
    (r : ℕ) (t : List Bool → ℝ) (n : ℕ)
    (hInterior : ∀ pref : List Bool,
      |t pref| ≤ 4*(r+1 : ℝ)) (pref : List Bool) :
    parityOriginalBufferedDecisionMass434 r t n pref = 1 := by
  induction n generalizing pref with
  | zero => rfl
  | succ n ih =>
      simp only [parityOriginalBufferedDecisionMass434,
        ih (pref ++ [false]), ih (pref ++ [true]), mul_one]
      rw [source_buffered_gate_partition]
      have h := hInterior pref
      have hR : sourceAllocationBuffer r (t pref) = 1 := by
        apply (sourceAllocationBuffer r).one_of_mem_closedBall
        simpa [Metric.mem_closedBall, Real.dist_eq, sourceAllocationBuffer] using h
      exact hR

/-- Explicit quantitative B590 boundary-loss budget: if the true
compact buffer loses at most epsilon at EACH reachable decision node,
the full n-slot adaptive allocation has loss at most n*epsilon.
This works for path-dependent residuals, including repeated Q primes,
and makes clear which genuine source boundary estimate is still needed. -/
theorem parity_original_buffered_decision_uniform_loss_budget434
    (r : ℕ) (t : List Bool → ℝ) (epsilon : ℝ)
    (hEps : 0 ≤ epsilon)
    (hLoss : ∀ pref : List Bool,
      1-sourceAllocationBuffer r (t pref) ≤ epsilon)
    (n : ℕ) (pref : List Bool) :
    1-parityOriginalBufferedDecisionMass434 r t n pref ≤
      (n:ℝ)*epsilon := by
  induction n generalizing pref with
  | zero => simp [parityOriginalBufferedDecisionMass434]
  | succ n ih =>
      rw [parity_original_buffered_decision_loss_recursion434]
      have hF := source_buffered_gate_bounds r false (t pref)
      have hT := source_buffered_gate_bounds r true (t pref)
      have hN := ih (pref ++ [false])
      have hP := ih (pref ++ [true])
      have hR := (sourceAllocationBuffer r).le_one (x := t pref)
      have hSum := source_buffered_gate_partition r (t pref)
      have hTerm :
        sourceBufferedGateReal r false (t pref) *
            (1-parityOriginalBufferedDecisionMass434 r t n (pref ++ [false])) +
          sourceBufferedGateReal r true (t pref) *
            (1-parityOriginalBufferedDecisionMass434 r t n (pref ++ [true])) ≤
          ((n:ℝ)*epsilon) := by
        calc
          _ ≤ sourceBufferedGateReal r false (t pref) * ((n:ℝ)*epsilon) +
                sourceBufferedGateReal r true (t pref) * ((n:ℝ)*epsilon) :=
                  add_le_add (mul_le_mul_of_nonneg_left hN hF.1)
                    (mul_le_mul_of_nonneg_left hP hT.1)
          _ = sourceAllocationBuffer r (t pref) * ((n:ℝ)*epsilon) := by rw [← hSum]; ring
          _ ≤ ((n:ℝ)*epsilon) := mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hEps) hR
      calc
        _ = (1-sourceAllocationBuffer r (t pref)) +
              (sourceBufferedGateReal r false (t pref) *
                (1-parityOriginalBufferedDecisionMass434 r t n (pref ++ [false])) +
               sourceBufferedGateReal r true (t pref) *
                (1-parityOriginalBufferedDecisionMass434 r t n (pref ++ [true]))) := by ring
        _ ≤ epsilon + (n:ℝ)*epsilon := add_le_add (hLoss pref) hTerm
        _ = ((n+1:ℕ):ℝ)*epsilon := by push_cast; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590Eq44BufferInterior -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Numerical Parity §4.2 source Eq(4.4) interior: if the genuine remaining
Q-prime logarithm tail is <= 48 s_j, the residual budget is bounded by
that tail plus (c2+1)s_j = (11/5)s_j, and the true slot log p is within
[c1,c2]s_j=[1,6/5]s_j, then the original B590 20-slot compact
buffer radius 4(20+1)=84 covers the transition without loss.
The missing step is to prove these hypotheses uniformly for every
REACHABLE source prefix on the actual retained Q/P physical support. -/
theorem parity_original_eq44_rough_tail_implies_buffer_interior434
    (s R logp tail : ℝ) (hs : 0 < s)
    (hR0 : 0 ≤ R)
    (hEq44 : R ≤ tail + (11/5 : ℝ)*s)
    (hTail : tail ≤ 48*s)
    (hp0 : s ≤ logp)
    (hp1 : logp ≤ (6/5 : ℝ)*s) :
    |(R-logp)/s| ≤ 4*((20:ℕ)+1:ℝ) := by
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hs).2
    norm_num
    linarith
  · apply (div_le_iff₀ hs).2
    norm_num
    linarith

/-- The exact preselected B590 source f0+f1 partition is unity on the
numeric Parity Eq(4.4) physical interior. This is no longer an unknown
constant: r=20 and the genuine c1=1,c2=6/5 are retained. -/
theorem parity_original_eq44_rough_tail_buffer_partition_one434
    (s R logp tail : ℝ) (hs : 0 < s)
    (hR0 : 0 ≤ R)
    (hEq44 : R ≤ tail + (11/5 : ℝ)*s)
    (hTail : tail ≤ 48*s)
    (hp0 : s ≤ logp)
    (hp1 : logp ≤ (6/5 : ℝ)*s) :
    sourceBufferedGateReal 20 false ((R-logp)/s) +
      sourceBufferedGateReal 20 true ((R-logp)/s) = 1 := by
  rw [source_buffered_gate_partition]
  apply (sourceAllocationBuffer 20).one_of_mem_closedBall
  have h := parity_original_eq44_rough_tail_implies_buffer_interior434
    s R logp tail hs hR0 hEq44 hTail hp0 hp1
  rw [abs_div, abs_of_pos hs] at h
  have h2 : |R-logp| / |s| ≤ 4*((20:ℕ)+1:ℝ) := by
    simpa [abs_of_pos hs] using h
  simpa [Metric.mem_closedBall, Real.dist_eq, sourceAllocationBuffer] using h2
end Green64Analytic.Parity

end

end

/-! ## OriginalBufferReachableMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- True original B590 buffer-tree reachability: a prefix is reachable
only by following original strictly nonzero f0/f1 gates. This avoids the
false demand that every hypothetical zero-weight prefix lie inside the
source compact cutoff ζ. -/
inductive ParityOriginalBufferedReachable434 (r : ℕ) (t : List Bool → ℝ) :
    List Bool → Prop where
  | root : ParityOriginalBufferedReachable434 r t []
  | step (pref : List Bool) (b : Bool)
      (hReach : ParityOriginalBufferedReachable434 r t pref)
      (hGate : sourceBufferedGateReal r b (t pref) ≠ 0) :
      ParityOriginalBufferedReachable434 r t (pref ++ [b])

/-- The FULL original B590 adaptive f0/f1 tree is normalized on every
reachable original prefix whenever ζ=1 at those prefixes. Inaccessible
branches with zero gate weight contribute zero; no assertion about their
remaining Q residuals is required. This is the exact mathematical
bridge from the original source's *local* compact-support interior to
its *global* allocation mass=1. -/
theorem parity_original_buffered_reachable_tree_mass_one434
    (r : ℕ) (t : List Bool → ℝ)
    (hCut : ∀ pref, ParityOriginalBufferedReachable434 r t pref →
      sourceAllocationBuffer r (t pref) = 1)
    (n : ℕ) (pref : List Bool)
    (hReach : ParityOriginalBufferedReachable434 r t pref) :
    parityOriginalBufferedDecisionMass434 r t n pref = 1 := by
  induction n generalizing pref with
  | zero => rfl
  | succ n ih =>
      have hBranch (b : Bool) :
          sourceBufferedGateReal r b (t pref) *
            parityOriginalBufferedDecisionMass434 r t n (pref ++ [b]) =
          sourceBufferedGateReal r b (t pref) := by
        by_cases hGate : sourceBufferedGateReal r b (t pref) = 0
        · simp only [hGate, zero_mul]
        · rw [ih (pref ++ [b])
            (ParityOriginalBufferedReachable434.step pref b hReach hGate)]
          ring
      calc
        parityOriginalBufferedDecisionMass434 r t (n+1) pref =
          sourceBufferedGateReal r false (t pref) *
            parityOriginalBufferedDecisionMass434 r t n (pref ++ [false]) +
          sourceBufferedGateReal r true (t pref) *
            parityOriginalBufferedDecisionMass434 r t n (pref ++ [true]) := rfl
        _ = sourceBufferedGateReal r false (t pref) +
              sourceBufferedGateReal r true (t pref) := by
              rw [hBranch false, hBranch true]
        _ = sourceAllocationBuffer r (t pref) :=
          source_buffered_gate_partition r (t pref)
        _ = 1 := hCut pref hReach

/-- Exact zero leakage on all physically reachable B590 branches.
No E4.1 or Type II assumption; source-to-actual prefix mapping remains
an independently stated mathematical obligation. -/
theorem parity_original_buffered_reachable_tree_loss_zero434
    (r : ℕ) (t : List Bool → ℝ)
    (hCut : ∀ pref, ParityOriginalBufferedReachable434 r t pref →
      sourceAllocationBuffer r (t pref) = 1)
    (n : ℕ) :
    1-parityOriginalBufferedDecisionMass434 r t n [] = 0 := by
  rw [parity_original_buffered_reachable_tree_mass_one434 r t hCut n []
    (ParityOriginalBufferedReachable434.root)]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBufferFiniteBoolSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Original finite B590 decision-tree *leaf* weight for all Boolean
assignments of its remaining n Q-slots, using the ACTUAL local source
`sourceBufferedGateReal`; later transition arguments may depend on every
previous choice. No product normalization assumption. -/
def parityOriginalBufferedLeafWeight434
    (r : ℕ) (t : List Bool → ℝ) :
    (n : ℕ) → List Bool → (Fin n → Bool) → ℝ
  | 0, _, _ => 1
  | n+1, pref, δ =>
      sourceBufferedGateReal r (δ 0) (t pref) *
        parityOriginalBufferedLeafWeight434 r t n (pref ++ [δ 0]) (Fin.tail δ)

/-- EXACT native f0/f1 decision tree equals the literal sum over ALL
original finite Boolean labelled assignments. This finite combinatorial
fact includes variable residuals depending on earlier selections. -/
theorem parity_original_buffered_tree_eq_full_finite_bool_sum434
    (r : ℕ) (t : List Bool → ℝ) (n : ℕ) (pref : List Bool) :
    parityOriginalBufferedDecisionMass434 r t n pref =
      ∑ δ : Fin n → Bool,
        parityOriginalBufferedLeafWeight434 r t n pref δ := by
  induction n generalizing pref with
  | zero =>
      simp [parityOriginalBufferedDecisionMass434, parityOriginalBufferedLeafWeight434]
  | succ n ih =>
      have hReindex :
          (∑ δ : Fin (n+1) → Bool,
            parityOriginalBufferedLeafWeight434 r t (n+1) pref δ) =
          ∑ pair : Bool × (Fin n → Bool),
            sourceBufferedGateReal r pair.1 (t pref) *
            parityOriginalBufferedLeafWeight434 r t n (pref ++ [pair.1]) pair.2 := by
        apply Fintype.sum_equiv
          (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm
        intro δ
        simp [Fin.consEquiv_symm_apply, parityOriginalBufferedLeafWeight434]
      rw [hReindex, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [Fintype.sum_bool]
      rw [← ih (pref ++ [true]), ← ih (pref ++ [false])]
      simp only [parityOriginalBufferedDecisionMass434]
      ring

/-- Global all-delta allocation mass of the original finite B590
adaptive source tree is exactly one whenever source ζ=1 for every
NONZERO reachable prefix. No condition on discarded zero-weight
prefixes and no E4.1 analytic assumption. -/
theorem parity_original_full_finite_bool_sum_of_reachable_buffer_one434
    (r : ℕ) (t : List Bool → ℝ) (n : ℕ)
    (hCut : ∀ pref, ParityOriginalBufferedReachable434 r t pref →
      sourceAllocationBuffer r (t pref) = 1) :
    (∑ δ : Fin n → Bool,
      parityOriginalBufferedLeafWeight434 r t n [] δ) = 1 := by
  rw [← parity_original_buffered_tree_eq_full_finite_bool_sum434]
  exact parity_original_buffered_reachable_tree_mass_one434 r t hCut n []
    (ParityOriginalBufferedReachable434.root)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590LoggedCausalMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The exact SOURCE f0/f1 branch product in logarithmic-capacity
coordinates, with FULL earlier-δ dependence, not independent slot gates.
At R=log E and logp_i=log(original p_i) this is definitionally the
physical `parityOriginalQAllocationBranchWeight434`. -/
def parityOriginalB590LoggedCausalWeight434
    {n : ℕ} (r : ℕ) (R : ℝ) (s logp : Fin n → ℝ)
    (δ : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, sourceBufferedGateReal r (δ i)
    ((R - (∑ j : Fin n,
      if j < i then (if δ j then logp j else 0) else 0) - logp i) / s i)

/-- SOURCE-TRUE B590 smooth branch is the logged causal product for
exact real logs; all actual original sorted Q slot labels remain. -/
theorem parity_original_B590_actual_weight_eq_logged_causal434
    {n : ℕ} (r : ℕ) (E : ℝ) (s : Fin n → ℝ)
    (p : Fin n → ℕ) (δ : Fin n → Bool) :
    parityOriginalQAllocationBranchWeight434 r E s δ p =
      parityOriginalB590LoggedCausalWeight434 r (Real.log E) s
        (fun i => Real.log (p i : ℝ)) δ := by
  unfold parityOriginalB590LoggedCausalWeight434
    parityOriginalQAllocationBranchWeight434
    parityOriginalQAllocationResidual434
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  congr 1
  rw [Finset.sum_filter]


/-- At every original successive Q slot, taking one real B590 decision
updates exactly the residual log-capacity; the remaining Q sequence is
not reweighted or artificially decoupled. -/
theorem parity_original_B590_logged_causal_weight_cons434
    {n : ℕ} (r : ℕ) (R : ℝ) (s logp : Fin (n+1) → ℝ)
    (b : Bool) (rest : Fin n → Bool) :
    parityOriginalB590LoggedCausalWeight434 r R s logp (Fin.cons b rest) =
      sourceBufferedGateReal r b ((R-logp 0)/s 0) *
      parityOriginalB590LoggedCausalWeight434 r
        (R - if b then logp 0 else 0)
        (fun i => s i.succ) (fun i => logp i.succ) rest := by
  unfold parityOriginalB590LoggedCausalWeight434
  rw [Fin.prod_univ_succ]
  have hFirst : (∑ j : Fin (n+1),
      if j < (0 : Fin (n+1)) then
        (if ((Fin.cons b rest : Fin (n+1) → Bool) j) = true then logp j else 0) else 0) = 0 := by
    simp
  simp only [Fin.cons_zero, hFirst, sub_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hPrefix : (∑ j : Fin (n+1),
      if j < i.succ then
        (if ((Fin.cons b rest : Fin (n+1) → Bool) j) = true then logp j else 0) else 0) =
    (if b then logp 0 else 0) +
      (∑ j : Fin n, if j < i then (if rest j then logp j.succ else 0) else 0) := by
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  rw [hPrefix]
  simp only [Fin.cons_succ]
  congr 1
  ring


/-- Total original history-dependent Q-assignment mass, with no
independence assumption or omitted prime slot. -/
def parityOriginalB590LoggedCausalMass434
    {n : ℕ} (r : ℕ) (R : ℝ) (s logp : Fin n → ℝ) : ℝ :=
  ∑ δ : Fin n → Bool, parityOriginalB590LoggedCausalWeight434 r R s logp δ

/-- Exact first-slot marginalization of the WHOLE real causal B590
source assignment mass over all complete Boolean label assignments. -/
theorem parity_original_logged_B590_mass_cons434
    {n : ℕ} (r : ℕ) (R : ℝ) (s logp : Fin (n+1) → ℝ) :
    parityOriginalB590LoggedCausalMass434 r R s logp =
      sourceBufferedGateReal r false ((R-logp 0)/s 0) *
        parityOriginalB590LoggedCausalMass434 r R
          (fun i => s i.succ) (fun i => logp i.succ) +
      sourceBufferedGateReal r true ((R-logp 0)/s 0) *
        parityOriginalB590LoggedCausalMass434 r (R-logp 0)
          (fun i => s i.succ) (fun i => logp i.succ) := by
  unfold parityOriginalB590LoggedCausalMass434
  calc
    (∑ δ : Fin (n+1) → Bool,
      parityOriginalB590LoggedCausalWeight434 r R s logp δ) =
      ∑ pair : Bool × (Fin n → Bool),
        parityOriginalB590LoggedCausalWeight434 r R s logp
          (Fin.cons pair.1 pair.2) := by
          apply Fintype.sum_equiv
            (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm
          intro δ
          simp [Fin.consEquiv_symm_apply]
    _ = ∑ b : Bool, ∑ rest : Fin n → Bool,
          sourceBufferedGateReal r b ((R-logp 0)/s 0) *
            parityOriginalB590LoggedCausalWeight434 r
              (R - if b then logp 0 else 0)
              (fun i => s i.succ) (fun i => logp i.succ) rest := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro rest hrest
          exact parity_original_B590_logged_causal_weight_cons434 r R s logp b rest
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [Fintype.sum_bool]
      simp [parityOriginalB590LoggedCausalMass434]
      ring


/-- UNCONDITIONAL SOURCE Parity B590 f0/f1 mass subprobability for every
real logarithmic residual, prime-log tuple, scale tuple and number of
slots: sum over ALL original labelled assignments is between zero and
one even though later residuals depend on earlier f0/f1 choices.
The bound is *not* a fictitious product of independent masses. -/
theorem parity_original_logged_B590_mass_between_zero_one434
    (r n : ℕ) :
    ∀ (R : ℝ) (s logp : Fin n → ℝ),
      0 ≤ parityOriginalB590LoggedCausalMass434 r R s logp ∧
      parityOriginalB590LoggedCausalMass434 r R s logp ≤ 1 := by
  induction n with
  | zero =>
      intro R s logp
      simp [parityOriginalB590LoggedCausalMass434,
        parityOriginalB590LoggedCausalWeight434]
  | succ n ih =>
      intro R s logp
      have hFalse := ih R (fun i => s i.succ) (fun i => logp i.succ)
      have hTrue := ih (R-logp 0) (fun i => s i.succ) (fun i => logp i.succ)
      have hGateF := source_buffered_gate_bounds r false ((R-logp 0)/s 0)
      have hGateT := source_buffered_gate_bounds r true ((R-logp 0)/s 0)
      have hBuffer := (sourceAllocationBuffer r).le_one (x := ((R-logp 0)/s 0))
      rw [parity_original_logged_B590_mass_cons434]
      constructor
      · exact add_nonneg (mul_nonneg hGateF.1 hFalse.1)
          (mul_nonneg hGateT.1 hTrue.1)
      · calc
          _ ≤ sourceBufferedGateReal r false ((R-logp 0)/s 0) +
                sourceBufferedGateReal r true ((R-logp 0)/s 0) :=
                  add_le_add (mul_le_of_le_one_right hGateF.1 hFalse.2)
                    (mul_le_of_le_one_right hGateT.1 hTrue.2)
          _ = sourceAllocationBuffer r ((R-logp 0)/s 0) :=
            source_buffered_gate_partition r ((R-logp 0)/s 0)
          _ ≤ 1 := hBuffer

/-- Direct native source weight normalization: ORIGINAL
`parityOriginalQAllocationBranchWeight434` summed over every labelled
Bool assignment, with full earlier-choice history, is ALWAYS in [0,1].
No external constants, no positive branch or Q-cap assumptions. -/
theorem parity_original_actual_source_B590_total_mass_between_zero_one434
    {n : ℕ} (r : ℕ) (E : ℝ) (s : Fin n → ℝ) (p : Fin n → ℕ) :
    0 ≤ (∑ δ : Fin n → Bool,
      parityOriginalQAllocationBranchWeight434 r E s δ p) ∧
    (∑ δ : Fin n → Bool,
      parityOriginalQAllocationBranchWeight434 r E s δ p) ≤ 1 := by
  simp_rw [parity_original_B590_actual_weight_eq_logged_causal434]
  exact parity_original_logged_B590_mass_between_zero_one434 r n (Real.log E)
    s (fun i => Real.log (p i : ℝ))
end Green64Analytic.Parity

end

end

/-! ## OriginalActualAllocationSubprob -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- On EVERY actual full original r0=20 Q-prime tuple, with its
original reserved slot and sorted scales, the real genuine B590
branch-allocation mass is a SUBPROBABILITY between zero and one.
This proves the full all-δ upper bound with true previous-selection
coupling, rather than the invalid `2^N` bound from per-branch estimates. -/
theorem parity_actual_original_A_full_tuple_allocation_mass_le_one434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    0 ≤ parityActualOriginalAFullTupleAllocationMass434 d L E band slot f ∧
    parityActualOriginalAFullTupleAllocationMass434 d L E band slot f ≤ 1 := by
  unfold parityActualOriginalAFullTupleAllocationMass434
  exact parity_original_actual_source_B590_total_mass_between_zero_one434
    20 E (sourceActualSortedFrequencyScales 20 d L band slot)
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)

/-- The ACTUAL source buffer missing mass is always nonnegative, no
fictitious partition=1 even for unsupported boundary tuples. -/
theorem parity_actual_original_A_full_tuple_buffer_defect_nonneg434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    0 ≤ 1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f := by
  have h := parity_actual_original_A_full_tuple_allocation_mass_le_one434
    d L E band slot f
  linarith

/-- Exact absolute-value removal on the ACTUAL original f0/f1
allocation-mass defect; this is a proven sign, not a named condition. -/
theorem parity_actual_original_A_full_tuple_buffer_defect_abs_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    |1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f| =
      1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f :=
  abs_of_nonneg (parity_actual_original_A_full_tuple_buffer_defect_nonneg434
    d L E band slot f)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FiniteSuffix -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The original sorted Fin n f0/f1 tail is invariant under removal of
the first Q slot, with its true original label order retained. -/
theorem parity_original_Q_finite_ge_suffix_cons434
    {n : ℕ} (f : Fin (n+1) → ℝ) (i : Fin n) :
    (∑ j : Fin n, if i ≤ j then f j.succ else 0) =
    ∑ j : Fin (n+1), if i.succ ≤ j then f j else 0 := by
  rw [Fin.sum_univ_succ]
  simp

/-- The original strict suffix, needed for the f0 skip supply, also
commutes with Fin.cons Q-prime assignment and its dynamic scale. -/
theorem parity_original_Q_finite_gt_suffix_cons434
    {n : ℕ} (f : Fin (n+1) → ℝ) (i : Fin n) :
    (∑ j : Fin n, if i < j then f j.succ else 0) =
    ∑ j : Fin (n+1), if i.succ < j then f j else 0 := by
  rw [Fin.sum_univ_succ]
  simp

/-- Exact source remaining-after-first Q label sum. -/
theorem parity_original_Q_finite_after_first_exact434
    {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ j : Fin n, f j.succ) =
    ∑ j : Fin (n+1), if (0 : Fin (n+1)) < j then f j else 0 := by
  rw [Fin.sum_univ_succ]
  simp
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FiniteGeometricUnity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 33000

/-- Exact source-local Parity (4.4) geometry for an ORIGINAL ordered
finite Q-prime sequence and its true ported B590 f0/f1 scales.
The nontrivial geometry will be discharged using actual Q band support,
sourceSortedLabelEquiv and arbitrary-beta physical Q product mass. -/
def parityOriginalB590FiniteGeometry434 {n : ℕ}
    (B : ℝ) (s logp : Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    0 < s i ∧ s i ≤ logp i ∧ logp i ≤ (6/5:ℝ)*s i ∧
    B ≤ (11/5:ℝ)*s i ∧
    (∑ j : Fin n, if i ≤ j then logp j else 0) ≤ 48*s i ∧
    logp i+s i ≤ (∑ j : Fin n, if i < j then logp j else 0)+B

/-- Removing the first true Q slot preserves every geometric input
needed by the original B590 adaptive normalization. -/
theorem parity_original_B590_finite_geometry_tail434
    {n : ℕ} (B : ℝ) (s logp : Fin (n+1) → ℝ)
    (hGeom : parityOriginalB590FiniteGeometry434 B s logp) :
    parityOriginalB590FiniteGeometry434 B
      (fun i => s i.succ) (fun i => logp i.succ) := by
  intro i
  obtain ⟨hs, hlo, hhi, hb, htail, hsupply⟩ := hGeom i.succ
  refine ⟨hs,hlo,hhi,hb,?_,?_⟩
  · rw [parity_original_Q_finite_ge_suffix_cons434 logp i]
    exact htail
  · rw [parity_original_Q_finite_gt_suffix_cons434 logp i]
    exact hsupply

/-- The full ORIGINAL SOURCE B590 causal mass is exactly 1 on each
actual finite Q geometry when R starts between zero and the available
prime-log mass+B. Proof marginalizes genuine f0/f1 gates in their
original order, and uses f0/f1 support on every reachable branch;
zero-weight dead-end prefixes are never assumed to have an interior
argument. This is a TRUE normalizer, not a new branch weight. -/
theorem parity_original_B590_logged_mass_one_of_geometry434
    (n : ℕ) :
    ∀ (B R : ℝ) (s logp : Fin n → ℝ),
      0 ≤ B → parityOriginalB590FiniteGeometry434 B s logp →
      0 ≤ R → R ≤ (∑ i : Fin n, logp i)+B →
      parityOriginalB590LoggedCausalMass434 20 R s logp = 1 := by
  induction n with
  | zero =>
      intro B R s logp hB hGeom hR0 hRup
      simp [parityOriginalB590LoggedCausalMass434,
        parityOriginalB590LoggedCausalWeight434]
  | succ n ih =>
      intro B R s logp hB hGeom hR0 hRup
      obtain ⟨hs,hlo,hhi,hBS,hTail,hSupply⟩ := hGeom 0
      let f0 := sourceBufferedGateReal 20 false ((R-logp 0)/s 0)
      let f1 := sourceBufferedGateReal 20 true ((R-logp 0)/s 0)
      have hSum : (∑ i : Fin (n+1), logp i) =
          logp 0 + (∑ i : Fin n, logp i.succ) := Fin.sum_univ_succ logp
      have hFullTail : (∑ i : Fin (n+1), if (0 : Fin (n+1)) ≤ i then logp i else 0) =
          (∑ i : Fin (n+1), logp i) := by simp
      have hUpper : R ≤ (∑ i : Fin (n+1), logp i) + (11/5:ℝ)*s 0 := by
        linarith
      have hUnit : f0+f1=1 := by
        exact parity_original_eq44_rough_tail_buffer_partition_one434
          (s 0) R (logp 0) (∑ i : Fin (n+1), logp i)
          hs hR0 hUpper (by rw [←hFullTail]; exact hTail) hlo hhi
      have hNext := parity_original_B590_finite_geometry_tail434 B s logp hGeom
      have hAfter : ∑ i : Fin n, logp i.succ =
          ∑ i : Fin (n+1), if (0:Fin (n+1)) < i then logp i else 0 :=
        parity_original_Q_finite_after_first_exact434 logp
      have hFalse : f0 * parityOriginalB590LoggedCausalMass434 20 R
          (fun i => s i.succ) (fun i => logp i.succ) = f0 := by
        by_cases hz : f0=0
        · simp [hz]
        · have hSkip := parity_original_B590_one_nonzero_f0_skip_budget434
            20 R (logp 0) (s 0) hs hz
          have hChildUp : R ≤ (∑ i : Fin n, logp i.succ)+B := by
            rw [hAfter]
            linarith
          rw [ih B R (fun i => s i.succ) (fun i => logp i.succ)
            hB hNext hR0 hChildUp]
          ring
      have hTrue : f1 * parityOriginalB590LoggedCausalMass434 20 (R-logp 0)
          (fun i => s i.succ) (fun i => logp i.succ) = f1 := by
        by_cases hz : f1=0
        · simp [hz]
        · have hSelect := parity_original_B590_one_nonzero_f1_selected_budget434
            20 R (logp 0) (s 0) hs hz
          have hChild0 : 0 ≤ R-logp 0 := by linarith
          have hChildUp : R-logp 0 ≤ (∑ i : Fin n, logp i.succ)+B := by
            rw [hSum] at hRup
            linarith
          rw [ih B (R-logp 0) (fun i => s i.succ) (fun i => logp i.succ)
            hB hNext hChild0 hChildUp]
          ring
      rw [parity_original_logged_B590_mass_cons434]
      change f0 * parityOriginalB590LoggedCausalMass434 20 R
          (fun i => s i.succ) (fun i => logp i.succ) +
        f1 * parityOriginalB590LoggedCausalMass434 20 (R-logp 0)
          (fun i => s i.succ) (fun i => logp i.succ) = 1
      rw [hFalse,hTrue]
      exact hUnit
end Green64Analytic.Parity

end

end

/-! ## OriginalQActualDyadicTail48_ -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact uniform tail `20*(6/5)*2 = 48` for the original Parity
20 slots/band, original dyadic exponent `(5/(11*20))*L*2^-j`.
No asymptotic O-constant and no abstract Q support replacement. -/
theorem parity_original_Q_actual_dyadic_slot_tail_48_434
    (j n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (slotLog : ℕ → Fin 20 → ℝ)
    (hSlot : ∀ k ∈ Finset.Ico j n, ∀ i : Fin 20,
      slotLog k i ≤ (6/5:ℝ)*(5/(11*(20:ℝ)))*L*(1/2:ℝ)^k) :
    (∑ k ∈ Finset.Ico j n, ∑ i : Fin 20, slotLog k i) ≤
      48*((5/(11*(20:ℝ)))*L*(1/2:ℝ)^j) := by
  have hPer (k : ℕ) (hk : k ∈ Finset.Ico j n) :
      (∑ i : Fin 20, slotLog k i) ≤
      (20:ℝ)*((6/5:ℝ)*(5/(11*(20:ℝ)))*L*(1/2:ℝ)^k) := by
    calc
      _ ≤ ∑ _i : Fin 20, (6/5:ℝ)*(5/(11*(20:ℝ)))*L*(1/2:ℝ)^k := by
        apply Finset.sum_le_sum
        intro i hi
        exact hSlot k hk i
      _ = _ := by simp [mul_comm]
  have hFinite : (∑ k ∈ Finset.Ico j n, ∑ i : Fin 20, slotLog k i) ≤
      ((20:ℝ)*(6/5:ℝ)*(5/(11*(20:ℝ)))*L) *
      (∑ k ∈ Finset.Ico j n, (1/2:ℝ)^k) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico j n,
          (20:ℝ)*((6/5:ℝ)*(5/(11*(20:ℝ)))*L*(1/2:ℝ)^k) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hPer k hk
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hGeom : (∑ k ∈ Finset.Ico j n, (1/2:ℝ)^k) ≤
      2*(1/2:ℝ)^j := by
    have hg := geom_sum_Ico_le_of_lt_one (x := (1/2:ℝ))
      (m := j) (n := n) (by norm_num) (by norm_num)
    convert hg using 1 <;> norm_num [div_eq_mul_inv] <;> ring
  have hCoef : 0 ≤ (20:ℝ)*(6/5:ℝ)*(5/(11*(20:ℝ)))*L := by positivity
  calc
    _ ≤ ((20:ℝ)*(6/5:ℝ)*(5/(11*(20:ℝ)))*L) *
      (∑ k ∈ Finset.Ico j n, (1/2:ℝ)^k) := hFinite
    _ ≤ ((20:ℝ)*(6/5:ℝ)*(5/(11*(20:ℝ)))*L) *
      (2*(1/2:ℝ)^j) := mul_le_mul_of_nonneg_left hGeom hCoef
    _ = _ := by ring


/-- EXACT original Q-band tuple specialization of the uniform 48*s_j
log-tail estimate, not an assumed bound on a hypothetical prime array.
For every real physical original all-labelled Q tuple, every band j and
all subsequent bands, the actual logarithmic prime mass is bounded.
The original sorted-slot prefix mapping to Eq(4.4) remains separate. -/
theorem parity_actual_original_Q_full_labelled_remaining_log_tail_48_434
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : (k : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L k})
    (j : Fin (d+1)) :
    (∑ k ∈ Finset.Ico j.val (d+1), ∑ i : Fin 20,
      if hk : k < d+1 then
        Real.log (((f ⟨k,hk⟩ i).val:ℕ):ℝ) else 0) ≤
      48*((5/(11*(20:ℝ)))*L*(1/2:ℝ)^j.val) := by
  apply parity_original_Q_actual_dyadic_slot_tail_48_434 j.val (d+1) L hL
    (fun k i => if hk : k < d+1 then
      Real.log (((f ⟨k,hk⟩ i).val:ℕ):ℝ) else 0)
  intro k hk i
  have hkHi : k < d+1 := (Finset.mem_Ico.mp hk).2
  simp only [dif_pos hkHi]
  have hp : (f ⟨k,hkHi⟩ i).val ∈ sourceClosedPrimeLogBand L
      (sourceOriginalQActualExponent 20 k)
      ((6/5:ℝ)*sourceOriginalQActualExponent 20 k) :=
    (f ⟨k,hkHi⟩ i).property
  have hUp := (source_original_Q_closed_prime_log_bounds L
    (sourceOriginalQActualExponent 20 k)
    ((6/5:ℝ)*sourceOriginalQActualExponent 20 k)
    (f ⟨k,hkHi⟩ i).val hp).2
  have hScale : sourceOriginalQActualExponent 20 k =
      (5/(11*(20:ℝ)))*(1/2:ℝ)^k := by
    unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  calc
    Real.log ((f ⟨k,hkHi⟩ i).val:ℝ) ≤
        (6/5:ℝ)*sourceOriginalQActualExponent 20 k*L := hUp
    _ = _ := by rw [hScale]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualSortedSuffix48_ -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 35000

/-- The full original sorted source Q suffix is bounded by the original
20-labelled band Q tail from its genuine full Q tuple, including the
single original reserved slot and repeated prime choices. -/
theorem parity_original_actual_sorted_Q_suffix_le_full_band_tail434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (k : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L k})
    (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) :
    (∑ z ∈ (Finset.univ.filter (fun z : Fin
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length => i ≤ z)),
      Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f z).val : ℝ)) ≤
    ∑ k ∈ ((Finset.univ : Finset (Fin (d+1))).filter (fun k =>
      (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot i).val.1 ≤ k)),
      ∑ j : Fin 20, Real.log ((f k j).val:ℝ) := by
  classical
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot i).val.1
  let T : Finset (Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length) := Finset.univ.filter (fun z => i ≤ z)
  let S : Finset (Fin (d+1) × Fin 20) :=
    Finset.univ.filter (fun z => b ≤ z.1)
  let eqv := sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot
  let label : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length → Fin (d+1) × Fin 20 := fun z => (eqv z).val
  have hInject : Function.Injective label := fun z w he =>
    eqv.injective (Subtype.ext he)
  have hSubset : T.image label ⊆ S := by
    intro z hz
    obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hz
    rw [←heq]
    have hji : i ≤ j := (Finset.mem_filter.mp hj).2
    have hBand : b ≤ (label j).1 := by
      by_cases heq : i=j
      · subst j
        exact le_refl _
      · exact parity_actual_Q_ordered_band_nondecreasing434
          d L hL band slot i j (lt_of_le_of_ne hji heq)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBand⟩
  have hQNonneg : ∀ z ∈ S, 0 ≤ Real.log ((f z.1 z.2).val : ℝ) := by
    intro z hz
    have hp := source_original_Q_actual_prime 20 d L z.1
      (f z.1 z.2).val (f z.1 z.2).property
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hImage :
      (∑ z ∈ T, Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f z).val : ℝ)) =
      ∑ z ∈ T.image label, Real.log ((f z.1 z.2).val : ℝ) := by
    rw [Finset.sum_image (s := T) (g := label) (f := fun z =>
      Real.log ((f z.1 z.2).val : ℝ)) (fun x hx y hy h => hInject h)]
    rfl
  have hLe : (∑ z ∈ T.image label, Real.log ((f z.1 z.2).val : ℝ)) ≤
      ∑ z ∈ S, Real.log ((f z.1 z.2).val : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (by intro z hz hnot; exact hQNonneg z hz)
  have hS : (∑ z ∈ S, Real.log ((f z.1 z.2).val : ℝ)) =
      ∑ k ∈ ((Finset.univ : Finset (Fin (d+1))).filter (fun k => b ≤ k)),
        ∑ j : Fin 20, Real.log ((f k j).val : ℝ) := by
    unfold S
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : b ≤ k
    · simp only [h, if_pos]
    · simp only [h, ite_false, Finset.sum_const_zero]
  change (∑ z ∈ T, Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f z).val : ℝ)) ≤ _
  calc
    _ = ∑ z ∈ T.image label, Real.log ((f z.1 z.2).val : ℝ) := hImage
    _ ≤ ∑ z ∈ S, Real.log ((f z.1 z.2).val : ℝ) := hLe
    _ = _ := hS


/-- The ACTUAL original sorted Q tail is uniformly bounded by the
sharp original `48*s_{band(i)}` on each finite physical Q tuple. -/
theorem parity_original_actual_sorted_Q_suffix_le_48_scale434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (k : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L k})
    (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) :
    (∑ z ∈ (Finset.univ.filter (fun z : Fin
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length => i ≤ z)),
      Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f z).val : ℝ)) ≤
    48*sourceActualSortedFrequencyScales 20 d L band slot i := by
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
    band slot i).val.1
  have hBase := parity_original_actual_sorted_Q_suffix_le_full_band_tail434
    d L hL band slot f i
  have hBandEq :
      (∑ k ∈ ((Finset.univ : Finset (Fin (d+1))).filter (fun k => b ≤ k)),
        ∑ j : Fin 20, Real.log ((f k j).val : ℝ)) =
      ∑ k ∈ Finset.Ico b.val (d+1),
        ∑ j : Fin 20, if hk : k < d+1 then
          Real.log ((f ⟨k,hk⟩ j).val : ℝ) else 0 := by
    classical
    apply Finset.sum_bij (fun k hk => k.val)
    · intro k hk
      have h := (Finset.mem_filter.mp hk).2
      exact Finset.mem_Ico.mpr ⟨h, k.isLt⟩
    · intro k hk l hl heq
      exact Fin.ext heq
    · intro k hk
      have hn : k < d+1 := (Finset.mem_Ico.mp hk).2
      let j : Fin (d+1) := ⟨k,hn⟩
      refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_Ico.mp hk).1⟩,?_⟩
      rfl
    · intro k hk
      have hkPos : k.val < d+1 := k.isLt
      apply Finset.sum_congr rfl
      intro j hj
      simp only [dif_pos hkPos]
  have hOriginal := parity_actual_original_Q_full_labelled_remaining_log_tail_48_434
    d L (le_of_lt hL) f b
  have hScale : sourceActualSortedFrequencyScales 20 d L band slot i =
      (5/(11*(20:ℝ)))*L*(1/2:ℝ)^b.val := by
    change sourceOriginalPGroupScale 20 L b.val = _
    unfold sourceOriginalPGroupScale
    have hpow : (2:ℝ)^b.val ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hpow]
    have hunit : (2:ℝ)^b.val * (1/2:ℝ)^b.val = 1 := by
      rw [←mul_pow]; norm_num
    calc
      (20:ℝ) = (20:ℝ)*((2:ℝ)^b.val*(1/2:ℝ)^b.val) := by rw [hunit]; ring
      _ = _ := by ring
  rw [hBandEq] at hBase
  rw [hScale]
  exact hBase.trans hOriginal
end Green64Analytic.Parity

end

end

/-! ## OriginalActualFiniteGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000

/-- ALL exact SOURCE geometry for Parity's original r0=20 sorted Q tuple,
including its actual reserved Q slot and the sourceOriginalPGroupScale
last-band terminal slack B=(11/5)*s_last. Unlike previous individual
positive-branch lemmas, this geometry holds for EVERY actual labelled
Q tuple, BEFORE choosing any f0/f1 branch, so it supports the true
all-δ assignment mass normalization. -/
theorem parity_original_actual_fullQ_finite_B590_geometry434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    let p := parityActualSourceRemainingFullQTuple434 d L band slot f
    parityOriginalB590FiniteGeometry434
      ((11/5:ℝ)*sourceOriginalPGroupScale 20 L d)
      (sourceActualSortedFrequencyScales 20 d L band slot)
      (fun i => Real.log ((p i).val : ℝ)) := by
  dsimp only
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  have hS : ∀ i, 0 < s i :=
    parity_actual_sorted_Q_allocation_scales_positive434 d L hL band slot
  intro i
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
    band slot i).val.1
  have hp : (p i).val ∈ sourceOriginalQActualBands 20 d L b := (p i).property
  have hPrime := source_original_Q_closed_prime_log_bounds L
    (sourceOriginalQActualExponent 20 b.val)
    ((6/5:ℝ)*sourceOriginalQActualExponent 20 b.val) (p i).val hp
  have hScale : sourceOriginalQActualExponent 20 b.val * L = s i := by
    change sourceOriginalQActualExponent 20 b.val * L =
      sourceOriginalPGroupScale 20 L b.val
    exact source_original_Q_actual_scale_eq_P_scale 20 b.val L (by norm_num)
  have hlo : s i ≤ Real.log ((p i).val:ℝ) := by
    rw [←hScale]
    exact hPrime.1
  have hhi : Real.log ((p i).val:ℝ) ≤ (6/5:ℝ)*s i := by
    rw [←hScale]
    simpa only [mul_assoc] using hPrime.2
  have hB : (11/5:ℝ)*sourceOriginalPGroupScale 20 L d ≤
      (11/5:ℝ)*s i := by
    let last : Fin (d+1) := ⟨d,by omega⟩
    have hb : b ≤ last := by change b.val ≤ d; omega
    have hbScale : sourceOriginalPGroupScale 20 L d ≤ s i := by
      by_cases heq : b=last
      · change sourceActualSortedScales 20 d L last ≤
          sourceActualSortedScales 20 d L b
        rw [heq]
      · have hlt : b < last := lt_of_le_of_ne hb heq
        exact le_of_lt (parity_actual_Q_scale_strict_antitone434 d L hL b last hlt)
    exact mul_le_mul_of_nonneg_left hbScale (by norm_num)
  have hTail := parity_original_actual_sorted_Q_suffix_le_48_scale434
    d L hL band slot f i
  have hSupply := parity_original_actual_Q_suffix_capacity_eq44_434
    d L hL band slot p i
  refine ⟨hS i,hlo,hhi,hB,?_,?_⟩
  · rw [Finset.sum_filter] at hTail
    exact hTail
  · rw [Finset.sum_filter] at hSupply
    exact hSupply
end Green64Analytic.Parity

end

end

/-! ## OriginalActualAllocationMassOne -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- Full ORIGINAL source Parity §4.2 B590 f0/f1 mass normalization:
for EVERY genuine 20!-labelled original Q-prime assignment with the
real reserved Q slot, if the physical nonreserved Q product contains
the true capacity 1<=E<=prod remaining Q, then the sum of ALL B590
history-dependent f0/f1 smooth branch weights is **EXACTLY ONE**.
No full-branch nonzero assumption, no hypothetical prefix gate,
no replacement of original factorial, no external E4.1 estimate.
The original Q-band geometry and reachable-prefix normalization are
kernel-proved in real source variables. -/
theorem parity_original_actual_fullQ_B590_all_assignments_mass_one434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hFull : E ≤ ((∏ i,
      (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ)) :
    parityActualOriginalAFullTupleAllocationMass434 d L E band slot f = 1 := by
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let B : ℝ := (11/5:ℝ)*sourceOriginalPGroupScale 20 L d
  have hGeo : parityOriginalB590FiniteGeometry434 B s
      (fun i => Real.log ((p i).val : ℝ)) :=
    parity_original_actual_fullQ_finite_B590_geometry434 d L hL band slot f
  have hB : 0 ≤ B := by
    exact mul_nonneg (by norm_num) (le_of_lt
      (source_original_positive_dyadic_scale 20 d L (by norm_num) hL))
  have hpPos : ∀ i, 0 < (p i).val := by
    intro i
    let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1
    exact (source_original_Q_actual_prime 20 d L b (p i).val (p i).property).pos
  have hLogProd : Real.log ((∏ i, (p i).val : ℕ) : ℝ) =
      ∑ i, Real.log ((p i).val : ℝ) := by
    rw [Nat.cast_prod,Real.log_prod]
    intro i hi
    exact_mod_cast (Nat.ne_of_gt (hpPos i))
  have hEPos : 0 < E := by linarith
  have hLogCap : Real.log E ≤ ∑ i, Real.log ((p i).val : ℝ) := by
    rw [←hLogProd]
    exact Real.log_le_log hEPos hFull
  have hRoot : Real.log E ≤ (∑ i, Real.log ((p i).val : ℝ)) + B := by
    linarith
  have hMass := parity_original_B590_logged_mass_one_of_geometry434
    (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
    B (Real.log E) s (fun i => Real.log ((p i).val : ℝ))
    hB hGeo (Real.log_nonneg hE) hRoot
  have hSame : parityActualOriginalAFullTupleAllocationMass434 d L E band slot f =
      parityOriginalB590LoggedCausalMass434 20 (Real.log E) s
        (fun i => Real.log ((p i).val : ℝ)) := by
    unfold parityActualOriginalAFullTupleAllocationMass434
      parityOriginalB590LoggedCausalMass434
    apply Finset.sum_congr rfl
    intro δ hδ
    exact parity_original_B590_actual_weight_eq_logged_causal434 20 E s
      (fun i => (p i).val) δ
  exact hSame.trans hMass
end Green64Analytic.Parity

end

end

/-! ## OriginalXAAllocationDefectBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- The genuine historic XA buffered allocation discrepancy is bounded
by the EXACT absolute original tuple weights and their exact mass defects.
No support-discard, cutoff saving, or assumed abstract partition of unity.
This is the lossless absolute-value inequality needed before plugging in
a mathematical estimate for the buffer-boundary tuples. -/
theorem parity_actual_original_XA_buffer_allocation_absolute_majorant434
    (d : ℕ) (L E x : ℝ)
    (Psi : ℝ → ℝ) (band : Fin (d+1)) (slot : Fin 20) :
    |parityActualOriginalXAAllocationDefect434 d L E x Psi band slot| ≤
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          |parityActualOriginalAFullTupleWeight434 d L u f| *
            |1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f|) *
          |Psi ((u:ℝ)/x)| := by
  unfold parityActualOriginalXAAllocationDefect434
  calc
    |∑ u ∈ Finset.range (⌊2*x⌋₊+1),
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
        (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) *
      Psi ((u:ℝ)/x)| ≤
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        |(∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalAFullTupleWeight434 d L u f *
            (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) *
            Psi ((u:ℝ)/x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc
        |∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalAFullTupleWeight434 d L u f *
            (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)| ≤
          ∑ f : ((j : Fin (d+1)) → Fin 20 →
            {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
            |parityActualOriginalAFullTupleWeight434 d L u f *
              (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)| :=
                Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalAAllocatedV -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- On EVERY contributing tuple of the actual full original source A,
separating one reserved Q prime and applying the literal B590 allocation
to all remaining labelled Q primes gives the PHYSICAL equality u = e*v.
The v factor contains exactly the reserved Q prime, every original
unselected OrderedQSkip prime and the full multiplicity-counted P part.
No Fourier approximation, source replacement or smooth error is assumed. -/
theorem parity_actual_original_A_labelled_allocated_ev_exact434
    (d : ℕ) (L : ℝ) (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool) :
    let P := sourceOriginalPAllActualBands 20 L
    let p := parityActualSourceRemainingFullQTuple434 d L band slot f
    let e := paritySourceOrderedAllocatedE434 δ p
    let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
      sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    e*v = u := by
  dsimp only
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let P := sourceOriginalPAllActualBands 20 L
  have hp : paritySourceOrderedAllocatedE434 δ p *
      paritySourceOrderedAllocatedV434 δ p = ∏ i, (p i).val :=
    parity_source_ordered_allocation_partition434 δ p
  have hq := parity_actual_source_fullQ_split_reserved_sorted_exact434
    d L band slot f
  calc
    paritySourceOrderedAllocatedE434 δ p *
        ((f band slot).val * paritySourceOrderedAllocatedV434 δ p *
          sourceOriginalPPrimePart (Finset.univ.biUnion P) u) =
      ((f band slot).val *
        (paritySourceOrderedAllocatedE434 δ p * paritySourceOrderedAllocatedV434 δ p)) *
        sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by ac_rfl
    _ = ((f band slot).val * (∏ i, (p i).val)) *
        sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hp]
    _ = (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) *
        sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hq]
    _ = sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u *
        sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hf]
    _ = u := source_original_ordinary_times_P_part _ u hu

/-- At each actual complete original A source tuple and EVERY B590
assignment, the real P-group weight, multiplicity parity and the exact
ε-sign transfer to the original v (= reserved Q prime × skipped Q × P).
This is the PHYSICAL, not an abstract-fibre, form of Parity (4.7),(4.9). -/
theorem parity_actual_original_A_labelled_P_factor_transfer434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L) (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool) :
    let P := sourceOriginalPAllActualBands 20 L
    let p := parityActualSourceRemainingFullQTuple434 d L band slot f
    let e := paritySourceOrderedAllocatedE434 δ p
    let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
      sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    e*v = u ∧ v ≠ 0 ∧
      sourceOriginalW1 P u = sourceOriginalW1 P v ∧
      sourceOriginalPParityExponent (Finset.univ.biUnion P) u =
        sourceOriginalPParityExponent (Finset.univ.biUnion P) v ∧
      ∀ tw : Bool, groupSign P tw u = groupSign P tw v := by
  subst d
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let p := parityActualSourceRemainingFullQTuple434 (sourceOriginalLiteralDepth 20 L) L band slot f
  let e := paritySourceOrderedAllocatedE434 δ p
  let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
    sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  have hev : e*v = u :=
    parity_actual_original_A_labelled_allocated_ev_exact434 (sourceOriginalLiteralDepth 20 L) L u hu f hf band slot δ
  have hv : v ≠ 0 := by
    intro hv0
    apply hu
    rw [←hev,hv0,mul_zero]
  have hP := parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hL band slot δ p v hv
  dsimp only at hP
  refine ⟨hev,hv,?_,?_,?_⟩
  · exact (congrArg (sourceOriginalW1 P) hev).symm.trans hP.1
  · exact (congrArg
      (sourceOriginalPParityExponent (Finset.univ.biUnion P)) hev).symm.trans hP.2.1
  · intro tw
    exact (congrArg (groupSign P tw) hev).symm.trans (hP.2.2 tw)

/-- The *complete* original source weight W1 times the signed parity
projector is unchanged when its actual Q allocation is transferred to
v. In particular a_e never silently absorbs any P-group parity factor. -/
theorem parity_actual_original_A_labelled_W1_projector_transfer434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L) (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool) :
    let P := sourceOriginalPAllActualBands 20 L
    let p := parityActualSourceRemainingFullQTuple434 d L band slot f
    let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
      sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    sourceOriginalW1 P u *
       ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u)/2) =
    sourceOriginalW1 P v *
       ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) v)/2) := by
  dsimp only
  have h := parity_actual_original_A_labelled_P_factor_transfer434
    d L hL hd u hu f hf band slot δ
  dsimp only at h
  rw [h.2.2.1,h.2.2.2.1]
end Green64Analytic.Parity

end

end

/-! ## OriginalAFullLabelledSmoothFourier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- Complete source ORIGINAL Q-labelled tuple, with every factorial
orbit repetition, and a Boolean assignment to e of every nonreserved
slot. The reserved labelled prime itself remains outside the Boolean
domain, exactly as in Parity §4.1–§4.2. -/
abbrev parityActualOriginalAFullBranchCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20) : Type :=
  ((Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length → Bool) ×
   ((j : Fin (d+1)) → Fin 20 →
     {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}))

/-- Literal original e product of a FULL labelled Q-tuple and B590
assignment: use native sourceSortedLabelEquiv, not a synthetic prime list. -/
def parityActualOriginalAFullBranchE434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (x : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℕ :=
  paritySourceOrderedAllocatedE434 x.1
    (parityActualSourceRemainingFullQTuple434 d L band slot x.2)

/-- The complete original A source term AFTER inserting the genuine
B590 smooth gate and complete B509 Fourier phase, including the actual
ALL-Q product indicator, original (20!)^(-d-1), original W1 and signed
multiplicity P-parity. This is the smoothed *descendant* of sourceOriginalA;
no unsupported equality with unsmoothed sourceOriginalA is asserted. -/
def parityActualOriginalAFullBranchWeight434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (x : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let p := parityActualSourceRemainingFullQTuple434 d L band slot x.2
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  if (∏ j : Fin (d+1), ∏ i : Fin 20, (x.2 j i).val) =
     sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u then
    (((∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
       (sourceOriginalW1 P u *
         ((1-(-1:ℝ)^sourceOriginalPParityExponent
           (Finset.univ.biUnion P) u)/2)) : ℝ) : ℂ) *
      ((parityOriginalQAllocationBranchWeight434 20 E s x.1
        (fun i => (p i).val) : ℂ) *
        paritySourceFullSlotFourierPhase434 s ξ x.1 p)
  else 0

/-- Same COMPLETE physical source term, with full original P-mark weight
and parity transferred to v=reserved Q * OrderedQSkip * Ppart, and the
FULL B509 Fourier phase split between selected e and skipped residual.
Only the representation changes: no extra character/phase/weight. -/
def parityActualOriginalAFullBranchVWeight434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (x : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let p := parityActualSourceRemainingFullQTuple434 d L band slot x.2
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let v := (x.2 band slot).val * paritySourceOrderedAllocatedV434 x.1 p *
    sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  if (∏ j : Fin (d+1), ∏ i : Fin 20, (x.2 j i).val) =
     sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u then
    (((∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
       (sourceOriginalW1 P v *
         ((1-(-1:ℝ)^sourceOriginalPParityExponent
           (Finset.univ.biUnion P) v)/2)) : ℝ) : ℂ) *
      ((parityOriginalQAllocationBranchWeight434 20 E s x.1
        (fun i => (p i).val) : ℂ) *
        (paritySourceAllocatedSlotFourierPhase434 s ξ x.1 p *
          orderedSkipPhase (δ := x.1) s ξ
            (fun i : {i : Fin _ // ¬x.1 i = true} => p i.val)))
  else 0

/-- Exact ORIGINAL A-labelled B590/B509 pointwise source transfer.
The complete all-band 20! normalization, real B590 f0/f1 gate and
source product indicator are unchanged. The proof uses real u=e*v,
original W1/P parity, and original full selected/skipped Fourier identity. -/
theorem parity_actual_original_A_full_branch_source_to_v_exact434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (E : ℝ) (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (x : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    parityActualOriginalAFullBranchWeight434 d L E u band slot ξ x =
      parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ x := by
  unfold parityActualOriginalAFullBranchWeight434
    parityActualOriginalAFullBranchVWeight434
  dsimp only
  by_cases hGate : (∏ j : Fin (d+1), ∏ i : Fin 20, (x.2 j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hGate]
    have hP := parity_actual_original_A_labelled_W1_projector_transfer434
      d L hL hd u hu x.2 hGate band slot x.1
    dsimp only at hP
    have hFourier := parity_source_full_slot_fourier_phase_split434
      (sourceActualSortedFrequencyScales 20 d L band slot) ξ x.1
      (parityActualSourceRemainingFullQTuple434 d L band slot x.2)
    rw [hP,hFourier]
  · simp only [if_neg hGate]

/-- The genuine smoothed full original source sum has an EXACT e-fibre
regrouping. Every labelled Q tuple, its true B590 gate, full B509
Fourier phase, original factorial and P projector remain in the fibre;
no all-alpha E4.1 saving, factorial orbit truncation or tail is assumed. -/
theorem parity_actual_original_A_full_branch_e_fibre_reindex434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ x : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot ξ x) =
    ∑ e ∈ ((Finset.univ : Finset
      (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
        (parityActualOriginalAFullBranchE434 d L band slot)),
      sourceEndpointFibre
        (Finset.univ : Finset
          (parityActualOriginalAFullBranchCarrier434 d L band slot))
        (parityActualOriginalAFullBranchE434 d L band slot)
        (parityActualOriginalAFullBranchWeight434 d L E u band slot ξ) e := by
  let S : Finset (parityActualOriginalAFullBranchCarrier434 d L band slot) :=
    Finset.univ
  let g := parityActualOriginalAFullBranchE434 d L band slot
  let w := parityActualOriginalAFullBranchWeight434 d L E u band slot ξ
  have h := Finset.sum_image' (s := S) (g := g)
    (f := fun e => sourceEndpointFibre S g w e) w (by intro x hx; rfl)
  simpa only [S,g,w,sourceEndpointFibre] using h.symm

/-- Full PHYSICAL ORIGINAL A source reduction after the B590 smooth
branch and B509 Fourier split: an exact finite sum over allocated e,
with original reserved prime and P-group W1/parity all left in v.
This is still before Parity (4.7) Fourier integration, H decomposition and
absolute tail bound; no unsmoothed A equality or Type II claim. -/
theorem parity_actual_original_A_full_source_to_e_v_sum434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (E : ℝ) (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ x : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot ξ x) =
    ∑ e ∈ ((Finset.univ : Finset
      (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
        (parityActualOriginalAFullBranchE434 d L band slot)),
      sourceEndpointFibre
        (Finset.univ : Finset
          (parityActualOriginalAFullBranchCarrier434 d L band slot))
        (parityActualOriginalAFullBranchE434 d L band slot)
        (parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ) e := by
  rw [parity_actual_original_A_full_branch_e_fibre_reindex434]
  apply Finset.sum_congr rfl
  intro e he
  unfold sourceEndpointFibre
  apply Finset.sum_congr rfl
  intro x hx
  exact parity_actual_original_A_full_branch_source_to_v_exact434
    d L hL hd E u hu band slot ξ x
end Green64Analytic.Parity

end

end

