module

public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part069
public import Green64.Library.Weights.Part067
public import Green64.Library.Weights.Part072
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part016
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part020
public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Green64.Library.Weights.Part071
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

/-!
# Weights / Part075

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSignedCleanWavefront -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Genuine ONE-STEP reachability of a finite signed COMPLEX
CLEAN matrix from a set of physical input states. Only edges
with ACTUALLY NONZERO matrix coefficients are permitted.
No Markov/subprobability or independent states are postulated. -/
def sourceOriginalSignedCleanSuccessor434
    {H : Type} [Fintype H] [DecidableEq H]
    (C : ℕ → H → H → ℂ) (i : ℕ) (S : Finset H) : Finset H :=
  S.biUnion (fun a => (Finset.univ : Finset H).filter
    (fun b => C i a b ≠ 0))

/-- True moving chronological finite CLEAN wavefront, starting
with actual initial states S; at visit i each successor follows
a NONZERO ORIGINAL signed CLEAN matrix edge. This keeps
physical Fock×cumulative-seen reachability and does NOT
replace it by the full finite power-set state carrier. -/
def sourceOriginalSignedCleanWavefront434
    {H : Type} [Fintype H] [DecidableEq H]
    (C : ℕ → H → H → ℂ) :
    (n start : ℕ) → Finset H → Finset H
  | 0, _, S => S
  | n+1, start, S =>
    sourceOriginalSignedCleanWavefront434 C n (start+1)
      (sourceOriginalSignedCleanSuccessor434 C start S)
/-- Nonzero original CLEAN transition sends a live state into
the immediately following physical CLEAN wavefront. -/
theorem source_original_SIGNED_clean_successor_mem434
    {H : Type} [Fintype H] [DecidableEq H]
    (C : ℕ → H → H → ℂ) (i : ℕ) (S : Finset H)
    (a b : H) (ha : a ∈ S) (hab : C i a b ≠ 0) :
    b ∈ sourceOriginalSignedCleanSuccessor434 C i S := by
  classical
  unfold sourceOriginalSignedCleanSuccessor434
  exact Finset.mem_biUnion.mpr
    ⟨a,ha,Finset.mem_filter.mpr ⟨Finset.mem_univ b,hab⟩⟩

/-- A REAL signed CLEAN n-step matrix chain seen at any
original starting state a in S depends ONLY on terminal
amplitudes inside the exact NONZERO-EDGE chronological
wavefront Reach(C,n,start,S). Thus no phantom initial
histories, nonphysical states, or independently sampled
histories may contribute. Finite complex cancellation
is fully preserved, with no absolute-value replacement. -/
theorem source_original_SIGNED_clean_chain_wavefront_ext434
    {H : Type} [Fintype H] [DecidableEq H]
    (C : ℕ → H → H → ℂ) :
    ∀ n start (S : Finset H) (f g : H → ℂ),
      (∀ b ∈ sourceOriginalSignedCleanWavefront434 C n start S,
        f b = g b) →
      ∀ a ∈ S,
        sourceOriginalSignedMatrixChain434 C n start f a =
        sourceOriginalSignedMatrixChain434 C n start g a := by
  intro n
  induction n with
  | zero =>
      intro start S f g hEq a ha
      simpa only [sourceOriginalSignedMatrixChain434,
        sourceOriginalSignedCleanWavefront434] using hEq a ha
  | succ n ih =>
      intro start S f g hEq a ha
      have hEq' :
          ∀ b ∈ sourceOriginalSignedCleanWavefront434 C n (start+1)
              (sourceOriginalSignedCleanSuccessor434 C start S),
            f b = g b := hEq
      change
        (∑ b : H, C start a b *
          sourceOriginalSignedMatrixChain434 C n (start+1) f b) =
        (∑ b : H, C start a b *
          sourceOriginalSignedMatrixChain434 C n (start+1) g b)
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hcab : C start a b = 0
      · simp [hcab]
      · have hmem : b ∈
            sourceOriginalSignedCleanSuccessor434 C start S :=
          source_original_SIGNED_clean_successor_mem434
            C start S a b ha hcab
        rw [ih (start+1)
          (sourceOriginalSignedCleanSuccessor434 C start S)
          f g hEq' b hmem]

/-- Exact complex CLEAN chain is unchanged by zeroing
terminal data outside the ACTUAL chronological wavefront
from the desired start states; NO energy/counting loss. -/
theorem source_original_SIGNED_clean_chain_restrict_wavefront434
    {H : Type} [Fintype H] [DecidableEq H]
    (C : ℕ → H → H → ℂ) (n start : ℕ) (S : Finset H)
    (f : H → ℂ) (a : H) (ha : a ∈ S) :
    sourceOriginalSignedMatrixChain434 C n start f a =
      sourceOriginalSignedMatrixChain434 C n start
        (fun b => if b ∈ sourceOriginalSignedCleanWavefront434
          C n start S then f b else 0) a := by
  apply source_original_SIGNED_clean_chain_wavefront_ext434
    C n start S f
    (fun b => if b ∈ sourceOriginalSignedCleanWavefront434
      C n start S then f b else 0)
  · intro b hb
    simp [hb]
  · exact ha
/-- Actual FIRST-DIRTY Duhamel expansion on a genuine
initial set S has EXACTLY ONE DIRTY action at j, evaluated
ONLY at the CLEAN-REACHABLE wavefront from S after j steps.
Full signed suffix remains unchanged on its physical carrier.
This avoids *all initially inaccessible numerical history
fibres* on a per-insertion basis, not only at time zero.
It retains ALL complex interferences, joint K and chronology. -/
theorem source_original_SIGNED_DIRTY_initial_wavefront_positions434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ) (n start : ℕ)
    (S : Finset H) (f : H → ℂ) (a : H)
    (ha : a ∈ S) :
    sourceOriginalSignedMatrixDirtyChain434
      C D n start f a =
    ∑ j ∈ Finset.range n,
      sourceOriginalSignedMatrixChain434 C j start
        (fun b =>
          if b ∈ sourceOriginalSignedCleanWavefront434
            C j start S then
              sourceOriginalSignedMatrixAction434 (D (start+j))
                (sourceOriginalSignedMatrixChain434
                  (sourceOriginalSignedKernelAdd434 C D)
                  (n-(j+1)) (start+j+1) f) b
          else 0) a := by
  rw [source_original_signed_matrix_dirty_positions434]
  apply Finset.sum_congr rfl
  intro j hj
  unfold sourceOriginalSignedMatrixAt434
  exact source_original_SIGNED_clean_chain_restrict_wavefront434
    C j start S
    (sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f))
    a ha
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSignedWavefrontHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Signed original local insertion observable evaluated ONLY
at the TRUE CLEAN-reachable Fock×seen wavefront from a
specified finite set of physically admissible initial states.
The DIRTY matrix, entire FULL suffix and all complex chronology
are unchanged; the only restriction is the PROVED CLEAN support. -/
def sourceOriginalSignedWavefrontLocalTarget434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ) (n start j : ℕ)
    (S : Finset H) (f : H → ℂ) (b : H) : ℂ :=
  if b ∈ sourceOriginalSignedCleanWavefront434 C j start S then
    sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f) b
  else 0

/-- Original first-DIRTY COMPLEX expansion restricted to
true nonzero-initial-amplitude states. The entire post-CLEAN
wavefront at EACH insertion j is explicit and exact. -/
theorem source_original_SIGNED_DIRTY_supported_wavefront_identity434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ) (n start : ℕ)
    (S : Finset H) (f : H → ℂ) :
    (fun a : H =>
      if a∈S then sourceOriginalSignedMatrixDirtyChain434 C D n start f a
      else 0) =
    (fun a : H => ∑ j ∈ Finset.range n,
      if a∈S then
        sourceOriginalSignedMatrixChain434 C j start
          (sourceOriginalSignedWavefrontLocalTarget434
            C D n start j S f) a
      else 0) := by
  funext a
  by_cases ha : a∈S
  · simp only [if_pos ha]
    exact source_original_SIGNED_DIRTY_initial_wavefront_positions434
      C D n start S f a ha
  · simp [ha]

/-- Finite TRUE supported CLEAN/DIRTY signed Hilbert
Duhamel bound: only n insertion positions are paid,
and the local target at each position is EXACTLY
masked to the actual CLEAN-reachable wavefront.
No multiplying by #historical states, #SMALL/BIG labels,
#comparison patterns or independently sampled events. -/
theorem source_original_SIGNED_DIRTY_supported_wavefront_energy434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 ≤ π a)
    (n start : ℕ) (S : Finset H) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (fun a => if a∈S then
        sourceOriginalSignedMatrixDirtyChain434 C D n start f a else 0) ≤
    (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedJointForwardEnergy434 π
        (fun a => if a∈S then
          sourceOriginalSignedMatrixChain434 C j start
            (sourceOriginalSignedWavefrontLocalTarget434
              C D n start j S f) a
          else 0) := by
  have hEq := source_original_SIGNED_DIRTY_supported_wavefront_identity434
    C D n start S f
  rw [hEq]
  have hh := source_original_SIGNED_forward_finite_square_sum434
    π hπ (Finset.range n)
    (fun j a => if a∈S then
      sourceOriginalSignedMatrixChain434 C j start
        (sourceOriginalSignedWavefrontLocalTarget434
          C D n start j S f) a
      else 0)
  simpa only [Finset.card_range] using hh
/-- Actual supported true initial Fock×seen chronology admits
a certified forward Hilbert bound by CLEAN Schur gains
times the local DIRTY*FULL-suffix energy RESTRICTED to the
CLEAN-reachable states at the insertion time.
This is always <= the old unmasked full-state target budget,
with NO new probability/independence hypotheses.
Requires only positive genuine finite Fock/OLD density π. -/
theorem source_original_SIGNED_DIRTY_supported_wavefront_Schur434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (S : Finset H) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (fun a => if a∈S then
        sourceOriginalSignedMatrixDirtyChain434 C D n start f a else 0) ≤
    (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
      sourceOriginalSignedJointForwardEnergy434 π
        (sourceOriginalSignedWavefrontLocalTarget434
          C D n start j S f) := by
  have hStart :=
    source_original_SIGNED_DIRTY_supported_wavefront_energy434
      C D π (fun a => (hπ a).le) n start S f
  have hPoint (j : ℕ) :
      sourceOriginalSignedJointForwardEnergy434 π
        (fun a => if a∈S then
          sourceOriginalSignedMatrixChain434 C j start
            (sourceOriginalSignedWavefrontLocalTarget434
              C D n start j S f) a else 0) ≤
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
        sourceOriginalSignedJointForwardEnergy434 π
          (sourceOriginalSignedWavefrontLocalTarget434
            C D n start j S f) := by
    let g := sourceOriginalSignedWavefrontLocalTarget434
      C D n start j S f
    let h : H → ℂ := sourceOriginalSignedMatrixChain434 C j start g
    have hMask :
        sourceOriginalSignedJointForwardEnergy434 π
          (fun a => if a∈S then h a else 0) ≤
        sourceOriginalSignedJointForwardEnergy434 π h := by
      unfold sourceOriginalSignedJointForwardEnergy434
      apply Finset.sum_le_sum
      intro a ha
      by_cases hm : a∈S
      · simp [hm]
      · simp [hm]
        exact sq_nonneg _
    have hSchur := source_original_SIGNED_forward_chain_exact_Schur434
      C π hπ j start g
    exact hMask.trans hSchur
  have hSum := Finset.sum_le_sum
    (s := Finset.range n)
    (fun j hj => hPoint j)
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg _
  exact hStart.trans (mul_le_mul_of_nonneg_left hSum hN)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSignedWavefrontTripleSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- TRUE CLEAN-reachable DIRTY insertion kernel, identical to
the original complex DIRTY matrix INSIDE the chronological CLEAN
wavefront and exactly zero for unreachable start states.
No fake transition, resampling, or positive K replacement. -/
noncomputable def sourceOriginalSignedWavefrontDIRTYKernel434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ) (n start j : ℕ)
    (S : Finset H) : H → H → ℂ :=
  fun a b =>
    if a ∈ sourceOriginalSignedCleanWavefront434 C j start S then
      D (start+j) a b else 0

/-- Exact complex equality of actual wavefront-local DIRTY
amplitude and one matrix action with the masked SOURCE kernel,
followed by the unchanged FULL suffix. -/
theorem source_original_SIGNED_wavefront_local_matrix_action434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ)
    (n start j : ℕ) (S : Finset H) (f : H → ℂ) :
    sourceOriginalSignedWavefrontLocalTarget434
      C D n start j S f =
    sourceOriginalSignedMatrixAction434
      (sourceOriginalSignedWavefrontDIRTYKernel434
        C D n start j S)
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f) := by
  funext a
  unfold sourceOriginalSignedWavefrontLocalTarget434
    sourceOriginalSignedMatrixAction434
    sourceOriginalSignedWavefrontDIRTYKernel434
  by_cases h : a ∈ sourceOriginalSignedCleanWavefront434 C j start S
  · simp [h]
  · simp [h]
/-- Coherent signed local first-DIRTY Fock×seen target energy
is bounded by the TRUE masked-DIRTY one-step Schur gain,
followed by the TRUE FULL signed chain Schur gain times
the actual terminal Hilbert energy. No factor #histories,
#state paths, #K patterns, or #BIG carrier. The triple
Schur gains themselves are not asserted to be small. -/
theorem source_original_SIGNED_wavefront_local_triple_Schur434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (n start j : ℕ) (S : Finset H) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (sourceOriginalSignedWavefrontLocalTarget434
        C D n start j S f) ≤
    sourceOriginalSignedOneStepSchurGain434 π
      (sourceOriginalSignedWavefrontDIRTYKernel434
        C D n start j S) *
    sourceOriginalSignedPrefixSchurGainChain434
      (sourceOriginalSignedKernelAdd434 C D) π
      (n-(j+1)) (start+j+1) *
    sourceOriginalSignedJointForwardEnergy434 π f := by
  let F := sourceOriginalSignedKernelAdd434 C D
  let M := sourceOriginalSignedWavefrontDIRTYKernel434
    C D n start j S
  let g := sourceOriginalSignedMatrixChain434 F
    (n-(j+1)) (start+j+1) f
  have hEq := source_original_SIGNED_wavefront_local_matrix_action434
    C D n start j S f
  rw [hEq]
  have hFirst := source_original_SIGNED_forward_exact_Schur434
    π hπ M g
  have hSecond := source_original_SIGNED_forward_chain_exact_Schur434
    F π hπ (n-(j+1)) (start+j+1) f
  have hG : 0 ≤ sourceOriginalSignedOneStepSchurGain434 π M :=
    source_original_SIGNED_one_step_Schur_gain_nonneg434 π M
  calc
    _ ≤ sourceOriginalSignedOneStepSchurGain434 π M *
          sourceOriginalSignedJointForwardEnergy434 π g := by
            simpa only [sourceOriginalSignedOneStepSchurGain434,
              mul_comm,mul_left_comm,mul_assoc] using hFirst
    _ ≤ sourceOriginalSignedOneStepSchurGain434 π M *
          (sourceOriginalSignedPrefixSchurGainChain434 F π
            (n-(j+1)) (start+j+1) *
            sourceOriginalSignedJointForwardEnergy434 π f) :=
      mul_le_mul_of_nonneg_left hSecond hG
    _ = _ := by ring
/-- Exact complete chronological first-DIRTY forward operator
energy controlled by ONLY the real n insertion factor, and
true triple Schur gains: CLEAN prefix, DIRTY edge masked
to genuinely reached clean states, FULL suffix.
Every complex C/D/K and same numerical seen state is kept.
The bound has NO additional state/history/prime cardinality
penalty. Quantitative log decay of the gains remains open. -/
theorem source_original_SIGNED_supported_wavefront_triple_Schur434
    {H : Type} [Fintype H] [DecidableEq H]
    (C D : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (S : Finset H) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (fun a => if a∈S then
        sourceOriginalSignedMatrixDirtyChain434 C D n start f a
        else 0) ≤
    (n:ℝ) * (∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
      sourceOriginalSignedOneStepSchurGain434 π
        (sourceOriginalSignedWavefrontDIRTYKernel434
          C D n start j S) *
      sourceOriginalSignedPrefixSchurGainChain434
        (sourceOriginalSignedKernelAdd434 C D) π
        (n-(j+1)) (start+j+1)) *
      sourceOriginalSignedJointForwardEnergy434 π f := by
  have hFront := source_original_SIGNED_DIRTY_supported_wavefront_Schur434
    C D π hπ n start S f
  have hLocal (j : ℕ) :=
    source_original_SIGNED_wavefront_local_triple_Schur434
      C D π hπ n start j S f
  have hPref (j : ℕ) :
      0 ≤ sourceOriginalSignedPrefixSchurGainChain434 C π j start :=
    source_original_SIGNED_prefix_Schur_gain_chain_nonneg434 C π j start
  have hSum :
      (∑ j ∈ Finset.range n,
        sourceOriginalSignedPrefixSchurGainChain434 C π j start *
        sourceOriginalSignedJointForwardEnergy434 π
          (sourceOriginalSignedWavefrontLocalTarget434
            C D n start j S f)) ≤
      ∑ j ∈ Finset.range n,
        sourceOriginalSignedPrefixSchurGainChain434 C π j start *
        (sourceOriginalSignedOneStepSchurGain434 π
          (sourceOriginalSignedWavefrontDIRTYKernel434 C D n start j S) *
          sourceOriginalSignedPrefixSchurGainChain434
            (sourceOriginalSignedKernelAdd434 C D) π
              (n-(j+1)) (start+j+1) *
          sourceOriginalSignedJointForwardEnergy434 π f) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hLocal j) (hPref j)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
      sourceOriginalSignedJointForwardEnergy434 π
        (sourceOriginalSignedWavefrontLocalTarget434
          C D n start j S f) := hFront
    _ ≤ (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
      (sourceOriginalSignedOneStepSchurGain434 π
        (sourceOriginalSignedWavefrontDIRTYKernel434 C D n start j S) *
        sourceOriginalSignedPrefixSchurGainChain434
          (sourceOriginalSignedKernelAdd434 C D) π
          (n-(j+1)) (start+j+1) *
        sourceOriginalSignedJointForwardEnergy434 π f) :=
      mul_le_mul_of_nonneg_left hSum hn
    _ = _ := by
      have hDist :
          (∑ j ∈ Finset.range n,
            sourceOriginalSignedPrefixSchurGainChain434 C π j start *
            (sourceOriginalSignedOneStepSchurGain434 π
              (sourceOriginalSignedWavefrontDIRTYKernel434
                C D n start j S) *
              sourceOriginalSignedPrefixSchurGainChain434
                (sourceOriginalSignedKernelAdd434 C D) π
                  (n-(j+1)) (start+j+1) *
              sourceOriginalSignedJointForwardEnergy434 π f)) =
          (∑ j ∈ Finset.range n,
            sourceOriginalSignedPrefixSchurGainChain434 C π j start *
            sourceOriginalSignedOneStepSchurGain434 π
              (sourceOriginalSignedWavefrontDIRTYKernel434
                C D n start j S) *
            sourceOriginalSignedPrefixSchurGainChain434
              (sourceOriginalSignedKernelAdd434 C D) π
                (n-(j+1)) (start+j+1)) *
            sourceOriginalSignedJointForwardEnergy434 π f := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hDist]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSignedWavefrontGhostESplit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- FIRST physical G-row restricted to an actual CLEAN wavefront
of past reachable state histories. It keeps each complex ghost
matrix entry unchanged ON wavefront and zero off it. -/
noncomputable def sourceOriginalSignedWavefrontMaskedGhost434
    {H : Type} [Fintype H] [DecidableEq H]
    (S : Finset H) (G : H → H → ℂ) : H → H → ℂ :=
  fun a b => if a∈S then G a b else 0

/-- EXACT physical matrix factorization of a masked G_i*E_i
DIRTY edge, using the same intermediate seen-history state,
with no modulus, ghost averaging, missing OLD gate or inserted
independence assumption. -/
theorem source_original_SIGNED_wavefront_masked_G_E_factor434
    {H : Type} [Fintype H] [DecidableEq H]
    (S : Finset H) (G E : H → H → ℂ) :
    (fun a b => if a∈S then
      sourceOriginalSignedMatrixProduct434 G E a b else 0) =
    sourceOriginalSignedMatrixProduct434
      (sourceOriginalSignedWavefrontMaskedGhost434 S G) E := by
  funext a b
  unfold sourceOriginalSignedMatrixProduct434
    sourceOriginalSignedWavefrontMaskedGhost434
  by_cases h : a∈S
  · simp [h]
  · simp [h]
/-- Local G_i E_DIRTY physical wavefront target, after the
original full signed future, bounded by the TRUE Schur gain of
the CLEAN-front-masked ghost G_i times the TRUE Schur gain
of the separately OLD-masked E_DIRTY_i. The extra future is
kept completely COHERENT inside the input test. Both actual
matrix kernels are retained, no full-path TV. -/
theorem source_original_SIGNED_wavefront_ghost_then_E_Schur434
    {H : Type} [Fintype H] [DecidableEq H]
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (S : Finset H) (G E : H → H → ℂ) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (sourceOriginalSignedMatrixAction434
        (sourceOriginalSignedMatrixProduct434
          (sourceOriginalSignedWavefrontMaskedGhost434 S G) E) f) ≤
    sourceOriginalSignedOneStepSchurGain434 π
      (sourceOriginalSignedWavefrontMaskedGhost434 S G) *
    sourceOriginalSignedOneStepSchurGain434 π E *
    sourceOriginalSignedJointForwardEnergy434 π f := by
  let Gs := sourceOriginalSignedWavefrontMaskedGhost434 S G
  have hEq (a : H) :
      sourceOriginalSignedMatrixAction434
        (sourceOriginalSignedMatrixProduct434 Gs E) f a =
      sourceOriginalSignedMatrixAction434 Gs
        (sourceOriginalSignedMatrixAction434 E f) a := by
    exact (source_original_signed_matrix_product_apply434 Gs E f a).symm
  have hEq' :
      sourceOriginalSignedMatrixAction434
        (sourceOriginalSignedMatrixProduct434 Gs E) f =
      sourceOriginalSignedMatrixAction434 Gs
        (sourceOriginalSignedMatrixAction434 E f) := by
    funext a
    exact hEq a
  rw [hEq']
  have hFirst := source_original_SIGNED_forward_exact_Schur434
    π hπ Gs (sourceOriginalSignedMatrixAction434 E f)
  have hSecond := source_original_SIGNED_forward_exact_Schur434 π hπ E f
  have hG : 0 ≤ sourceOriginalSignedOneStepSchurGain434 π Gs :=
    source_original_SIGNED_one_step_Schur_gain_nonneg434 π Gs
  calc
    _ ≤ sourceOriginalSignedOneStepSchurGain434 π Gs *
      sourceOriginalSignedJointForwardEnergy434 π
        (sourceOriginalSignedMatrixAction434 E f) := by
          simpa only [sourceOriginalSignedOneStepSchurGain434,
            mul_comm,mul_left_comm,mul_assoc] using hFirst
    _ ≤ sourceOriginalSignedOneStepSchurGain434 π Gs *
      (sourceOriginalSignedOneStepSchurGain434 π E *
        sourceOriginalSignedJointForwardEnergy434 π f) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [sourceOriginalSignedOneStepSchurGain434,
          mul_comm,mul_left_comm,mul_assoc] using hSecond) hG
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03SignedBilinearProjection -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 550000

/-- Odd-parity numerator: the original untwisted coefficient minus
the actual completely multiplicative parity-twisted coefficient.
The factor 1/2, if desired, is applied only AFTER projection. -/
noncomputable def sourceOriginalParityOddNumerator434
    (P : Finset ℕ) (a : ℤ → ℂ) (m : ℤ) : ℂ :=
  sourceSignedCoefficients434 P false a m -
    sourceSignedCoefficients434 P true a m

/-- Exact FOUR-SIGN arithmetic cancellation at a single original
coefficient pair. This retains cross terms; it does not imply
smallness of the surviving odd-odd correlation. -/
theorem source_original_four_sign_pair_odd_numerator434
    (P : Finset ℕ) (a b : ℤ → ℂ) (m n : ℤ) :
    (star (sourceSignedCoefficients434 P false a m) *
        sourceSignedCoefficients434 P false b n
     - star (sourceSignedCoefficients434 P true a m) *
        sourceSignedCoefficients434 P false b n
     - star (sourceSignedCoefficients434 P false a m) *
        sourceSignedCoefficients434 P true b n
     + star (sourceSignedCoefficients434 P true a m) *
        sourceSignedCoefficients434 P true b n) =
    star (sourceOriginalParityOddNumerator434 P a m) *
      sourceOriginalParityOddNumerator434 P b n := by
  unfold sourceOriginalParityOddNumerator434
  rw [star_sub]
  ring
/-- The COMPLETE bilinear kernel is kept intact: no factorization
in K, no path independence, and no loss of cross-sign terms. -/
noncomputable def sourceOriginalSignedBilinearKernel434
    (P : Finset ℕ) (S T : Finset ℤ) (a b : ℤ → ℂ)
    (K : ℤ → ℤ → ℂ) (eps1 eps2 : Bool) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ T, K m n *
    (star (sourceSignedCoefficients434 P eps1 a m) *
      sourceSignedCoefficients434 P eps2 b n)

/-- The original four independent parity channels project EXACTLY
onto the odd-odd part BEFORE the coherent square. This statement
is valid for the ACTUAL nonseparable joint arithmetic kernel K. -/
theorem source_original_four_sign_bilinear_projection434
    (P : Finset ℕ) (S T : Finset ℤ) (a b : ℤ → ℂ)
    (K : ℤ → ℤ → ℂ) :
    (sourceOriginalSignedBilinearKernel434 P S T a b K false false
      - sourceOriginalSignedBilinearKernel434 P S T a b K true false
      - sourceOriginalSignedBilinearKernel434 P S T a b K false true
      + sourceOriginalSignedBilinearKernel434 P S T a b K true true) =
    ∑ m ∈ S, ∑ n ∈ T, K m n *
      (star (sourceOriginalParityOddNumerator434 P a m) *
        sourceOriginalParityOddNumerator434 P b n) := by
  simp only [sourceOriginalSignedBilinearKernel434,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have h := source_original_four_sign_pair_odd_numerator434 P a b m n
  calc
    _ = K m n *
      (star (sourceSignedCoefficients434 P false a m) *
          sourceSignedCoefficients434 P false b n
       - star (sourceSignedCoefficients434 P true a m) *
          sourceSignedCoefficients434 P false b n
       - star (sourceSignedCoefficients434 P false a m) *
          sourceSignedCoefficients434 P true b n
       + star (sourceSignedCoefficients434 P true a m) *
          sourceSignedCoefficients434 P true b n) := by ring
    _ = _ := by rw [h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ProjectedActualKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 650000

/-- The ACTUAL original source03 prime parity on the FULL
canonical prime union. No artificial choice of signs is used. -/
theorem source_original_TRUE_source03_odd_parity_factor434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d < (1/2:ℝ)) (hcd : cfg.cexp < d)
    (m : ℤ) :
    let uF := sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd
    sourceOriginalParityOddNumerator434 z.G uF.endpoint m =
       ((1:ℂ) - literalSourceParity z.G m.toNat) * uF.endpoint m := by
  dsimp only
  simp only [sourceOriginalParityOddNumerator434,
    sourceSignedCoefficients434, sourceEndpointSign434,
    Bool.false_eq_true, ite_false, ite_true,
    one_mul]
  ring

/-- The SAME full signed joint kernel K appears in all FOUR
original source03 channels. Their inclusion-exclusion removes
the parity-even endpoint components before any Gram square. -/
theorem source_original_TRUE_source03_projected_actual_kernel434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u v : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d < (1/2:ℝ)) (hcd : cfg.cexp < d)
    (K : ℤ → ℤ → ℂ) :
    let uu := sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd
    let vv := sourceOriginalCanonicalComparisonFullTwist434 z v hL hd hcd
    (sourceOriginalSignedBilinearKernel434 uu.Ptw
         uu.support vv.support uu.endpoint vv.endpoint K false false
      - sourceOriginalSignedBilinearKernel434 uu.Ptw
         uu.support vv.support uu.endpoint vv.endpoint K true false
      - sourceOriginalSignedBilinearKernel434 uu.Ptw
         uu.support vv.support uu.endpoint vv.endpoint K false true
      + sourceOriginalSignedBilinearKernel434 uu.Ptw
         uu.support vv.support uu.endpoint vv.endpoint K true true) =
    ∑ m ∈ uu.support, ∑ t ∈ vv.support,
      K m t *
        (star (sourceOriginalParityOddNumerator434 z.G uu.endpoint m) *
          sourceOriginalParityOddNumerator434 z.G vv.endpoint t) := by
  dsimp only
  have hP :
      (sourceOriginalCanonicalComparisonFullTwist434
        z u hL hd hcd).Ptw = z.G := rfl
  rw [hP]
  exact source_original_four_sign_bilinear_projection434
    z.G _ _ _ _ K

/-- Exact normalized four-sign projector (ff-tf-ft+tt)/4 for
the TRUE source03 prime family and the UNCHANGED joint K.
No mean-square saving follows without new character arithmetic. -/
theorem source_original_TRUE_source03_projected_quarter_kernel434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u v : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d < (1/2:ℝ)) (hcd : cfg.cexp < d)
    (K : ℤ → ℤ → ℂ) :
    let uu := sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd
    let vv := sourceOriginalCanonicalComparisonFullTwist434 z v hL hd hcd
    let C : Bool → Bool → ℂ :=
      sourceOriginalSignedBilinearKernel434 uu.Ptw uu.support
        vv.support uu.endpoint vv.endpoint K
    (C false false - C true false - C false true + C true true) / 4 =
      (∑ m ∈ uu.support, ∑ t ∈ vv.support,
        K m t * (star (sourceOriginalParityOddNumerator434 z.G uu.endpoint m) *
          sourceOriginalParityOddNumerator434 z.G vv.endpoint t)) / 4 := by
  dsimp only
  exact congrArg (fun w : ℂ => w / 4)
    (source_original_TRUE_source03_projected_actual_kernel434
      z u v hL hd hcd K)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ActualTwoBoxKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The ACTUAL two independent integer product boxes, retaining the
literal shifted arithmetic equation n=m+k*da*db and both complex
cell weights. Only the FULL finite kernel is summed, not split into
independent character kernels. -/
noncomputable def sourceOriginalActualTwoBoxShiftKernel434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (k : ℤ)
    (m n : ℤ) : ℂ :=
  ∑ ij ∈ F1.product F2,
    if n = m + k*(ij.1:ℤ)*(ij.2:ℤ) then
      w1 ij.1 * w2 ij.2 else 0

/-- Exact finite Fubini reindexing of the ORIGINAL shifted two-box
bilinear arithmetic expression, before applying any sign projector.
No factorization or estimate on the signed kernel is asserted. -/
theorem source_original_ACTUAL_two_box_kernel_fubini434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) (P : Finset ℕ)
    (k : ℤ) (eps1 eps2 : Bool) :
    sourceOriginalSignedBilinearKernel434 P S T a b
      (sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k)
      eps1 eps2 =
    ∑ ij ∈ F1.product F2, ∑ m ∈ S, ∑ n ∈ T,
      if n = m + k*(ij.1:ℤ)*(ij.2:ℤ) then
        (w1 ij.1*w2 ij.2) *
          (star (sourceSignedCoefficients434 P eps1 a m) *
            sourceSignedCoefficients434 P eps2 b n) else 0 := by
  unfold sourceOriginalSignedBilinearKernel434
    sourceOriginalActualTwoBoxShiftKernel434
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ m ∈ S, ∑ ij ∈ F1.product F2, ∑ n ∈ T,
          (if n = m + k*(ij.1:ℤ)*(ij.2:ℤ) then w1 ij.1*w2 ij.2 else 0) *
            (star (sourceSignedCoefficients434 P eps1 a m) *
              sourceSignedCoefficients434 P eps2 b n) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ ij ∈ F1.product F2, ∑ m ∈ S, ∑ n ∈ T,
          (if n = m + k*(ij.1:ℤ)*(ij.2:ℤ) then w1 ij.1*w2 ij.2 else 0) *
            (star (sourceSignedCoefficients434 P eps1 a m) *
              sourceSignedCoefficients434 P eps2 b n) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ij hij
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs with h
      · ring
      · simp

/-- Unfold the EXACT original nested two-block shifted correlation,
with both independent arithmetic product boxes and any common parity
labels. The two group coefficient weights are not factorized further. -/
theorem source_original_ACTUAL_two_box_nested_source434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) (P : Finset ℕ)
    (k : ℤ) (eps1 eps2 : Bool) :
    sourceOriginalSignedBilinearKernel434 P S T a b
      (sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k)
      eps1 eps2 =
    ∑ da ∈ F1, w1 da * ∑ db ∈ F2, w2 db *
      ∑ m ∈ S, ∑ n ∈ T,
        if n = m + k*(da:ℤ)*(db:ℤ) then
          star (sourceSignedCoefficients434 P eps1 a m) *
            sourceSignedCoefficients434 P eps2 b n else 0 := by
  rw [source_original_ACTUAL_two_box_kernel_fubini434]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro da hda
  apply Finset.sum_congr rfl
  intro db hdb
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with h
  · ring
  · simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ActualTwoBoxArithmetic -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 750000

/-- Any nonzero contribution to the literal shifted TWO-box kernel
forces divisibility of n-m by the genuine integer shift k. -/
theorem source_original_ACTUAL_two_box_shift_dvd434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (k m n : ℤ)
    (hndvd : ¬ k ∣ n-m) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k m n = 0 := by
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  split_ifs with h
  · exfalso
    apply hndvd
    refine ⟨(ij.1:ℤ)*(ij.2:ℤ), ?_⟩
    rw [h]
    ring
  · rfl

/-- For k nonzero, the two-box operator has no diagonal contribution
whenever the weights vanish at the prohibited product label zero. -/
theorem source_original_ACTUAL_two_box_shift_offdiag434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (k m : ℤ)
    (hk : k ≠ 0) (hw1 : w1 0 = 0) (hw2 : w2 0 = 0) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k m m = 0 := by
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases ha : ij.1 = 0
  · simp [ha, hw1]
  by_cases hb : ij.2 = 0
  · simp [hb, hw2]
  have ha' : (ij.1:ℤ) ≠ 0 := by exact_mod_cast ha
  have hb' : (ij.2:ℤ) ≠ 0 := by exact_mod_cast hb
  have hprod : k*(ij.1:ℤ)*(ij.2:ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hk ha') hb'
  have hneq : ¬ m = m + k*(ij.1:ℤ)*(ij.2:ℤ) := by
    intro h
    apply hprod
    omega
  simp [hneq]

/-- The ACTUAL logarithmic-cell gates vanish at zero, so the
genuine two-product SOURCE kernel has no literal m=n diagonal.
No independence of the two arithmetic boxes is assumed. -/
theorem source_original_ACTUAL_two_box_logcell_offdiag434
    (F1 F2 : Finset ℕ) (rho1 rho2 : ℕ → ℝ)
    (U1 U2 h1 h2 : ℝ) (b1 b2 : ℕ → ℂ) (k m : ℤ)
    (hk : k ≠ 0) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2
      (fun a => (rho1 a:ℂ)*sourceOriginalLogCellMask434 F1 U1 h1 b1 a)
      (fun b => (rho2 b:ℂ)*sourceOriginalLogCellMask434 F2 U2 h2 b2 b)
      k m m = 0 := by
  apply source_original_ACTUAL_two_box_shift_offdiag434
  · exact hk
  · simp [sourceOriginalLogCellMask434]
  · simp [sourceOriginalLogCellMask434]

/-- The FOUR actual independent endpoint signs are projected before
forming any Gram square. The full two-box shifted arithmetic kernel
survives, with all complex off-diagonal terms retained. -/
theorem source_original_ACTUAL_two_box_odd_bilinear434
    (F1 F2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) (P : Finset ℕ) (k : ℤ) :
    let K := sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k
    (sourceOriginalSignedBilinearKernel434 P S T a b K false false
      - sourceOriginalSignedBilinearKernel434 P S T a b K true false
      - sourceOriginalSignedBilinearKernel434 P S T a b K false true
      + sourceOriginalSignedBilinearKernel434 P S T a b K true true) =
    ∑ ij ∈ F1.product F2, ∑ m ∈ S, ∑ n ∈ T,
      if n = m + k*(ij.1:ℤ)*(ij.2:ℤ) then
        (w1 ij.1*w2 ij.2) *
          (star (sourceOriginalParityOddNumerator434 P a m) *
             sourceOriginalParityOddNumerator434 P b n) else 0 := by
  dsimp only
  calc
    _ = ∑ m ∈ S, ∑ n ∈ T,
          sourceOriginalActualTwoBoxShiftKernel434 F1 F2 w1 w2 k m n *
            (star (sourceOriginalParityOddNumerator434 P a m) *
              sourceOriginalParityOddNumerator434 P b n) :=
        source_original_four_sign_bilinear_projection434
          P S T a b _
    _ = _ := by
      have h := source_original_ACTUAL_two_box_kernel_fubini434
        F1 F2 w1 w2 S T
        (sourceOriginalParityOddNumerator434 P a)
        (sourceOriginalParityOddNumerator434 P b)
        ∅ k false false
      simpa [sourceOriginalSignedBilinearKernel434,
        sourceSignedCoefficients434, sourceEndpointSign434] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ActualBigAtomAvoidance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A nonzero TRUE source factorial product atom cannot contain
any prime outside its genuine group-prime union. -/
theorem source_original_TRUE_atom_avoids_outside_prime434
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (r q : ℕ) (hqprime : q.Prime)
    (hqout : q ∉ G.biUnion S)
    (hr : sourceProductAtomMass G S k V r ≠ 0) :
    ¬ q ∣ r := by
  have hv : sourceAtomValid G S k r := by
    by_contra hn
    exact hr (by simp [sourceProductAtomMass, hn])
  intro hdiv
  have hmem : q ∈ r.primeFactors :=
    hqprime.mem_primeFactors hdiv hv.1
  exact hqout (hv.2.2 q hmem)

/-- A genuine BIG prime-product atom, from ALL the original
canonical BIG intervals, is not divisible by ANY genuine
SMALL prime from the distinguished source03 group S. -/
theorem source_original_TRUE_source03_BIG_atom_avoids_SMALL434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k : Fin n → ℕ) (r q : ℕ) (hq : q ∈ z.S)
    (hr : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k z.Vbig r ≠ 0) :
    ¬ q ∣ r := by
  have hprime : q.Prime := (z.hSmallBand none q hq).1
  have hnot : q ∉
      (Finset.univ : Finset (Fin n)).biUnion z.Tb := by
    intro h
    obtain ⟨i, hi, hbig⟩ := Finset.mem_biUnion.mp h
    exact (Finset.disjoint_left.mp (z.hSB none i)) hq hbig
  exact source_original_TRUE_atom_avoids_outside_prime434
    (Finset.univ : Finset (Fin n)) z.Tb k z.Vbig r q
    hprime hnot hr
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ActualBigShiftSmallObstruction -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1100000

/-- REAL source03 obstruction to a shifted collision: when k=+1
or k=-1, a SMALL prime q cannot divide both endpoint integers
of a shift by TWO nonzero genuine BIG prime-product atoms.
No synthetic independent-prime assumptions are introduced. -/
theorem source_original_TRUE_source03_BIG_shift_no_shared_SMALL434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (da db q : ℕ)
    (hq : q ∈ z.S)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db ≠ 0)
    (k : ℤ) (hk : k = 1 ∨ k = -1)
    (m t : ℤ)
    (hshift : t = m + k*(da:ℤ)*(db:ℤ))
    (hm : (q:ℤ) ∣ m) (ht : (q:ℤ) ∣ t) : False := by
  have hdiv : (q:ℤ) ∣ t-m := dvd_sub ht hm
  have heq : t-m = k*(da:ℤ)*(db:ℤ) := by
    rw [hshift]
    ring
  rw [heq] at hdiv
  have hprod : (q:ℤ) ∣ (da:ℤ)*(db:ℤ) := by
    rcases hk with hp | hm
    · rw [hp] at hdiv
      simpa using hdiv
    · rw [hm] at hdiv
      have hneg : (q:ℤ) ∣ -((da:ℤ)*(db:ℤ)) := by
        convert hdiv using 1 <;> ring
      exact dvd_neg.mp hneg
  have hnat : q ∣ da*db := by
    exact_mod_cast hprod
  rcases ((z.hSmallBand none q hq).1.dvd_mul).mp hnat with hd | hd
  · exact (source_original_TRUE_source03_BIG_atom_avoids_SMALL434
      z k1 da q hq ha) hd
  · exact (source_original_TRUE_source03_BIG_atom_avoids_SMALL434
      z k2 db q hq hb) hd

/-- After summing over both genuine BIG product-atom laws,
the complete shifted two-box K is exactly ZERO on the same
SMALL-prime double-divisibility stratum, for k=1 or k=-1.
This is an exact arithmetic cancellation-free exclusion,
not a logarithmic bound on the surviving off-diagonal Gram. -/
theorem source_original_TRUE_source03_BIG_two_box_SMALL_stratum_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (b1 b2 : ℕ → ℂ) (k : ℤ) (hk : k = 1 ∨ k = -1)
    (q : ℕ) (hq : q ∈ z.S) (m t : ℤ)
    (hm : (q:ℤ) ∣ m) (ht : (q:ℤ) ∣ t) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2
      (fun da => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da : ℂ)*b1 da)
      (fun db => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db : ℂ)*b2 db)
      k m t = 0 := by
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig ij.1 = 0
  · simp [ha]
  by_cases hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig ij.2 = 0
  · simp [hb]
  have hneq : t ≠ m + k*(ij.1:ℤ)*(ij.2:ℤ) := by
    intro h
    exact source_original_TRUE_source03_BIG_shift_no_shared_SMALL434
      z k1 k2 ij.1 ij.2 q hq ha hb k hk m t h hm ht
  simp [hneq]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03FullKSmallPrimeDisjoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For an ARBITRARY genuine integer shift k, no common SMALL
prime can divide both endpoints when it does not divide |k|
and both source weights are nonzero true BIG product atoms.
This extends the earlier k=1 or -1 exclusion to moving k. -/
theorem source_original_TRUE_source03_BIG_shift_no_shared_SMALL_generalK434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (da db q : ℕ)
    (hq : q ∈ z.S)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db ≠ 0)
    (k : ℤ) (hqk : ¬ q ∣ k.natAbs)
    (m t : ℤ) (hshift : t = m + k*(da:ℤ)*(db:ℤ))
    (hm : (q:ℤ) ∣ m) (ht : (q:ℤ) ∣ t) : False := by
  have hd : (q:ℤ) ∣ t-m := dvd_sub ht hm
  have heq : t-m = k*(da:ℤ)*(db:ℤ) := by
    rw [hshift]
    ring
  rw [heq] at hd
  have hNat : q ∣ (k*(da:ℤ)*(db:ℤ)).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
  have hAbs : (k*(da:ℤ)*(db:ℤ)).natAbs =
      k.natAbs * (da*db) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    ring
  rw [hAbs] at hNat
  have hp := (z.hSmallBand none q hq).1
  rcases (hp.dvd_mul).mp hNat with hQk | hQprod
  · exact hqk hQk
  rcases (hp.dvd_mul).mp hQprod with hQa | hQb
  · exact (source_original_TRUE_source03_BIG_atom_avoids_SMALL434
      z k1 da q hq ha) hQa
  · exact (source_original_TRUE_source03_BIG_atom_avoids_SMALL434
      z k2 db q hq hb) hQb

/-- From the ORIGINAL source03 SMALL exponential lower band
and the exact |k| budget, the true SMALL prime is too large
to divide the nonzero source shift k. -/
theorem source_original_TRUE_source03_SMALL_prime_exceeds_shift434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (q : ℕ) (hq : q ∈ z.S) (k : ℤ)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    ¬ q ∣ k.natAbs := by
  have hb : Real.exp (L^cfg.aexp) ≤ (q:ℝ) :=
    (z.hSmallBand none q hq).2.1
  have hr : (k.natAbs:ℝ) < (q:ℝ) :=
    lt_of_le_of_lt hK (hOrigSmall.trans_le hb)
  have hn : k.natAbs < q := by exact_mod_cast hr
  exact Nat.not_dvd_of_pos_of_lt hk hn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03RealLogCellKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Literal SOURCE03 two-product-box shift kernel with TRUE harmonic
product-atom laws and BOTH original logarithmic window masks.
The full joint shifted arithmetic equality remains inside one K. -/
noncomputable def sourceOriginalSource03RealLogCellKernel434
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ) (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ) (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (F1 F2 : Finset ℕ) (U1 U2 width1 width2 : ℝ)
    (b₁ b₂ : ℕ → ℂ) (k : ℤ) : ℤ → ℤ → ℂ :=
  sourceOriginalActualTwoBoxShiftKernel434 F1 F2
    (fun da => (sourceProductAtomMass G₁ S₁ k₁ V₁ da:ℂ) *
      sourceOriginalLogCellMask434 F1 U1 width1 b₁ da)
    (fun db => (sourceProductAtomMass G₂ S₂ k₂ V₂ db:ℂ) *
      sourceOriginalLogCellMask434 F2 U2 width2 b₂ db) k

/-- The real canonical source03 endpoint pair has EXACTLY the
original nested two-block log-cell expression in each sign channel.
The original SourceComparisonData is a required INPUT. -/
theorem source_original_TRUE_source03_original_two_box_channels434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u v : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d < (1/2:ℝ)) (hcd : cfg.cexp < d)
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ) (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ) (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (F1 F2 : Finset ℕ) (U1 U2 width1 width2 : ℝ)
    (b₁ b₂ : ℕ → ℂ) (k : ℤ) (eps1 eps2 : Bool) :
    let uu := sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd
    let vv := sourceOriginalCanonicalComparisonFullTwist434 z v hL hd hcd
    sourceOriginalSignedBilinearKernel434 uu.Ptw uu.support vv.support
       uu.endpoint vv.endpoint
       (sourceOriginalSource03RealLogCellKernel434 G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
          F1 F2 U1 U2 width1 width2 b₁ b₂ k) eps1 eps2 =
    ∑ da ∈ F1,
      (sourceProductAtomMass G₁ S₁ k₁ V₁ da:ℂ) *
        sourceOriginalLogCellMask434 F1 U1 width1 b₁ da *
      ∑ db ∈ F2,
        (sourceProductAtomMass G₂ S₂ k₂ V₂ db:ℂ) *
          sourceOriginalLogCellMask434 F2 U2 width2 b₂ db *
      ∑ m ∈ uu.support, ∑ t ∈ vv.support,
        if t = m + k*(da:ℤ)*(db:ℤ) then
          star (sourceSignedCoefficients434 uu.Ptw eps1 uu.endpoint m) *
            sourceSignedCoefficients434 uu.Ptw eps2 vv.endpoint t else 0 := by

  dsimp only
  exact source_original_ACTUAL_two_box_nested_source434 F1 F2
    (fun da => (sourceProductAtomMass G₁ S₁ k₁ V₁ da:ℂ) *
      sourceOriginalLogCellMask434 F1 U1 width1 b₁ da)
    (fun db => (sourceProductAtomMass G₂ S₂ k₂ V₂ db:ℂ) *
      sourceOriginalLogCellMask434 F2 U2 width2 b₂ db)
    (sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd).support
    (sourceOriginalCanonicalComparisonFullTwist434 z v hL hd hcd).support
    (sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd).endpoint
    (sourceOriginalCanonicalComparisonFullTwist434 z v hL hd hcd).endpoint
    (sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd).Ptw
    k eps1 eps2
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03FullKTwoBoxSMALL -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1100000

/-- For ANY integer k which avoids the given genuine SMALL prime,
the full TRUE BIG x BIG two-box kernel vanishes on endpoints both
divisible by that SMALL prime. All weighted shifted terms are kept. -/
theorem source_original_TRUE_source03_BIG_two_box_SMALL_generalK_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (b1 b2 : ℕ → ℂ) (k : ℤ)
    (q : ℕ) (hq : q ∈ z.S) (hqk : ¬ q ∣ k.natAbs)
    (m t : ℤ) (hm : (q:ℤ) ∣ m) (ht : (q:ℤ) ∣ t) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2
      (fun da => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da : ℂ)*b1 da)
      (fun db => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db : ℂ)*b2 db)
      k m t = 0 := by
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig ij.1 = 0
  · simp [ha]
  by_cases hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig ij.2 = 0
  · simp [hb]
  have hneq : t ≠ m + k*(ij.1:ℤ)*(ij.2:ℤ) := by
    intro h
    exact source_original_TRUE_source03_BIG_shift_no_shared_SMALL_generalK434
      z k1 k2 ij.1 ij.2 q hq ha hb k hqk m t h hm ht
  simp [hneq]

/-- Original source03 comparison datum supplies the verified
SMALL cutoff L^Carc < exp(L^a). Together with the genuine
nonzero shift size |k| <= L^Carc it proves exact exclusion
for the ACTUAL TWO logarithmic product boxes, all k. -/
theorem source_original_TRUE_source03_REAL_logcell_SMALL_stratum_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (q : ℕ) (hq : q ∈ z.S) (m t : ℤ)
    (hm : (q:ℤ) ∣ m) (ht : (q:ℤ) ∣ t) :
    sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 k m t = 0 := by
  have hqk : ¬ q ∣ k.natAbs :=
    source_original_TRUE_source03_SMALL_prime_exceeds_shift434
      z q hq k hk hK u.hOrigSmall
  simpa only [sourceOriginalSource03RealLogCellKernel434] using
    source_original_TRUE_source03_BIG_two_box_SMALL_generalK_zero434
      z k1 k2 F1 F2
      (sourceOriginalLogCellMask434 F1 U1 width1 b1)
      (sourceOriginalLogCellMask434 F2 U2 width2 b2)
      k q hq hqk m t hm ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03AllSmallShiftCongruence -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The actual union of the distinguished SMALL primes and every
original Ts-group. In contrast with G it contains no BIG primes. -/
noncomputable def sourceOriginalSource03AllSmall434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0) :
    Finset ℕ :=
  z.S ∪ (Finset.univ : Finset (Fin n)).biUnion z.Ts

/-- A nonzero canonical BIG product atom avoids EVERY real SMALL
group, not just the distinguished S. This is prime-factor support,
using genuine BIG/SMALL disjointness of the constructed source03. -/
theorem source_original_TRUE_source03_BIG_atom_avoids_any_SMALL434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Option (Fin n)) (k : Fin n → ℕ) (r q : ℕ)
    (hq : q ∈ z.P g)    (hr : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k z.Vbig r ≠ 0) :
    ¬ q ∣ r := by
  have hprime : q.Prime := (z.hSmallBand g q hq).1
  have hnot : q ∉
      (Finset.univ : Finset (Fin n)).biUnion z.Tb := by
    intro h
    obtain ⟨i, hi, hbig⟩ := Finset.mem_biUnion.mp h
    exact (Finset.disjoint_left.mp (z.hSB g i)) hq hbig
  exact source_original_TRUE_atom_avoids_outside_prime434
    (Finset.univ : Finset (Fin n)) z.Tb k z.Vbig r q
    hprime hnot hr

/-- Every real SMALL prime exceeds the literal moving-shift budget.
The proof works independently for S and every Ts. -/
theorem source_original_TRUE_source03_ANY_SMALL_exceeds_shift434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Option (Fin n)) (q : ℕ) (hq : q ∈ z.P g)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    ¬ q ∣ k.natAbs := by
  have hb : Real.exp (L^cfg.aexp) ≤ (q:ℝ) :=
    (z.hSmallBand g q hq).2.1
  have hr : (k.natAbs:ℝ) < (q:ℝ) :=
    lt_of_le_of_lt hK (hOrigSmall.trans_le hb)
  have hn : k.natAbs < q := by exact_mod_cast hr
  exact Nat.not_dvd_of_pos_of_lt hk hn
/-- Strong arithmetic exclusion: for a genuine BIG x BIG product
shift, the residue CHANGE is nonzero modulo every SMALL prime
whenever that prime avoids the moving multiplier k. In particular,
even two nonzero equal residues are impossible. -/
theorem source_original_TRUE_source03_BIG_shift_changes_SMALL_residue434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Option (Fin n)) (k1 k2 : Fin n → ℕ)
    (da db q : ℕ) (hq : q ∈ z.P g)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db ≠ 0)
    (k : ℤ) (hqk : ¬ q ∣ k.natAbs)
    (m t : ℤ) (hshift : t = m + k*(da:ℤ)*(db:ℤ))
    (hsame : (q:ℤ) ∣ t-m) : False := by
  have heq : t-m = k*(da:ℤ)*(db:ℤ) := by
    rw [hshift]
    ring
  rw [heq] at hsame
  have hNat : q ∣ (k*(da:ℤ)*(db:ℤ)).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hsame)
  have hAbs : (k*(da:ℤ)*(db:ℤ)).natAbs =
      k.natAbs*(da*db) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    ring
  rw [hAbs] at hNat
  have hp := (z.hSmallBand g q hq).1
  rcases (hp.dvd_mul).mp hNat with hQk | hQprod
  · exact hqk hQk
  rcases (hp.dvd_mul).mp hQprod with hQa | hQb
  · exact (source_original_TRUE_source03_BIG_atom_avoids_any_SMALL434
      z g k1 da q hq ha) hQa
  · exact (source_original_TRUE_source03_BIG_atom_avoids_any_SMALL434
      z g k2 db q hq hb) hQb

/-- The FULL genuine BIG x BIG two-product kernel has zero
congruence diagonal modulo ANY source03 SMALL prime. Both original
product weights and all possibly colliding pairs remain in the sum. -/
theorem source_original_TRUE_source03_BIG_two_box_SMALL_congruence_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Option (Fin n)) (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (b1 b2 : ℕ → ℂ) (k : ℤ)
    (q : ℕ) (hq : q ∈ z.P g) (hqk : ¬ q ∣ k.natAbs)
    (m t : ℤ) (hsame : (q:ℤ) ∣ t-m) :
    sourceOriginalActualTwoBoxShiftKernel434 F1 F2
      (fun da => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da : ℂ)*b1 da)
      (fun db => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db : ℂ)*b2 db)
      k m t = 0 := by
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig ij.1 = 0
  · simp [ha]
  by_cases hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig ij.2 = 0
  · simp [hb]
  have hneq : t ≠ m + k*(ij.1:ℤ)*(ij.2:ℤ) := by
    intro h
    exact source_original_TRUE_source03_BIG_shift_changes_SMALL_residue434
      z g k1 k2 ij.1 ij.2 q hq ha hb k hqk m t h hsame
  simp [hneq]

/-- The original log-cell source03 comparison kernel is supported
strictly OFF the congruence diagonal modulo any SMALL group prime.
This needs only the literal hOrigSmall and shift budget, NOT a
hypothetical construction of full SourceComparisonData from scratch. -/
theorem source_original_TRUE_source03_REAL_logcell_ANY_SMALL_congruence_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Option (Fin n)) (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (q : ℕ) (hq : q ∈ z.P g) (m t : ℤ)
    (hsame : (q:ℤ) ∣ t-m) :
    sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 k m t = 0 := by
  have hqk : ¬ q ∣ k.natAbs :=
    source_original_TRUE_source03_ANY_SMALL_exceeds_shift434
      z g q hq k hk hK hOrigSmall
  simpa only [sourceOriginalSource03RealLogCellKernel434] using
    source_original_TRUE_source03_BIG_two_box_SMALL_congruence_zero434
      z g k1 k2 F1 F2
      (sourceOriginalLogCellMask434 F1 U1 width1 b1)
      (sourceOriginalLogCellMask434 F2 U2 width2 b2)
      k q hq hqk m t hsame

/-- Uniform support exclusion for ALL true source03 SMALL primes:
the distinguished S and every moving Ts group. It applies to
the literal two-box K, not a factorized surrogate. -/
theorem source_original_TRUE_source03_REAL_logcell_ALL_SMALL_congruence_zero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (q : ℕ) (hq : q ∈ sourceOriginalSource03AllSmall434 z)
    (m t : ℤ) (hsame : (q:ℤ) ∣ t-m) :
    sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 k m t = 0 := by
  simp only [sourceOriginalSource03AllSmall434] at hq
  rcases Finset.mem_union.mp hq with hqS | hqTs
  · exact source_original_TRUE_source03_REAL_logcell_ANY_SMALL_congruence_zero434
      z none k1 k2 F1 F2 U1 U2 width1 width2 b1 b2
      k hk hK hOrigSmall q hqS m t hsame
  · obtain ⟨g, hg, hqg⟩ := Finset.mem_biUnion.mp hqTs
    exact source_original_TRUE_source03_REAL_logcell_ANY_SMALL_congruence_zero434
      z (some g) k1 k2 F1 F2 U1 U2 width1 width2 b1 b2
      k hk hK hOrigSmall q hqg m t hsame
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03AllSmallUnitShift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Original moving squarefree SMALL modulus formed from ALL real
source03 groups S and Ts, not the BIG groups. -/
noncomputable def sourceOriginalSource03SMALLModulus434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0) :
    ℕ :=
  (sourceOriginalSource03AllSmall434 z).prod id

/-- Genuine BIG product atoms shift by a residue UNIT modulo the
product of ALL SMALL primes. In particular, the arithmetic shift
avoids every coordinate hyperplane of the true SMALL residue torus. -/
theorem source_original_TRUE_source03_BIG_product_SMALL_modulus_coprime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (da db : ℕ)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db ≠ 0)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (k.natAbs*(da*db)) := by
  unfold sourceOriginalSource03SMALLModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro q hq
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hq
    rcases Finset.mem_union.mp hq with hS | hTs
    · exact ⟨none, hS⟩
    · obtain ⟨g, hg, hmem⟩ := Finset.mem_biUnion.mp hTs
      exact ⟨some g, hmem⟩
  obtain ⟨g, hqg⟩ := hgroups
  have hprime : q.Prime := (z.hSmallBand g q hqg).1
  apply (hprime.coprime_iff_not_dvd).2
  intro hdiv
  have hqk : ¬ q ∣ k.natAbs :=
    source_original_TRUE_source03_ANY_SMALL_exceeds_shift434
      z g q hqg k hk hK hOrigSmall
  rcases (hprime.dvd_mul).mp hdiv with hdk | hdab
  · exact hqk hdk
  rcases (hprime.dvd_mul).mp hdab with hda | hdb
  · exact (source_original_TRUE_source03_BIG_atom_avoids_any_SMALL434
      z g k1 da q hqg ha) hda
  · exact (source_original_TRUE_source03_BIG_atom_avoids_any_SMALL434
      z g k2 db q hqg hb) hdb

/-- For the LITERAL shifted source equation t=m+k*da*db,
the difference t-m is a unit modulo the FULL SMALL modulus.
This is a joint all-SMALL statement, not independent randomness. -/
theorem source_original_TRUE_source03_BIG_shift_SMALL_modulus_coprime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (da db : ℕ)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db ≠ 0)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (m t : ℤ) (hshift : t = m+k*(da:ℤ)*(db:ℤ)) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (t-m).natAbs := by
  have heq : t-m = k*(da:ℤ)*(db:ℤ) := by
    rw [hshift]
    ring
  have hAbs : (t-m).natAbs = k.natAbs*(da*db) := by
    rw [heq]
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    ring
  rw [hAbs]
  exact source_original_TRUE_source03_BIG_product_SMALL_modulus_coprime434
    z k1 k2 da db ha hb k hk hK hOrigSmall

/-- Support theorem for the COMPLETE genuine two-product kernel,
including any collisions or cancellations: every NONZERO output
has shift difference coprime to the product of all SMALL primes.
No assumption of pairwise independent chronological histories. -/
theorem source_original_TRUE_source03_BIG_two_box_only_SMALL_units434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (m t : ℤ)
    (hnonzero : sourceOriginalActualTwoBoxShiftKernel434 F1 F2
      (fun da => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig da : ℂ)*b1 da)
      (fun db => (sourceProductAtomMass
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig db : ℂ)*b2 db)
      k m t ≠ 0) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (t-m).natAbs := by
  by_contra hnot
  apply hnonzero
  unfold sourceOriginalActualTwoBoxShiftKernel434
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig ij.1 = 0
  · simp [ha]
  by_cases hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig ij.2 = 0
  · simp [hb]
  have hneq : t ≠ m + k*(ij.1:ℤ)*(ij.2:ℤ) := by
    intro h
    exact hnot (source_original_TRUE_source03_BIG_shift_SMALL_modulus_coprime434
      z k1 k2 ij.1 ij.2 ha hb k hk hK hOrigSmall m t h)
  simp [hneq]

/-- The genuine original two-log-cell comparison kernel itself
has SUPPORT only on units modulo the canonical total SMALL modulus.
It preserves both windows and their exact product-atom laws. -/
theorem source_original_TRUE_source03_REAL_logcell_only_SMALL_units434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (m t : ℤ)
    (hnonzero : sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 k m t ≠ 0) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (t-m).natAbs := by
  apply source_original_TRUE_source03_BIG_two_box_only_SMALL_units434
    z k1 k2 F1 F2
    (sourceOriginalLogCellMask434 F1 U1 width1 b1)
    (sourceOriginalLogCellMask434 F2 U2 width2 b2)
    k hk hK hOrigSmall m t
  simpa only [sourceOriginalSource03RealLogCellKernel434] using hnonzero

/-- Every genuine source03 four-sign endpoint channel restricts
EXACTLY to the unit shifts of the true full SMALL modulus.
The original common two-box K and both logarithmic-cell gates are
unchanged. This is support, NOT a character-RMS or Gram bound. -/
theorem source_original_TRUE_source03_REAL_logcell_four_sign_UNIT_support434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (k1 k2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (S T : Finset ℤ) (a b : ℤ → ℂ) :
    ∀ eps1 eps2 : Bool,
      let K := sourceOriginalSource03RealLogCellKernel434
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
        F1 F2 U1 U2 width1 width2 b1 b2 k
      sourceOriginalSignedBilinearKernel434 z.G S T a b
        K eps1 eps2 =
      sourceOriginalSignedBilinearKernel434 z.G S T a b
        (fun m t => if Nat.Coprime
          (sourceOriginalSource03SMALLModulus434 z) (t-m).natAbs
          then K m t else 0) eps1 eps2 := by
  intro eps1 eps2
  dsimp only
  unfold sourceOriginalSignedBilinearKernel434
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hunit : Nat.Coprime
      (sourceOriginalSource03SMALLModulus434 z) (t-m).natAbs
  · simp [hunit]
  · have hzero : sourceOriginalSource03RealLogCellKernel434
        (Finset.univ : Finset (Fin n)) z.Tb k1 z.Vbig
        (Finset.univ : Finset (Fin n)) z.Tb k2 z.Vbig
        F1 F2 U1 U2 width1 width2 b1 b2 k m t = 0 := by
      by_contra hn
      exact hunit (source_original_TRUE_source03_REAL_logcell_only_SMALL_units434
        z k1 k2 F1 F2 U1 U2 width1 width2 b1 b2
        k hk hK hOrigSmall m t hn)
    simp [hunit, hzero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalSmallBigFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- EXACT original chronological physical SMALL shared-mark factor.
No comparison BIG-only substitution is used. -/
noncomputable def sourceOriginalPhysicalSourceSMALLFactor434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ss : GroupPermFamily (G := SG) (J+ell)) : ℕ :=
  ∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
    sm g (marks (sm g) (J+ell) (x.1 g) (ss g j))
/-- EXACT physical shared-BIG and auxiliary free-BIG factor. -/
noncomputable def sourceOriginalPhysicalSourceBIGFactor434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell)) : ℕ :=
  ∏ g : BG,
    (∏ i ∈ sourceBigShared J ell m pat g,
      bm g ((x.2 g).1 (bs g i))) *
    (∏ j : ↥(pat.free g), bm g (aux g j))

/-- Literal sourceOrientedPhysicalD equals the physical shared
SMALL product times the full actual BIG/auxiliary product. -/
theorem source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell)) :
    sourceOrientedPhysicalD SP sm BP bm J ell m cap
      pat aux x bs ss =
    sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss *
    sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap pat aux x bs := by
  rfl

/-- All true S/Ts SMALL primes are disjoint from every true FULL
BIG interval, for the canonical source03 slice. -/
theorem source_original_TRUE_source03_ALL_SMALL_avoids_BIG_prime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (q r : ℕ) (hq : q ∈ sourceOriginalSource03AllSmall434 z)
    (i : Fin n) (hr : r ∈ z.Tb i) : ¬q ∣ r := by
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hq
    rcases Finset.mem_union.mp hq with hS | hTs
    · exact ⟨none,hS⟩
    · obtain ⟨g,hg,hmem⟩ := Finset.mem_biUnion.mp hTs
      exact ⟨some g,hmem⟩
  obtain ⟨g,hqg⟩ := hgroups
  have hp : q.Prime := (z.hSmallBand g q hqg).1
  have hrp : r.Prime := (z.hBigBand i r hr).1
  have hnot : q ∉ z.Tb i :=
    (Finset.disjoint_left.mp (z.hSB g i)) hqg
  intro hdvd
  have heq : q = r := (Nat.prime_dvd_prime_iff_eq hp hrp).1 hdvd
  exact hnot (heq ▸ hr)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalSMALLFiniteUpper -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- A finite physical (not independent) shared-SMALL source
product has at most J+ell factors PER genuine SMALL group.
For ANY prime carrier, no prime distinctness/mark independence
is necessary. This is a deterministic SOURCE E-divisor inequality. -/
theorem source_original_ACTUAL_PHYSICAL_SMALL_finite_upper434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)]
    [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ)
    [∀ g p, NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ)
    [∀ g p, NeZero (bm g p)]
    (J ell : ℕ) (cap : BG → ℕ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ss : GroupPermFamily (G := SG) (J+ell))
    (U : ℝ) (hU : 1 ≤ U)
    (hSm : ∀ g (p : SP g), (sm g p:ℝ) ≤ U) :
    ((sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss : ℕ):ℝ) ≤
        U^((J+ell)*Fintype.card SG) := by
  unfold sourceOriginalPhysicalSourceSMALLFactor434
  rw [Nat.cast_prod]
  calc
    (∏ g : SG,
      (((∏ j ∈ sourceSmallShared J ell g,
        sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)) : ℕ) : ℕ):ℝ)) ≤
      ∏ _g : SG, U^(J+ell) := by
        apply Finset.prod_le_prod₀
        · intro g hg
          exact Nat.cast_nonneg _
        · intro g hg
          have hgroup :
              (((∏ j ∈ sourceSmallShared J ell g,
                sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)) : ℕ):ℕ):ℝ) ≤
                U^((sourceSmallShared J ell g).card) := by
            rw [Nat.cast_prod]
            calc
              (∏ j ∈ sourceSmallShared J ell g,
                (sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)):ℝ)) ≤
                ∏ _j ∈ sourceSmallShared J ell g, U := by
                  apply Finset.prod_le_prod₀
                  · intro j hj
                    exact Nat.cast_nonneg _
                  · intro j hj
                    exact hSm g _
              _ = _ := by simp
          have hcard : (sourceSmallShared J ell g).card ≤ J+ell := by
            simpa using (Finset.card_le_card
              (Finset.subset_univ (sourceSmallShared J ell g)))
          exact hgroup.trans (pow_le_pow_right₀ hU hcard)
    _ = U^((J+ell)*Fintype.card SG) := by
      simp only [Finset.prod_const, Finset.card_univ, pow_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBigCoprime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- Every true BIG prime label in the original physical alphabet
is a unit against the product of ALL genuine source03 SMALL primes,
assuming the physical BIG alphabet is contained in true full Tb
prime intervals. For canonical subtype alphabets, this is automatic. -/
theorem source_original_TRUE_source03_ALL_SMALL_modulus_BIG_label_coprime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (r : ℕ) (hr : ∃ i : Fin n, r ∈ z.Tb i) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z) r := by
  unfold sourceOriginalSource03SMALLModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro q hq
  obtain ⟨i,hi⟩ := hr
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hq
    rcases Finset.mem_union.mp hq with hs | ht
    · exact ⟨none,hs⟩
    · obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp ht
      exact ⟨some g,hp⟩
  obtain ⟨g,hqg⟩ := hgroups
  have hp : q.Prime := (z.hSmallBand g q hqg).1
  apply (hp.coprime_iff_not_dvd).2
  exact source_original_TRUE_source03_ALL_SMALL_avoids_BIG_prime434
    z q r hq i hi
/-- The actual physical shared-BIG and auxiliary free-BIG product
is jointly coprime to the ENTIRE true canonical SMALL modulus.
The physical shared endpoints and auxiliary draws are not sampled
independently by this proof; each literal slot is retained. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_factor_coprime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell)) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOriginalPhysicalSourceBIGFactor434
        SP sm BP bm J ell m cap pat aux x bs) := by
  unfold sourceOriginalPhysicalSourceBIGFactor434
  apply (Nat.coprime_prod_right_iff).2
  intro g hg
  apply (Nat.coprime_mul_iff_right).2
  constructor
  · apply (Nat.coprime_prod_right_iff).2
    intro i hi
    exact source_original_TRUE_source03_ALL_SMALL_modulus_BIG_label_coprime434
      z _ (hbig g ((x.2 g).1 (bs g i)))
  · apply (Nat.coprime_prod_right_iff).2
    intro j hj
    exact source_original_TRUE_source03_ALL_SMALL_modulus_BIG_label_coprime434
      z _ (hbig g (aux g j))
/-- For EVERY true SMALL q, the ORIGINAL physical divisor D
contains q iff its actual shared-SMALL product contains q.
The complete BIG endpoint / auxiliary factor cannot create a
new SMALL divisor. Hence TRUE physical D and BIG-only K have
different local support, with no replacement of source D. -/
theorem source_original_TRUE_source03_PHYSICAL_D_SMALL_divisor_iff434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (q : ℕ) (hq : q ∈ sourceOriginalSource03AllSmall434 z) :
    q ∣ sourceOrientedPhysicalD SP sm BP bm J ell m cap
      pat aux x bs ss ↔
    q ∣ sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss := by
  have hqprime : q.Prime := by
    simp only [sourceOriginalSource03AllSmall434] at hq
    rcases Finset.mem_union.mp hq with hs | ht
    · exact (z.hSmallBand none q hs).1
    · obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp ht
      exact (z.hSmallBand (some g) q hp).1
  have hqBig : ¬ q ∣ sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap pat aux x bs := by
    intro hdiv
    have hcop := source_original_TRUE_source03_PHYSICAL_BIG_factor_coprime434
      SP sm BP bm J ell m cap z hbig pat aux x bs
    have hQdvd : q ∣ sourceOriginalSource03SMALLModulus434 z := by
      unfold sourceOriginalSource03SMALLModulus434
      exact Finset.dvd_prod_of_mem id hq
    have h : q ∣ Nat.gcd
        (sourceOriginalSource03SMALLModulus434 z)
        (sourceOriginalPhysicalSourceBIGFactor434
          SP sm BP bm J ell m cap pat aux x bs) :=
      Nat.dvd_gcd hQdvd hdiv
    rw [hcop.gcd_eq_one] at h
    exact hqprime.not_dvd_one h
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434]
  constructor
  · intro h
    rcases hqprime.dvd_mul.mp h with hs | hb
    · exact hs
    · exact False.elim (hqBig hb)
  · intro h
    exact dvd_mul_of_dvd_left h _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalBIGFiniteUpper -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- Finite NATURAL prime-label products have a uniform
power upper bound in the reals, even with repeated labels. -/
theorem source_original_ACTUAL_finite_nat_product_uniform_upper434
    {I : Type} [DecidableEq I] (s : Finset I)
    (f : I → ℕ) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ i ∈ s, (f i : ℝ) ≤ U) :
    (((∏ i ∈ s, f i : ℕ) : ℕ) : ℝ) ≤ U^s.card := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ s, (f i:ℝ)) ≤ ∏ _i ∈ s, U := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact Nat.cast_nonneg _
      · intro i hi; exact h i hi
    _ = _ := by simp

/-- Literal BIG endpoint-shared + FREE-AUXILIARY physical product
is at most U ^ ((2J+ell)*number of BIG groups), for any label
upper bound U>=1. No independence, distinctness, or positive
operator norm is assumed: this is an integer-factor inequality. -/
theorem source_original_ACTUAL_PHYSICAL_BIG_finite_upper434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (U : ℝ) (hU : 1 ≤ U)
    (hBig : ∀ g (p : BP g), (bm g p : ℝ) ≤ U) :
    ((sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap pat aux x bs : ℕ) : ℝ) ≤
      U^((2*J+ell)*Fintype.card BG) := by
  unfold sourceOriginalPhysicalSourceBIGFactor434
  rw [Nat.cast_prod]
  calc
    (∏ g : BG,
      (((∏ i ∈ sourceBigShared J ell m pat g,
          bm g ((x.2 g).1 (bs g i))) *
        (∏ j : ↥(pat.free g), bm g (aux g j)) : ℕ) : ℝ)) ≤
      ∏ _g : BG, U^(2*J+ell) := by
        apply Finset.prod_le_prod₀
        · intro g hg; exact Nat.cast_nonneg _
        · intro g hg
          have hShare := source_original_ACTUAL_finite_nat_product_uniform_upper434
            (sourceBigShared J ell m pat g)
            (fun i => bm g ((x.2 g).1 (bs g i))) U
            (le_trans (by norm_num) hU)
            (by intro i hi; exact hBig g _)
          have hShareC : (sourceBigShared J ell m pat g).card ≤ J+ell := by
            simpa using (Finset.card_le_card
              (Finset.subset_univ (sourceBigShared J ell m pat g)))
          have hShare' : (((∏ i ∈ sourceBigShared J ell m pat g,
                bm g ((x.2 g).1 (bs g i))) : ℕ):ℝ) ≤ U^(J+ell) :=
            hShare.trans (pow_le_pow_right₀ hU hShareC)
          have hAux := source_original_ACTUAL_finite_nat_product_uniform_upper434
            (Finset.univ : Finset ↥(pat.free g))
            (fun j => bm g (aux g j)) U
            (le_trans (by norm_num) hU)
            (by intro j hj; exact hBig g _)
          have hAuxC : Fintype.card ↥(pat.free g) ≤ J := by
            have hCard : (pat.free g).card ≤ J := by
              simpa only [Finset.card_univ, Fintype.card_fin] using
                (Finset.card_le_card (Finset.subset_univ (pat.free g)))
            simpa using hCard
          have hAux' : (((∏ j : ↥(pat.free g),
                bm g (aux g j) : ℕ):ℝ)) ≤ U^J :=
            hAux.trans (pow_le_pow_right₀ hU (by simpa using hAuxC))
          calc
            _ = (((∏ i ∈ sourceBigShared J ell m pat g,
                  bm g ((x.2 g).1 (bs g i))) : ℕ):ℝ) *
                (((∏ j : ↥(pat.free g), bm g (aux g j) : ℕ):ℝ)) := by
                  push_cast; rfl
            _ ≤ U^(J+ell) * U^J := by
              exact mul_le_mul hShare' hAux' (by positivity)
                (by positivity)
            _ = U^(2*J+ell) := by
              rw [←pow_add]
              congr 1; omega
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, pow_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceGEPhysicalCapRealUpper -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- ORIGINAL source03 full oriented physical divisor D is
uniformly bounded on the complete Fock×seen carrier by an
EXPLICIT polynomial power of the exact input-group prime cap
exp(sqrt L). This does not average RAW/comparison signed K and
does not substitute a BIG-only shift for the physical D. -/
theorem source_original_ACTUAL_SOURCE_true_full_D_real_upper434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell m : ℕ)
    (cap : β → ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern β J m)
    (X : FullPhysicalState
      (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g})
      (fun _ p => p.val)
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g})
      (fun _ p => p.val)
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) J ell m cap patterns X) :
    ((sourceOrientedPhysicalD
      (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g})
      (fun _ p => p.val)
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) J ell m cap
      (patterns ch.1) ch.2.1 X
      ch.2.2.1.sigmaBig ch.2.2.2.1 : ℕ) : ℝ) ≤
    (Real.exp (Real.sqrt L))^(
      ((J+ell)*Fintype.card (Option ι)) +
      ((2*J+ell)*Fintype.card β)) := by
  let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let U := Real.exp (Real.sqrt L)
  have hU : (1:ℝ) ≤ U :=
    Real.one_le_exp (Real.sqrt_nonneg L)
  have hSm : ∀ g : Option ι, ∀ p : SP g, (p.val:ℝ) ≤ U := by
    intro g p
    exact (source_original_ACTUAL_SMALL_source_bounds434 u).2.1 g
      p.val p.property
  have hBig : ∀ g : β, ∀ p : BP g, (p.val:ℝ) ≤ U := by
    intro g p
    apply u.hGroup p.val
    rw [source_original_full_groups_union434 u]
    exact Finset.mem_biUnion.mpr
      ⟨Sum.inr g, Finset.mem_univ _, p.property⟩
  have hSmall := source_original_ACTUAL_PHYSICAL_SMALL_finite_upper434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap X ch.2.2.2.1 U hU
    (by intro g p; exact hSm g p)
  have hBigBound := source_original_ACTUAL_PHYSICAL_BIG_finite_upper434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap (patterns ch.1) ch.2.1 X
    ch.2.2.1.sigmaBig U hU (by intro g p; exact hBig g p)
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434]
  change
    ((sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap X ch.2.2.2.1 *
      sourceOriginalPhysicalSourceBIGFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap (patterns ch.1) ch.2.1
      X ch.2.2.1.sigmaBig : ℕ) : ℝ) ≤ U^(
      ((J+ell)*Fintype.card (Option ι)) +
      ((2*J+ell)*Fintype.card β))
  calc
    _ = ((sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap X ch.2.2.2.1 : ℕ) : ℝ) *
      ((sourceOriginalPhysicalSourceBIGFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap (patterns ch.1) ch.2.1
      X ch.2.2.1.sigmaBig : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ U^((J+ell)*Fintype.card (Option ι)) *
      U^((2*J+ell)*Fintype.card β) :=
        mul_le_mul hSmall hBigBound
          (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [←pow_add]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceGEPhysicalCapExplicit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- UNCONDITIONAL true moving source03 physical divisor bound,
valid simultaneously for BOTH original orientations and ALL
finite reachable Fock×seen source states: the genuinely defined
Dmax does not exceed the EXPLICIT exp(sqrt L) source prime bound.
No infinity/sup over fictional histories, and no hGrowth assumed. -/
theorem source_original_ACTUAL_SOURCE_GE_true_divisor_cap_explicit434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (k : ℤ) :
    ((sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k : ℕ) : ℝ) ≤
    (Real.exp (Real.sqrt L))^(
      ((J+ell)*Fintype.card (Option ι))+
      ((2*J+ell)*Fintype.card β)) := by
  let SP := fun g : Option ι =>
    {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let U := (Real.exp (Real.sqrt L))^(
      ((J+ell)*Fintype.card (Option ι))+
      ((2*J+ell)*Fintype.card β))
  have hU : 0 ≤ U := by positivity
  have hD :
      ∀ (X : FullPhysicalState SP (fun _ p => p.val)
          BP (fun _ p => p.val) (J+ell) cap)
        (ch : FullOrientedSourceChoice SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell m cap patterns X),
        ((sourceOrientedPhysicalD
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap (patterns ch.1) ch.2.1 X
          ch.2.2.1.sigmaBig ch.2.2.2.1 : ℕ) : ℝ) ≤ U := by
    intro X ch
    exact source_original_ACTUAL_SOURCE_true_full_D_real_upper434
      u J ell m cap patterns X ch
  have hplus :=
    source_original_ACTUAL_GE_divisor_cap_real_le434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns 1 k U hU hD
  have hminus :=
    source_original_ACTUAL_GE_divisor_cap_real_le434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns (-1) k U hU hD
  change ((max
    (sourceOriginalActualGEDivisorCap434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns 1 k)
    (sourceOriginalActualGEDivisorCap434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns (-1) k) : ℕ) : ℝ) ≤ U
  simpa only [Nat.cast_max, max_le_iff] using And.intro hplus hminus
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalPhysicalBigFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Every actual canonical FULL Tb prime-subtype label is nonzero.
No external positivity premise for the original BIG alphabet. -/
instance sourceOriginalSource03CanonicalBigLabelNonzero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (i : Fin n) (p : {r : ℕ // r ∈ z.Tb i}) : NeZero p.val :=
  ⟨(z.hBigBand i p.val p.property).1.ne_zero⟩

/-- The complete original physical BIG product, with the TRUE
canonical source03 FULL Tb prime alphabets, is coprime to ALL
canonical S+Ts primes. Unlike the generic interface, there is
no assumed BIG-label support: it follows by subtype membership. -/
theorem source_original_TRUE_source03_CANONICAL_PHYSICAL_BIG_coprime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀g, Fintype (SP g)] [∀g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀g p, NeZero (sm g p)]
    (J ell m : ℕ)
    (pat : SourcePattern (Fin n) J m)
    (aux : SourceBigAux
      (fun i : Fin n => {r : ℕ // r ∈ z.Tb i}) J m pat)
    (x : FullPhysicalState SP sm
      (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
      (fun _ p => p.val) (J+ell)
      (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i}))
    (bs : BigGroupPerm (BG := Fin n) (J+ell)) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOriginalPhysicalSourceBIGFactor434
        SP sm (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
        (fun _ p => p.val) J ell m
        (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i})
        pat aux x bs) := by
  exact source_original_TRUE_source03_PHYSICAL_BIG_factor_coprime434
    SP sm (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
    (fun _ p => p.val) J ell m
    (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i})
    z (by intro i p; exact ⟨i,p.property⟩) pat aux x bs

/-- In the ORIGINAL canonical physical Fock alphabets, exact
SMALL-prime divisibility of D is determined by shared SMALL marks
alone; the genuine full BIG endpoint/auxiliary sector adds none.
No hbig label-support premise is needed for canonical subtype draws. -/
theorem source_original_TRUE_source03_CANONICAL_PHYSICAL_D_SMALL_iff434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀g, Fintype (SP g)] [∀g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀g p, NeZero (sm g p)]
    (J ell m : ℕ)
    (pat : SourcePattern (Fin n) J m)
    (aux : SourceBigAux
      (fun i : Fin n => {r : ℕ // r ∈ z.Tb i}) J m pat)
    (x : FullPhysicalState SP sm
      (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
      (fun _ p => p.val) (J+ell)
      (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i}))
    (bs : BigGroupPerm (BG := Fin n) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (q : ℕ) (hq : q ∈ sourceOriginalSource03AllSmall434 z) :
    q ∣ sourceOrientedPhysicalD SP sm
      (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
      (fun _ p => p.val) J ell m
      (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i})
      pat aux x bs ss ↔
    q ∣ sourceOriginalPhysicalSourceSMALLFactor434
      SP sm (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
      (fun _ p => p.val) J ell
      (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i})
      x ss := by
  exact source_original_TRUE_source03_PHYSICAL_D_SMALL_divisor_iff434
    SP sm (fun i : Fin n => {r : ℕ // r ∈ z.Tb i})
    (fun _ p => p.val) J ell m
    (fun i => Fintype.card {r : ℕ // r ∈ z.Tb i})
    z (by intro i p; exact ⟨i,p.property⟩) pat aux x bs ss q hq
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalSmallModulus -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
variable (SP : Option (Fin n) → Type)
variable [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : Option (Fin n)) → SP g → ℕ)
variable [∀ g p, NeZero (sm g p)]
variable (BP : Fin n → Type)
variable [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : Fin n) → BP g → ℕ)
variable [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : Fin n → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern (Fin n) J m)

/-- Exact canonical source03 physical Fock SMALL group prime typing.
The hypothesis states the actual SMALL labels inhabit their
corresponding prime groups; it is automatically satisfied by subtype
carriers {p // p in z.P g}, unlike a fabricated shared-prime event.

With J>0 EVERY original oriented physical source D has an authentic
shared SMALL prime q from S dividing it. Hence its gcd with the
product of all TRUE SMALL primes cannot be one. -/
theorem source_original_TRUE_source03_PHYSICAL_D_not_SMALL_unit434
    (hSmallTyped : ∀ g (p : SP g), sm g p ∈ z.P g)
    (hJ : 0 < J)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ch : FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) :
    ¬ Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1) := by
  let j : Fin (J+ell) := Fin.castAdd ell ⟨0,hJ⟩
  have hj : j ∈ sourceSmallShared J ell (none : Option (Fin n)) := by
    simpa [sourceSmallShared, j] using hJ
  let q := sm none (marks (sm none) (J+ell) (x.1 none)
    (ch.2.2.2.1 none j))
  have hq : q ∈ z.S := hSmallTyped none _
  have hqQ : q ∣ sourceOriginalSource03SMALLModulus434 z := by
    change q ∣ (sourceOriginalSource03AllSmall434 z).prod id
    apply Finset.dvd_prod_of_mem (fun p => p)
    exact Finset.mem_union.mpr (Or.inl hq)
  have hqD : q ∣ sourceOrientedPhysicalD SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1 :=
    source_original_ACTUAL_shared_SMALL_label_dvd_D434
      SP sm BP bm J ell m cap patterns x ch none j hj
  intro hcoprime
  have hqOne : q = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hqQ hqD
  exact (z.hSmallBand none q hq).1.ne_one hqOne

/-- ORIGINAL signed physical displacement o*k*D is NOT a unit
modulo the entire genuine source03 SMALL modulus when J>0.
In particular it lies in a NONUNIT arithmetic sector even for
nonzero moving k. No legal-orientation or independence assumption. -/
theorem source_original_TRUE_source03_PHYSICAL_step_not_SMALL_unit434
    (hSmallTyped : ∀ g (p : SP g), sm g p ∈ z.P g)
    (hJ : 0 < J)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ch : FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x)
    (o k : ℤ) :
    ¬ Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1
        o k).natAbs := by
  let j : Fin (J+ell) := Fin.castAdd ell ⟨0,hJ⟩
  have hj : j ∈ sourceSmallShared J ell (none : Option (Fin n)) := by
    simpa [sourceSmallShared, j] using hJ
  let q := sm none (marks (sm none) (J+ell) (x.1 none)
    (ch.2.2.2.1 none j))
  have hq : q ∈ z.S := hSmallTyped none _
  have hqQ : q ∣ sourceOriginalSource03SMALLModulus434 z := by
    change q ∣ (sourceOriginalSource03AllSmall434 z).prod id
    exact Finset.dvd_prod_of_mem (fun p => p)
      (Finset.mem_union.mpr (Or.inl hq))
  have hqStep : (q:ℤ) ∣ sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1
      o k :=
    source_original_ACTUAL_shared_SMALL_label_dvd_step434
      SP sm BP bm J ell m cap patterns x o k ch none j hj
  have hqNat : q ∣ (sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1
      o k).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hqStep)
  intro hcoprime
  have hOne : q=1 := Nat.eq_one_of_dvd_coprimes hcoprime hqQ hqNat
  exact (z.hSmallBand none q hq).1.ne_one hOne

/-- The complete original two-box BIG product-atom/log-cell kernel
vanishes at EVERY genuine physical source edge shift when J>0.
This is the exact SUPPORT MISMATCH between the purely BIG-based
comparison operator and the ORIGINAL shared-SMALL physical source;
it does not assert that the physical transition coefficient vanishes. -/
theorem source_original_TRUE_source03_BIG_kernel_at_PHYSICAL_step_zero434
    (hSmallTyped : ∀ g (p : SP g), sm g p ∈ z.P g)
    (hJ : 0 < J)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ch : FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x)
    (a1 a2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (κ : ℤ) (hκ : 0 < κ.natAbs)
    (hBudget : (κ.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (o k t : ℤ) :
    sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb a1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb a2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 κ
      t (t+sourceOrientedStep SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k) = 0 := by
  by_contra hnot
  have hunit := source_original_TRUE_source03_REAL_logcell_only_SMALL_units434
    z a1 a2 F1 F2 U1 U2 width1 width2 b1 b2
    κ hκ hBudget hOrigSmall t
    (t+sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
      ch.2.2.2.1 o k) hnot
  have hnonunit := source_original_TRUE_source03_PHYSICAL_step_not_SMALL_unit434
    z SP sm BP bm J ell m cap patterns hSmallTyped hJ x ch o k
  apply hnonunit
  simpa only [add_sub_cancel_left] using hunit
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalPhysicalNonunit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- The ACTUAL source03 canonical SMALL carrier: true primes
from S and all Ts, not a freely indexed model of prime labels. -/
abbrev sourceOriginalSource03CanonicalSmallCarrier434
    (g : Option (Fin n)) := {p : ℕ // p ∈ z.P g}

/-- The ACTUAL complete BIG prime interval carrier. -/
abbrev sourceOriginalSource03CanonicalBigCarrier434
    (g : Fin n) := {p : ℕ // p ∈ z.Tb g}

instance sourceOriginalSource03CanonicalSmallNeZero434
    (g : Option (Fin n))
    (p : sourceOriginalSource03CanonicalSmallCarrier434 z g) :
    NeZero p.val :=
  ⟨(z.hSmallBand g p.val p.property).1.ne_zero⟩

instance sourceOriginalSource03CanonicalBigNeZero434
    (g : Fin n)
    (p : sourceOriginalSource03CanonicalBigCarrier434 z g) :
    NeZero p.val :=
  ⟨(z.hBigBand g p.val p.property).1.ne_zero⟩

/-- Fully specialized physical source03 carrier; no external
SMALL-label-in-group assumption. For EVERY actual oriented source
physical choice, J>0 forces its signed Fourier step into the
NONUNIT sector of the true canonical SMALL prime modulus. -/
theorem source_original_TRUE_source03_CANONICAL_physical_step_nonunit434
    (J ell m : ℕ) (hJ : 0 < J) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (o k : ℤ) :
    ¬ Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOrientedStep
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k).natAbs := by
  exact source_original_TRUE_source03_PHYSICAL_step_not_SMALL_unit434
    z
    (sourceOriginalSource03CanonicalSmallCarrier434 z)
    (fun _ p => p.val)
    (sourceOriginalSource03CanonicalBigCarrier434 z)
    (fun _ p => p.val) J ell m cap patterns
    (fun _ p => p.property) hJ x ch o k

/-- Completely genuine canonical source03 no-go: the BIG-only
two-Fourier-box log-cell kernel is ZERO on the signed shift of
EVERY ACTUAL physical source edge (J>0). In particular an
unmodified BIG-only comparison kernel cannot represent the
original shared-SMALL D edge. This is NOT cancellation of the
physical Fock×seen signed history. -/
theorem source_original_TRUE_source03_CANONICAL_BIG_kernel_physical_zero434
    (J ell m : ℕ) (hJ : 0 < J) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (a1 a2 : Fin n → ℕ) (F1 F2 : Finset ℕ)
    (U1 U2 width1 width2 : ℝ) (b1 b2 : ℕ → ℂ)
    (κ : ℤ) (hκ : 0 < κ.natAbs)
    (hBudget : (κ.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (o k t : ℤ) :
    sourceOriginalSource03RealLogCellKernel434
      (Finset.univ : Finset (Fin n)) z.Tb a1 z.Vbig
      (Finset.univ : Finset (Fin n)) z.Tb a2 z.Vbig
      F1 F2 U1 U2 width1 width2 b1 b2 κ
      t (t+sourceOrientedStep
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k) = 0 := by
  exact source_original_TRUE_source03_BIG_kernel_at_PHYSICAL_step_zero434
    z
    (sourceOriginalSource03CanonicalSmallCarrier434 z)
    (fun _ p => p.val)
    (sourceOriginalSource03CanonicalBigCarrier434 z)
    (fun _ p => p.val) J ell m cap patterns
    (fun _ p => p.property) hJ x ch
    a1 a2 F1 F2 U1 U2 width1 width2 b1 b2
    κ hκ hBudget hOrigSmall o k t
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalCharacterZero -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- In the TRUE canonical source03 physical system, EVERY
Dirichlet character modulo the entire real SMALL prime product
vanishes on EVERY physical signed E displacement when J>0.
This is a structural obstruction to applying an unconditioned
multiplicative-character RMS in the FULL SMALL modulus:
physical E changes are NONUNITS, not equidistributed units. -/
theorem source_original_TRUE_source03_PHYSICAL_SMALL_character_zero434
    (J ell m : ℕ) (hJ : 0 < J) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (o k : ℤ)
    (χ : DirichletCharacter ℂ
      (sourceOriginalSource03SMALLModulus434 z)) :
    χ (sourceOrientedStep
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
      ch.2.2.2.1 o k : ℤ) = 0 := by
  have hnonunit :=
    source_original_TRUE_source03_CANONICAL_physical_step_nonunit434
      z J ell m hJ cap patterns x ch o k
  apply (DirichletCharacter.apply_eq_zero_iff χ _).2
  intro hcop
  apply hnonunit
  have hnat := (Int.isCoprime_iff_nat_coprime).mp hcop
  simpa only [Int.natAbs_natCast, Nat.coprime_comm] using hnat

/-- By contrast, EVERY genuine BIG-only two-product step
with two nonzero actual source03 product-atom weights is a UNIT
modulo Qsmall. Consequently EVERY Dirichlet character of this
same SMALL modulus is NONZERO on that shift.

This separates the physical first-DIRTY source from the bare
BIG x BIG two-box comparison at the character level. -/
theorem source_original_TRUE_source03_BIG_shift_SMALL_character_nonzero434
    (a1 a2 : Fin n → ℕ) (da db : ℕ)
    (ha : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb a1 z.Vbig da ≠ 0)
    (hb : sourceProductAtomMass
      (Finset.univ : Finset (Fin n)) z.Tb a2 z.Vbig db ≠ 0)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hBudget : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (χ : DirichletCharacter ℂ
      (sourceOriginalSource03SMALLModulus434 z)) :
    χ (k*(da:ℤ)*(db:ℤ) : ℤ) ≠ 0 := by
  have hcop := source_original_TRUE_source03_BIG_product_SMALL_modulus_coprime434
    z a1 a2 da db ha hb k hk hBudget hOrigSmall
  apply (DirichletCharacter.apply_ne_zero_iff χ _).2
  apply (Int.isCoprime_iff_nat_coprime).2
  have habs : (k*(da:ℤ)*(db:ℤ)).natAbs =
      k.natAbs*(da*db) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    ring
  simpa only [habs, Int.natAbs_natCast, Nat.coprime_comm] using hcop
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBigConditional -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open Green64SourceC6
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- Every actual BIG prime label has unit residue modulo
the product Qsmall of ALL actual source03 SMALL primes. -/
theorem source_original_TRUE_source03_Qsmall_coprime_BIG_prime434
    (g : Fin n) (p : sourceOriginalSource03CanonicalBigCarrier434 z g) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z) p.val := by
  unfold sourceOriginalSource03SMALLModulus434
  apply Nat.coprime_prod_left_iff.mpr
  intro q hq
  have hp : p.val.Prime := (z.hBigBand g p.val p.property).1
  have hpair : q.Prime ∧ q ≠ p.val := by
    simp only [sourceOriginalSource03AllSmall434] at hq
    rcases Finset.mem_union.mp hq with hqS | hqTs
    · refine ⟨(z.hSmallBand none q hqS).1, ?_⟩
      intro heq
      exact (Finset.disjoint_left.mp (z.hSB none g))
        hqS (heq ▸ p.property)
    · obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqTs
      refine ⟨(z.hSmallBand (some i) q hqi).1, ?_⟩
      intro heq
      exact (Finset.disjoint_left.mp (z.hSB (some i) g))
        hqi (heq ▸ p.property)
  exact (Nat.coprime_primes hpair.1 hp).mpr hpair.2

/-- The ACTUAL oriented source BIG-factor of the physical divisor:
all permuted BIG shared marks plus genuine free BIG auxiliary draws.
Unlike a surrogate atom law, the complete chronological BIG labels
are kept, including the fact that auxiliary primes may repeat. -/
noncomputable def sourceOriginalSource03CanonicalPhysicalBIGFactor434
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) : ℕ :=
  ∏ g : Fin n,
    (∏ i ∈ sourceBigShared J ell m (patterns ch.1) g,
       ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val) *
    (∏ j : ↥((patterns ch.1).free g), (ch.2.1 g j).val)

/-- The true physical BIG factor stays in the multiplicative
UNIT group modulo Qsmall, for ANY oriented SMALL/BIG state and
ANY permitted original free-particle pattern; no assumption on
independence of two arithmetic windows or on signed weights. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_factor_SMALL_unit434
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) :
    Nat.Coprime (sourceOriginalSource03SMALLModulus434 z)
      (sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch) := by
  unfold sourceOriginalSource03CanonicalPhysicalBIGFactor434
  apply Nat.coprime_prod_right_iff.mpr
  intro g hg
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    exact source_original_TRUE_source03_Qsmall_coprime_BIG_prime434
      z g ((x.2 g).1 (ch.2.2.1.sigmaBig g i))
  · apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    exact source_original_TRUE_source03_Qsmall_coprime_BIG_prime434
      z g (ch.2.1 g j)

/-- The REAL SMALL part of physical D with ALL source permuted
shared marks, rather than a fixed independently drawn prime list. -/
noncomputable def sourceOriginalSource03CanonicalPhysicalSMALLFactor434
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) : ℕ :=
  ∏ g : Option (Fin n),
    ∏ i ∈ sourceSmallShared J ell g,
      (marks (fun p : sourceOriginalSource03CanonicalSmallCarrier434 z g => p.val)
        (J+ell) (x.1 g) (ch.2.2.2.1 g i)).val
/-- TRUE exact oriented physical D factorization, preserving
the literal two SMALL/BIG endpoint permutations and ALL free
auxiliary BIG prime draws. This equality is definitional. -/
theorem source_original_TRUE_source03_PHYSICAL_D_SMALL_times_BIG434
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) :
    sourceOrientedPhysicalD
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
      ch.2.2.2.1 =
    sourceOriginalSource03CanonicalPhysicalSMALLFactor434
      z J ell m cap patterns x ch *
    sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch := by
  rfl
/-- Conditioning on the actual shared SMALL marks exposes a
NONVANISHING arithmetic BIG character observable. Unlike χ(D),
which is identically zero for J>0, χ(Dbig) is nonzero for ANY
Dirichlet character mod the complete canonical SMALL modulus.
This does not bound its mean square over the physical Fock states. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_character_nonzero434
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (χ : DirichletCharacter ℂ
      (sourceOriginalSource03SMALLModulus434 z)) :
    χ (sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch : ℤ) ≠ 0 := by
  have hcop :=
    source_original_TRUE_source03_PHYSICAL_BIG_factor_SMALL_unit434
      z J ell m cap patterns x ch
  apply (DirichletCharacter.apply_ne_zero_iff χ _).2
  apply (Int.isCoprime_iff_nat_coprime).2
  simpa only [Int.natAbs_natCast, Nat.coprime_comm] using hcop
end Green64Analytic.CorrelationSquare

end

end

