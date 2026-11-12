module

public import Green64.Library.Correlation.Part053
public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part017

@[expose] public section

/-!
# Weights / Part069

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedDIRTYEnergySum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The FULL time-aggregated inverse-mass energy of the TRUE signed
CLEAN prefix, transported on one Fock×chronological-seen carrier. -/
def sourceOriginalSignedPrefixEnergySum434 {H : Type} [Fintype H]
    (C : ℕ → H → H → ℂ) (π : H → ℝ)
    (n start : ℕ) (w : H → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, sourceOriginalSignedJointInverseEnergy434 π
    (sourceOriginalSignedForwardPrefix434 C j start w)

/-- The full chronological DIRTY insertion output energy against the
SAME mass and state at which the CLEAN prefix is paired. -/
def sourceOriginalSignedDIRTYTargetEnergySum434 {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (π : H → ℝ)
    (n start : ℕ) (f : H → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, sourceOriginalSignedJointForwardEnergy434 π
    (sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f))

theorem source_original_SIGNED_DIRTY_pairing_energy_CS434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (π : H → ℝ)
    (hπ : ∀ a, 0 < π a) (n start : ℕ) (w f : H → ℂ) :
    ‖∑ j ∈ Finset.range n, ∑ b : H,
      sourceOriginalSignedForwardPrefix434 C j start w b *
      sourceOriginalSignedMatrixAction434 (D (start+j))
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D)
          (n-(j+1)) (start+j+1) f) b‖ ≤
    Real.sqrt (sourceOriginalSignedPrefixEnergySum434 C π n start w) *
    Real.sqrt (sourceOriginalSignedDIRTYTargetEnergySum434 C D π n start f) := by
  classical
  let W : ℕ → H → ℂ := fun j =>
    sourceOriginalSignedForwardPrefix434 C j start w
  let G : ℕ → H → ℂ := fun j =>
    sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f)
  let P : ℕ → ℝ := fun j => sourceOriginalSignedJointInverseEnergy434 π (W j)
  let Q : ℕ → ℝ := fun j => sourceOriginalSignedJointForwardEnergy434 π (G j)
  have hP (j : ℕ) : 0 ≤ P j := by
    unfold P sourceOriginalSignedJointInverseEnergy434
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ (j : ℕ) : 0 ≤ Q j := by
    unfold Q sourceOriginalSignedJointForwardEnergy434
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hLocal (j : ℕ) :
      ‖∑ b : H, W j b * G j b‖ ≤ Real.sqrt (P j) * Real.sqrt (Q j) := by
    exact source_original_SIGNED_joint_weighted_CS434 π hπ (W j) (G j)
  have hSqP :
      (∑ j ∈ Finset.range n, (Real.sqrt (P j))^2) =
      ∑ j ∈ Finset.range n, P j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (hP j)
  have hSqQ :
      (∑ j ∈ Finset.range n, (Real.sqrt (Q j))^2) =
      ∑ j ∈ Finset.range n, Q j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (hQ j)
  have hReal :
      (∑ j ∈ Finset.range n, Real.sqrt (P j) * Real.sqrt (Q j)) ≤
      Real.sqrt (∑ j ∈ Finset.range n, P j) *
        Real.sqrt (∑ j ∈ Finset.range n, Q j) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.range n) (fun j => Real.sqrt (P j)) (fun j => Real.sqrt (Q j))
    rw [hSqP,hSqQ] at h
    exact h
  change ‖∑ j ∈ Finset.range n, ∑ b : H,W j b * G j b‖ ≤
      Real.sqrt (∑ j ∈ Finset.range n, P j) *
      Real.sqrt (∑ j ∈ Finset.range n, Q j)
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖∑ b : H,W j b * G j b‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, Real.sqrt (P j) * Real.sqrt (Q j) :=
      Finset.sum_le_sum (fun j _ => hLocal j)
    _ ≤ _ := hReal
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPrefixSchurChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact finite Schur growth factor of ONE signed original
joint Fock×seen CLEAN matrix, without an independent norm premise. -/
def sourceOriginalSignedOneStepSchurGain434
    {H : Type} [Fintype H] (π : H → ℝ) (M : H → H → ℂ) : ℝ :=
  sourceOriginalSignedColumnSchurMax434 π M *
    sourceOriginalSignedRowSchurMax434 M

theorem source_original_SIGNED_one_step_Schur_gain_nonneg434
    {H : Type} [Fintype H] (π : H → ℝ) (M : H → H → ℂ) :
    0 ≤ sourceOriginalSignedOneStepSchurGain434 π M :=
  mul_nonneg (source_original_SIGNED_column_Schur_max_nonneg434 π M)
    (source_original_SIGNED_row_Schur_max_nonneg434 M)

/-- Chronological product of the TRUE per-visit Schur constants,
with no extra history-cardinality or guessed exponential factor. -/
def sourceOriginalSignedPrefixSchurGainChain434
    {H : Type} [Fintype H] (C : ℕ → H → H → ℂ)
    (π : H → ℝ) : (n start : ℕ) → ℝ
  | 0,_ => 1
  | n+1,start =>
      sourceOriginalSignedOneStepSchurGain434 π (C start) *
        sourceOriginalSignedPrefixSchurGainChain434 C π n (start+1)

theorem source_original_SIGNED_prefix_Schur_gain_chain_nonneg434
    {H : Type} [Fintype H] (C : ℕ → H → H → ℂ)
    (π : H → ℝ) (n start : ℕ) :
    0 ≤ sourceOriginalSignedPrefixSchurGainChain434 C π n start := by
  induction n generalizing start with
  | zero =>
      simp only [sourceOriginalSignedPrefixSchurGainChain434]
      norm_num
  | succ n ih =>
      change 0 ≤ sourceOriginalSignedOneStepSchurGain434 π (C start) *
        sourceOriginalSignedPrefixSchurGainChain434 C π n (start+1)
      exact mul_nonneg
        (source_original_SIGNED_one_step_Schur_gain_nonneg434 π (C start))
        (ih (start+1))

/-- TRUE original signed cumulative CLEAN-prefix weighted energy
propagates by the EXACT product of finite Fock×seen Schur gains.
No hContraction assumption is introduced; the whole unsimplified
physical operator cost is displayed explicitly in the RHS. -/
theorem source_original_SIGNED_prefix_exact_Schur_chain434
    {H : Type} [Fintype H] (C : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (w : H → ℂ) :
    sourceOriginalSignedJointInverseEnergy434 π
      (sourceOriginalSignedForwardPrefix434 C n start w) ≤
    sourceOriginalSignedPrefixSchurGainChain434 C π n start *
      sourceOriginalSignedJointInverseEnergy434 π w := by
  induction n generalizing start w with
  | zero =>
      simp only [sourceOriginalSignedForwardPrefix434,
        sourceOriginalSignedPrefixSchurGainChain434,one_mul,le_refl]
  | succ n ih =>
      let w' := sourceOriginalSignedPrefixTranspose434 (C start) w
      let G := sourceOriginalSignedOneStepSchurGain434 π (C start)
      let GTail := sourceOriginalSignedPrefixSchurGainChain434 C π n (start+1)
      have hStep :
          sourceOriginalSignedJointInverseEnergy434 π w' ≤
          G * sourceOriginalSignedJointInverseEnergy434 π w :=
        source_original_SIGNED_prefix_exact_Schur434 π hπ (C start) w
      have hTail : 0 ≤ GTail :=
        source_original_SIGNED_prefix_Schur_gain_chain_nonneg434 C π n (start+1)
      change sourceOriginalSignedJointInverseEnergy434 π
        (sourceOriginalSignedForwardPrefix434 C n (start+1) w') ≤
        (G * GTail) * sourceOriginalSignedJointInverseEnergy434 π w
      calc
        _ ≤ GTail * sourceOriginalSignedJointInverseEnergy434 π w' :=
          ih (start+1) w'
        _ ≤ GTail * (G * sourceOriginalSignedJointInverseEnergy434 π w) :=
          mul_le_mul_of_nonneg_left hStep hTail
        _ = _ := by ring

/-- Explicit time-AGGREGATED prefix-energy upper budget. No new
hEnergy or smallness premise; the only cost is the SUM OF ACTUAL
prefix Schur products on the same Fock×seen joint state. -/
theorem source_original_SIGNED_prefix_energy_sum_Schur434
    {H : Type} [Fintype H] (C : ℕ → H → H → ℂ)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (w : H → ℂ) :
    sourceOriginalSignedPrefixEnergySum434 C π n start w ≤
    (∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start) *
    sourceOriginalSignedJointInverseEnergy434 π w := by
  unfold sourceOriginalSignedPrefixEnergySum434
  calc
    _ ≤ ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
        sourceOriginalSignedJointInverseEnergy434 π w := by
        apply Finset.sum_le_sum
        intro j hj
        exact source_original_SIGNED_prefix_exact_Schur_chain434 C π hπ
          j start w
    _ = _ := (Finset.sum_mul ..).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedForwardDIRTYSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- FINITE genuine complex Fock×seen Hilbert Minkowski/CS bound:
the ORIGINAL weighted forward-energy of a sum of signed
state-valued amplitudes costs ONLY the number of insertion
positions, not the number of physical state or seen histories.
Each state contributes a complex sum BEFORE taking its square. -/
theorem source_original_SIGNED_forward_finite_square_sum434
    {H I : Type} [Fintype H]
    (π : H → ℝ) (hπ : ∀ a, 0 ≤ π a)
    (F : Finset I) (v : I → H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (fun a => ∑ j ∈ F, v j a) ≤
    (F.card:ℝ) * ∑ j ∈ F,
      sourceOriginalSignedJointForwardEnergy434 π (v j) := by
  classical
  have hLoc (a : H) :
      ‖∑ j ∈ F, v j a‖^2 ≤
        (F.card:ℝ)*∑ j ∈ F, ‖v j a‖^2 := by
    have hh := source_original_finite_complex_sum_normSq_le_card434
      F (fun j => v j a)
    simpa only [Complex.normSq_eq_norm_sq] using hh
  have hEq1 := source_original_SIGNED_forward_energy_as_sum434
    π hπ (fun a => ∑ j ∈ F, v j a)
  rw [hEq1]
  have hR (j : I) := source_original_SIGNED_forward_energy_as_sum434
    π hπ (v j)
  simp_rw [hR]
  calc
    (∑ a : H, π a*‖∑ j ∈ F, v j a‖^2) ≤
        ∑ a : H, π a*((F.card:ℝ)*∑ j ∈ F,‖v j a‖^2) :=
      Finset.sum_le_sum (fun a ha =>
        mul_le_mul_of_nonneg_left (hLoc a) (hπ a))
    _ = ∑ a : H, ∑ j ∈ F,
        (F.card:ℝ) * (π a * ‖v j a‖^2) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = (F.card:ℝ) * (π a * (∑ j ∈ F, ‖v j a‖^2)) := by ring
        _ = (F.card:ℝ) * (∑ j ∈ F, π a * ‖v j a‖^2) := by
          rw [Finset.mul_sum]
        _ = (∑ j ∈ F, (F.card:ℝ) * (π a * ‖v j a‖^2)) := by
          rw [Finset.mul_sum]
    _ = ∑ j ∈ F, ∑ a : H,
        (F.card:ℝ) * (π a * ‖v j a‖^2) := by
      rw [Finset.sum_comm]
    _ = (F.card:ℝ) * ∑ j ∈ F,
        ∑ a : H,π a*‖v j a‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]

/-- Forward (not transpose) TRUE finite signed CLEAN Fock×seen
matrix chain energy has the same explicit product of REAL
Schur row/column maxima as the dual-prefix bound.
No abstract contraction, Markovness or history independence. -/
theorem source_original_SIGNED_forward_chain_exact_Schur434
    {H : Type} [Fintype H]
    (C : ℕ → H → H → ℂ) (π : H → ℝ)
    (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (sourceOriginalSignedMatrixChain434 C n start f) ≤
    sourceOriginalSignedPrefixSchurGainChain434 C π n start *
      sourceOriginalSignedJointForwardEnergy434 π f := by
  induction n generalizing start f with
  | zero =>
      simp [sourceOriginalSignedMatrixChain434,
        sourceOriginalSignedPrefixSchurGainChain434]
  | succ n ih =>
      let tail := sourceOriginalSignedMatrixChain434 C n (start+1) f
      let g := sourceOriginalSignedOneStepSchurGain434 π (C start)
      let rest := sourceOriginalSignedPrefixSchurGainChain434 C π n (start+1)
      have hStep :
          sourceOriginalSignedJointForwardEnergy434 π
            (sourceOriginalSignedMatrixAction434 (C start) tail) ≤
          g * sourceOriginalSignedJointForwardEnergy434 π tail := by
        simpa only [sourceOriginalSignedOneStepSchurGain434, g,
          mul_comm, mul_left_comm, mul_assoc] using
          (source_original_SIGNED_forward_exact_Schur434
            π hπ (C start) tail)
      have hTail :
          sourceOriginalSignedJointForwardEnergy434 π tail ≤
          rest * sourceOriginalSignedJointForwardEnergy434 π f :=
        ih (start+1) f
      have hg : 0 ≤ g :=
        source_original_SIGNED_one_step_Schur_gain_nonneg434 π (C start)
      change sourceOriginalSignedJointForwardEnergy434 π
        (sourceOriginalSignedMatrixAction434 (C start) tail) ≤
        (g*rest)*sourceOriginalSignedJointForwardEnergy434 π f
      calc
        _ ≤ g*sourceOriginalSignedJointForwardEnergy434 π tail := hStep
        _ ≤ g*(rest*sourceOriginalSignedJointForwardEnergy434 π f) :=
          mul_le_mul_of_nonneg_left hTail hg
        _ = _ := by ring
/-- KEY new matrix-energy interface: ORIGINAL signed
first-DIRTY chronological forward Fock×seen Hilbert energy
is controlled by the sum of GENUINE ONE-DIRTY-AT-j local
target energies multiplied by genuine prefix Schur products.
ONLY polynomial insertion-count factor n is paid.
No state/history/Fourier-channel cardinality, no comparison
K-independence, and NO unexplained global energy assumption.
The local DIRTY target energies remain to be bounded for the
actual FULL signed suffix; this is not a log saving itself. -/
theorem source_original_SIGNED_DIRTY_forward_positions_Schur434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (π : H → ℝ)
    (hπ : ∀ a, 0 < π a)
    (n start : ℕ) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (sourceOriginalSignedMatrixDirtyChain434 C D n start f) ≤
    (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
        sourceOriginalSignedJointForwardEnergy434 π
          (sourceOriginalSignedMatrixAction434 (D (start+j))
            (sourceOriginalSignedMatrixChain434
              (sourceOriginalSignedKernelAdd434 C D)
              (n-(j+1)) (start+j+1) f)) := by
  classical
  let E (j : ℕ) : H → ℂ :=
    sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        (n-(j+1)) (start+j+1) f)
  let V (j : ℕ) : H → ℂ :=
    sourceOriginalSignedMatrixAt434 C D j (n-(j+1)) start f
  have hPath : sourceOriginalSignedMatrixDirtyChain434 C D n start f =
      fun a => ∑ j ∈ Finset.range n,V j a := by
    funext a
    exact source_original_signed_matrix_dirty_positions434 C D n start f a
  have hSchur (j : ℕ) :
      sourceOriginalSignedJointForwardEnergy434 π (V j) ≤
        sourceOriginalSignedPrefixSchurGainChain434 C π j start *
          sourceOriginalSignedJointForwardEnergy434 π (E j) := by
    exact source_original_SIGNED_forward_chain_exact_Schur434
      C π hπ j start (E j)
  have hSum := Finset.sum_le_sum
    (s := Finset.range n)
    (fun j hj => hSchur j)
  rw [hPath]
  have hSquare := source_original_SIGNED_forward_finite_square_sum434
    π (fun a => (hπ a).le) (Finset.range n) V
  change sourceOriginalSignedJointForwardEnergy434 π
      (fun a => ∑ j ∈ Finset.range n, V j a) ≤
    (n:ℝ) * ∑ j ∈ Finset.range n,
      sourceOriginalSignedPrefixSchurGainChain434 C π j start *
      sourceOriginalSignedJointForwardEnergy434 π (E j)
  calc
    _ ≤ ((Finset.range n).card:ℝ) *
        ∑ j ∈ Finset.range n,
          sourceOriginalSignedJointForwardEnergy434 π (V j) := hSquare
    _ ≤ ((Finset.range n).card:ℝ) *
        ∑ j ∈ Finset.range n,
          sourceOriginalSignedPrefixSchurGainChain434 C π j start *
          sourceOriginalSignedJointForwardEnergy434 π (E j) :=
          mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg _)
    _ = _ := by simp
end Green64Analytic.CorrelationSquare

end

end

