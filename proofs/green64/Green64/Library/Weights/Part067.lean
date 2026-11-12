module

public import Green64.Library.Weights.Part066
public import Green64.Library.Weights.ActualSignedGhostMatrix
public import Green64.Library.Correlation.Part052
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part059

@[expose] public section

/-!
# Weights / Part067

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedHistoryDelta -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap


/-- Exact BASIS expansion on the genuine reachable Fock×seen carrier,
including zero outside the carrier. No summation over arbitrary
independently redrawn chronological histories. -/
theorem source_original_ACTUAL_signed_history_lift_delta434
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out seen =
    ∑ b : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap,
      f b * sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
        (sourceOriginalSignedFiniteDelta434 b) out seen := by
  classical
  by_cases h : (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap
  · simp only [sourceOriginalActualSignedHistoryLift434,dif_pos h]
    let z : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap :=
      ⟨(out,seen),h⟩
    exact ((congrFun (source_original_signed_finite_delta_expand434 f) z)).symm
  · simp [sourceOriginalActualSignedHistoryLift434,h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedHistoryWeightedDelta -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- A literal signed physical branch coefficient distributes across
the reachable Fock×chronological-history basis, including zero off it. -/
theorem source_original_ACTUAL_signed_weighted_delta434
    (c : ℂ) (f : H → ℂ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    c * sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out seen =
    ∑ b : H, (c * sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalSignedFiniteDelta434 b) out seen) * f b := by
  classical
  rw [source_original_ACTUAL_signed_history_lift_delta434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEFrameDelta -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- A SINGLE actual E-frame witness term, including its original
admissibility, unique OLD injection, CLEAN/DIRTY predicate and
full complex coefficient, for a finite-history terminal test. -/
def sourceOriginalActualSignedEFrameTerm434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : H → ℂ) : ℂ :=
  if h : ∃ w : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns
        x seen o k r w then
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns
      x r (Classical.choose h)
    if keep x z then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z *
      sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0
  else 0

/-- Weighted basis expansion of EACH true E-frame witness: neither
the admissible OLD injection nor the complex coefficient is changed. -/
theorem source_original_ACTUAL_signed_E_frame_term_delta434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : H → ℂ) :
    sourceOriginalActualSignedEFrameTerm434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen r f =
    ∑ b : H,
      sourceOriginalActualSignedEFrameTerm434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k x seen r
        (sourceOriginalSignedFiniteDelta434 b) * f b := by
  classical
  unfold sourceOriginalActualSignedEFrameTerm434
  by_cases h : ∃ w : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns
        x seen o k r w
  · simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns
      x r (Classical.choose h)
    let c := sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z
    let out := sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z
    let st := seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset
    change (if keep x z then c *
      sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out st else 0) =
      ∑ b : H, (if keep x z then c *
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
          (sourceOriginalSignedFiniteDelta434 b) out st else 0) * f b
    by_cases hk : keep x z
    · simp only [if_pos hk]
      exact source_original_ACTUAL_signed_weighted_delta434
        SP sm BP bm J ell cap c f out st
    · simp only [if_neg hk,zero_mul,Finset.sum_const_zero]
  · simp only [dif_neg h,zero_mul,Finset.sum_const_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEMatrixDirect -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Finite REAL source E-frame matrix identity proved directly,
one admissible signed frame witness at a time. The proof avoids
expanding a generic abstract operator across the entire Fock state. -/
theorem source_original_ACTUAL_signed_E_matrix_direct434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (f : H → ℂ) (a : H) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k f a =
    ∑ b : H, sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k a b * f b := by
  classical
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  let seen := a.val.2
  let Row : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns →
      (H → ℂ) → ℂ :=
    fun r g => sourceOriginalActualSignedEFrameTerm434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen r g
  change (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
    Row r f) = ∑ b : H, (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
    Row r (sourceOriginalSignedFiniteDelta434 b)) * f b
  calc
    _ = ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        ∑ b : H, Row r (sourceOriginalSignedFiniteDelta434 b) * f b := by
      apply Finset.sum_congr rfl
      intro r hr
      exact source_original_ACTUAL_signed_E_frame_term_delta434
        SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
        zeta theta o k x seen r f
    _ = ∑ b : H, ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        Row r (sourceOriginalSignedFiniteDelta434 b) * f b := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEMatrixPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Physical signed E-frame, including its true reachable Fock
canonical representative, equals the finite signed matrix action. -/
theorem source_original_ACTUAL_original_E_matrix_exact434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
      a.val.2 F =
    ∑ b : H, sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k a b * F b.val.1 b.val.2 := by
  calc
    _ = sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k
        (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
        a := source_original_ACTUAL_signed_finite_E_exact434
          SP sm BP bm J ell m cap patterns hcap
          keep q rho Vs V mu K zeta theta o k F a
    _ = _ := source_original_ACTUAL_signed_E_matrix_direct434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F) a
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedMatrixProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Row-first product of two genuine complex kernels on any finite
carrier. Later instantiation uses full Fock output and cumulative seen. -/
def sourceOriginalSignedMatrixProduct434
    {H : Type} [Fintype H] (G E : H → H → ℂ) (a c : H) : ℂ :=
  ∑ b : H, G a b * E b c

/-- Associativity of the finite signed row-first matrix action.
No operator norm, positivity, Markov assumption or history maximum. -/
theorem source_original_signed_matrix_product_apply434
    {H : Type} [Fintype H]
    (G E : H → H → ℂ) (f : H → ℂ) (a : H) :
    (∑ b : H, G a b * (∑ c : H, E b c * f c)) =
    ∑ c : H, sourceOriginalSignedMatrixProduct434 G E a c * f c := by
  classical
  calc
    _ = ∑ b : H, ∑ c : H, (G a b * E b c) * f c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ c : H, ∑ b : H, (G a b * E b c) * f c := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [sourceOriginalSignedMatrixProduct434,Finset.sum_mul]

/-- Exact signed forward-prefix/backward-suffix pairing under two
consecutive genuine kernels on the SAME finite state carrier. -/
theorem source_original_signed_matrix_product_pairing434
    {H : Type} [Fintype H]
    (G E : H → H → ℂ) (w f : H → ℂ) :
    (∑ a : H, w a * (∑ b : H, G a b * (∑ c : H, E b c * f c))) =
    ∑ c : H, (∑ b : H, (∑ a : H, w a * G a b) * E b c) * f c := by
  classical
  calc
    _ = ∑ a : H, ∑ b : H, (w a * G a b) * (∑ c : H, E b c * f c) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ b : H, (∑ a : H, w a * G a b) * (∑ c : H, E b c * f c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
    _ = ∑ b : H, ∑ c : H,
        ((∑ a : H, w a * G a b) * E b c) * f c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedOLDMaskedEMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE TOTAL OLD ≤ T Fock projector on a joint output/history
state. The history component remains unchanged and is never reset. -/
def sourceOriginalActualSignedOLDGate434 (T : ℕ) (a : H) : Prop :=
  (∑ g : BG,(a.val.1.2 g).2.card) ≤ T

/-- Both actual OLD endpoint masks P_T E P_T retained on the literal
finite COMPLEX E matrix; the original CLEAN/DIRTY keep is unchanged. -/
def sourceOriginalActualSignedOLDMaskedEMatrix434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ) (a b : H) : ℂ :=
  if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a then
    if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b then
      sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k a b
    else 0
  else 0

/-- Genuine finite projected E action on reachable joint history
states, with both total-OLD gates and complete source signs. -/
def sourceOriginalActualSignedOLDMaskedFiniteE434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ) (f : H → ℂ) (a : H) : ℂ :=
  if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a then
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k
      (fun b => if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b then
        f b else 0) a
  else 0

/-- Literal finite projected E is EXACTLY the complex matrix with
OLD≤T projector at BOTH actual endpoints, not an auxiliary bound. -/
theorem source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ) (f : H → ℂ) (a : H) :
    sourceOriginalActualSignedOLDMaskedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k T f a =
    ∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T a b * f b := by
  classical
  unfold sourceOriginalActualSignedOLDMaskedFiniteE434
  by_cases ha : sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a
  · simp only [if_pos ha]
    rw [source_original_ACTUAL_signed_E_matrix_direct434]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b
    · simp only [if_pos hb,sourceOriginalActualSignedOLDMaskedEMatrix434,
        if_pos ha]
    · simp only [if_neg hb,sourceOriginalActualSignedOLDMaskedEMatrix434,
        if_pos ha,mul_zero,zero_mul]
  · simp only [if_neg ha,sourceOriginalActualSignedOLDMaskedEMatrix434,
      zero_mul,Finset.sum_const_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedOLDMaskedEPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Actual P_T E_keep P_T signed Fock×seen prefix/suffix bilinear
pairing, including BOTH total OLD projectors and all complex signs.
The prefix is moved by the true matrix transpose; no history reset. -/
theorem source_original_ACTUAL_signed_OLD_E_prefix_suffix_pairing434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (T : ℕ) (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalActualSignedOLDMaskedFiniteE434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T f a) =
    ∑ b : H, (∑ a : H, w a *
      sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T a b) * f b := by
  classical
  let E := sourceOriginalActualSignedOLDMaskedEMatrix434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k T
  calc
    _ = ∑ a : H, w a * (∑ b : H,E a b*f b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434]
    _ = ∑ a : H, ∑ b : H,(w a * E a b) * f b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ b : H, ∑ a : H,(w a * E a b) * f b := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedOLDMaskedEPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Genuine signed original E frame with both total OLD endpoints,
identically the old-masked E finite matrix on physical Fock×seen. -/
theorem source_original_ACTUAL_signed_OLD_masked_E_physical_exact434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    (if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a then
      sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
        a.val.2
        (fun out st =>
          if (∑ g : BG, (out.2 g).2.card) ≤ T then F out st else 0)
     else 0) =
    ∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T a b * F b.val.1 b.val.2 := by
  classical
  let gate : H → Prop :=
    sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T
  by_cases ha : gate a
  · simp only [gate] at ha
    simp only [if_pos ha]
    rw [source_original_ACTUAL_original_E_matrix_exact434
      SP sm BP bm J ell m cap patterns hcap keep
      q rho Vs V mu K zeta theta o k
      (fun out st => if (∑ g : BG, (out.2 g).2.card) ≤ T
        then F out st else 0) a]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hc : gate b
    · change sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b at hc
      have h_old : (∑ g : BG, (b.val.1.2 g).2.card) ≤ T := hc
      simp only [if_pos h_old,
        sourceOriginalActualSignedOLDMaskedEMatrix434, if_pos ha,
        if_pos hc]
    · change ¬ sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b at hc
      have h_old : ¬ (∑ g : BG, (b.val.1.2 g).2.card) ≤ T := hc
      simp only [if_neg h_old,sourceOriginalActualSignedOLDMaskedEMatrix434,
        if_pos ha,if_neg hc,mul_zero,zero_mul]
  · simp only [gate] at ha
    simp only [if_neg ha]
    simp only [sourceOriginalActualSignedOLDMaskedEMatrix434,
      if_neg ha,zero_mul,Finset.sum_const_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedProjectedGEMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Genuine G_i followed by the original two-sided projected E_keep:
the product of their EXACT signed matrices on a single Fock×seen carrier. -/
def sourceOriginalActualSignedProjectedGEMatrix434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ) (a c : H) : ℂ :=
  sourceOriginalSignedMatrixProduct434
    (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
      q rho N i V mu)
    (sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T) a c

/-- Exact finite two-step signed action on the original joint history
carrier. No re-sampling of seen after G or E. -/
theorem source_original_ACTUAL_signed_projected_GE_matrix_apply434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ) (f : H → ℂ) (a : H) :
    (∑ b : H,
      sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        q rho N i V mu a b *
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T f b) =
    ∑ c : H, sourceOriginalActualSignedProjectedGEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k N i T a c * f c := by
  classical
  unfold sourceOriginalActualSignedProjectedGEMatrix434
  have e (b : H) :=
    source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T f b
  simp_rw [e]
  exact source_original_signed_matrix_product_apply434
    (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q rho N i V mu)
    (sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T) f a

/-- Exact complex-bilinear forward-prefix/backward-suffix pairing of
one G and both OLD-masked E visit. The prefix is propagated by the
true signed transpose, never by a positive history maximum. -/
theorem source_original_ACTUAL_signed_projected_GE_pairing434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ) (w f : H → ℂ) :
    (∑ a : H, w a * (∑ b : H,
      sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        q rho N i V mu a b *
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T f b)) =
    ∑ c : H, (∑ a : H, w a *
      sourceOriginalActualSignedProjectedGEMatrix434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k N i T a c) * f c := by
  classical
  let M := sourceOriginalActualSignedProjectedGEMatrix434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs V mu K zeta theta o k N i T
  calc
    _ = ∑ a : H, w a * (∑ c : H, M a c * f c) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_original_ACTUAL_signed_projected_GE_matrix_apply434]
    _ = ∑ a : H, ∑ c : H, (w a * M a c) * f c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = ∑ c : H, ∑ a : H, (w a * M a c) * f c := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedProjectedGEPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Original exact signed G and two-sided-old-masked E frame on
the REAL cumulative numerical history, before restricting to finite H. -/
def sourceOriginalActualSignedProjectedGEPhysical434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
    q rho N i V mu y seen (fun yg sg =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameFilteredRow434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta theta o k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)
          sg (fun out st =>
            if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)
      else 0)

/-- One ORIGINAL signed physical G/E step, with BOTH OLD masks,
equals the exact product of the TWO signed finite Fock×seen matrices.
All natural birth-history data are preserved; no positivity premise. -/
theorem source_original_ACTUAL_signed_projected_GE_physical_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalActualSignedProjectedGEPhysical434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k N i T F a.val.1 a.val.2 =
    ∑ c : H, sourceOriginalActualSignedProjectedGEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k N i T a c * F c.val.1 c.val.2 := by
  classical
  let G := sourceOriginalActualSignedGhostMatrix434
    SP sm BP bm J ell cap q rho N i V mu
  let E := sourceOriginalActualSignedOLDMaskedEMatrix434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k T
  let EF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
      sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)
        sg (fun out st =>
          if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)
      else 0
  have hE (b : H) :
      EF b.val.1 b.val.2 =
        ∑ c : H, E b c * F c.val.1 c.val.2 := by
    have he := source_original_ACTUAL_signed_OLD_masked_E_physical_exact434
      SP sm BP bm J ell m cap patterns hcap keep
      q rho Vs V mu K zeta theta o k T F b
    change (if sourceOriginalActualSignedOLDGate434
      SP sm BP bm J ell cap T b then _ else 0) = _ at he
    by_cases hb : sourceOriginalActualSignedOLDGate434
      SP sm BP bm J ell cap T b
    · have hb' : (∑ g : BG,(b.val.1.2 g).2.card) ≤ T := hb
      simp only [if_pos hb] at he
      simpa only [EF, E, if_pos hb'] using he
    · have hb' : ¬ (∑ g : BG,(b.val.1.2 g).2.card) ≤ T := hb
      simp only [if_neg hb] at he
      simpa only [EF, E, if_neg hb'] using he
  have hG :
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
        q rho N i V mu a.val.1 a.val.2 EF =
      ∑ b : H, G a b * EF b.val.1 b.val.2 :=
    source_original_ACTUAL_original_G_matrix_exact434
      SP sm BP bm J ell cap hi hcap q rho N i Vs V mu hVs hmu EF a
  change sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu a.val.1 a.val.2 EF = _
  calc
    _ = ∑ b : H, G a b * EF b.val.1 b.val.2 := hG
    _ = ∑ b : H, G a b *
        (∑ c : H, E b c * F c.val.1 c.val.2) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hE b]
    _ = ∑ c : H, sourceOriginalSignedMatrixProduct434 G E a c *
        F c.val.1 c.val.2 := by
      exact source_original_signed_matrix_product_apply434
        G E (fun c => F c.val.1 c.val.2) a
    _ = _ := by
      rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedGEThetaModes -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- True E Fourier coefficients after BOTH OLD endpoint masks, with
no deletion or resampling of the chronological numerical seen. -/
def sourceOriginalActualSignedOLDMaskedEThetaMode434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (T : ℕ) (a b : H) (D : ℕ) : ℂ :=
  if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a then
    if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b then
      sourceOriginalActualSignedEThetaMode434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta o k a b D
    else 0
  else 0

/-- For every exact reachable Fock×seen matrix entry, retaining BOTH
OLD gates only restricts its existing signed Fourier coefficients. -/
theorem source_original_ACTUAL_OLD_masked_E_theta_modes434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ) (a b : H) :
    sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k T a b =
    ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k a,
      sourceOriginalActualSignedOLDMaskedEThetaMode434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta o k T a b D *
      originalReturnPhase theta o k D := by
  by_cases ha : sourceOriginalActualSignedOLDGate434
      SP sm BP bm J ell cap T a
  · by_cases hb : sourceOriginalActualSignedOLDGate434
        SP sm BP bm J ell cap T b
    · simp only [sourceOriginalActualSignedOLDMaskedEMatrix434,
        sourceOriginalActualSignedOLDMaskedEThetaMode434,
        if_pos ha, if_pos hb]
      exact source_original_ACTUAL_signed_E_theta_modes434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k a b
    · simp [sourceOriginalActualSignedOLDMaskedEMatrix434,
        sourceOriginalActualSignedOLDMaskedEThetaMode434, ha, hb]
  · simp [sourceOriginalActualSignedOLDMaskedEMatrix434,
      sourceOriginalActualSignedOLDMaskedEThetaMode434, ha]

/-- The G_i physical ghost has no independent theta variable: the
actual signed G_i P_T E_i P_T kernel is a sum of TRUE complex
intermediate-state amplitudes and true Fourier divisor phases. -/
theorem source_original_ACTUAL_projected_GE_theta_modes434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (N i T : ℕ) (a c : H) :
    sourceOriginalActualSignedProjectedGEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k N i T a c =
    ∑ b : H,
      ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
          SP sm BP bm J ell m cap patterns o k b,
        (sourceOriginalActualSignedGhostMatrix434
          SP sm BP bm J ell cap q rho N i V mu a b *
         sourceOriginalActualSignedOLDMaskedEThetaMode434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta o k T b c D) *
          originalReturnPhase theta o k D := by
  unfold sourceOriginalActualSignedProjectedGEMatrix434
    sourceOriginalSignedMatrixProduct434
  apply Finset.sum_congr rfl
  intro b hb
  rw [source_original_ACTUAL_OLD_masked_E_theta_modes434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedOLDDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact COMPLEX (not absolute) original finite E decomposition:
every true legal signed witness lies either in CLEAN or DIRTY. -/
theorem source_original_ACTUAL_signed_E_matrix_clean_dirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (a b : H) :
    sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k a b =
    sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k a b +
    sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta o k a b := by
  classical
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  let seen := a.val.2
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
    (sourceOriginalSignedFiniteDelta434 b)
  change sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
    (fun _ _ => True) q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F +
    sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F
  rw [←source_original_ACTUAL_E_frame_true434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta o k x seen F]
  exact source_original_FRAME_E_clean_dirty_split434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta o k x seen F

/-- The two genuine OLD endpoint P_T masks distribute over the
original signed CLEAN + DIRTY split, with NO projection loss. -/
theorem source_original_ACTUAL_signed_OLD_E_clean_dirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (T : ℕ) (a b : H) :
    sourceOriginalActualSignedOLDMaskedEMatrix434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k T a b =
    sourceOriginalActualSignedOLDMaskedEMatrix434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k T a b +
    sourceOriginalActualSignedOLDMaskedEMatrix434 SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta o k T a b := by
  classical
  by_cases ha : sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a
  · by_cases hb : sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T b
    · simp only [sourceOriginalActualSignedOLDMaskedEMatrix434,
        if_pos ha,if_pos hb]
      exact source_original_ACTUAL_signed_E_matrix_clean_dirty434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k a b
    · simp only [sourceOriginalActualSignedOLDMaskedEMatrix434,
        if_pos ha,if_neg hb,zero_add]
  · simp only [sourceOriginalActualSignedOLDMaskedEMatrix434,
      if_neg ha,zero_add]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedGEDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Every original projected signed G_i E_i step splits into the
exact complex G_i PCLEANP and G_i P(E-CLEAN)P matrices. The same
joint Fock×seen state is used for both factors and their product. -/
theorem source_original_ACTUAL_signed_projected_GE_clean_dirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (N i T : ℕ) (a c : H) :
    sourceOriginalActualSignedProjectedGEMatrix434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k N i T a c =
    sourceOriginalActualSignedProjectedGEMatrix434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k N i T a c +
    sourceOriginalActualSignedProjectedGEMatrix434 SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta o k N i T a c := by
  classical
  unfold sourceOriginalActualSignedProjectedGEMatrix434
    sourceOriginalSignedMatrixProduct434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [source_original_ACTUAL_signed_OLD_E_clean_dirty434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta o k T b c]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteDuhamel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact signed finite-state row action; the state is later
the REAL reachable Fock output together with cumulative seen. -/
def sourceOriginalSignedMatrixAction434 {H : Type} [Fintype H]
    (K : H → H → ℂ) (f : H → ℂ) (a : H) : ℂ :=
  ∑ b : H, K a b * f b

/-- Ordered chronological signed matrix evolution; start indexes the
actual G/E visit, and the terminal history state is never resampled. -/
def sourceOriginalSignedMatrixChain434 {H : Type} [Fintype H]
    (M : ℕ → H → H → ℂ) :
    (remaining start : ℕ) → (H → ℂ) → H → ℂ
  | 0,_,f => f
  | n+1,start,f => sourceOriginalSignedMatrixAction434 (M start)
      (sourceOriginalSignedMatrixChain434 M n (start+1) f)

/-- The FULL signed G/E kernel as the pointwise sum CLEAN+DIRTY. -/
def sourceOriginalSignedKernelAdd434 {H : Type}
    (C D : ℕ → H → H → ℂ) (i : ℕ) (a b : H) : ℂ :=
  C i a b + D i a b

/-- Signed first-DIRTY insertion through n true chronological visits.
Before the unique insertion we use CLEAN; afterwards FULL. -/
def sourceOriginalSignedMatrixDirtyChain434 {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) :
    (remaining start : ℕ) → (H → ℂ) → H → ℂ
  | 0,_,_ => fun _ => 0
  | n+1,start,f => fun a =>
      sourceOriginalSignedMatrixAction434 (D start)
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D) n (start+1) f) a +
      sourceOriginalSignedMatrixAction434 (C start)
        (sourceOriginalSignedMatrixDirtyChain434 C D n (start+1) f) a

/-- Exact fully signed finite chronological Duhamel identity.
The subtraction and the insertion root involve the SAME intermediate
state, including all numerical memory. No absolute-value inequality. -/
theorem source_original_signed_matrix_Duhamel434
    {H : Type} [Fintype H] (C D : ℕ → H → H → ℂ)
    (n start : ℕ) (f : H → ℂ) (a : H) :
    sourceOriginalSignedMatrixChain434
      (sourceOriginalSignedKernelAdd434 C D) n start f a -
    sourceOriginalSignedMatrixChain434 C n start f a =
    sourceOriginalSignedMatrixDirtyChain434 C D n start f a := by
  induction n generalizing start a with
  | zero =>
      simp only [sourceOriginalSignedMatrixChain434,
        sourceOriginalSignedMatrixDirtyChain434,sub_self]
  | succ n ih =>
      change (∑ b : H, (C start a b + D start a b) *
        sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D) n (start+1) f b) -
        (∑ b : H, C start a b *
          sourceOriginalSignedMatrixChain434 C n (start+1) f b) =
        (∑ b : H, D start a b *
          sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 C D) n (start+1) f b) +
        (∑ b : H, C start a b *
          sourceOriginalSignedMatrixDirtyChain434 C D n (start+1) f b)
      rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      have h := ih (start+1) b
      rw [←h]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteTVTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {X S : Type} [Fintype X] [Fintype S] [Nonempty S]

/-- A signed prefix's physical-output TV is the l1 sum of complex
amplitudes over the original cumulative histories at that output. -/
def sourceOriginalFiniteHistoryTVProfile434
    (w : X × S → ℂ) (x : X) : ℝ :=
  ∑ s : S, ‖w (x,s)‖

/-- The TRUE COMPLEX forward-transpose action on joint states,
retaining the same input/output history indices in the matrix. -/
def sourceOriginalFiniteHistoryTVForward434
    (M : (X × S) → (X × S) → ℂ)
    (w : X × S → ℂ) (y : X) (t : S) : ℂ :=
  ∑ x : X,∑ s : S,w (x,s) * M (x,s) (y,t)

/-- A precise original-kernel history-TV bound: maximum over ONE
input history of the genuine total outgoing absolute row to a
specified physical output. No factor #Hist occurs in its definition. -/
def sourceOriginalFiniteHistoryTVKernel434
    (M : (X × S) → (X × S) → ℂ)
    (x y : X) : ℝ :=
  (Finset.univ : Finset S).sup' Finset.univ_nonempty
    (fun s => ∑ t : S,‖M (x,s) (y,t)‖)
theorem source_original_finite_history_TV_kernel_majorant434
    (M : (X × S) → (X × S) → ℂ)
    (x y : X) (s : S) :
    (∑ t : S,‖M (x,s) (y,t)‖) ≤
      sourceOriginalFiniteHistoryTVKernel434 M x y := by
  classical
  exact Finset.le_sup'
    (fun s : S => ∑ t : S,‖M (x,s) (y,t)‖)
    (Finset.mem_univ s)

/-- Actual one-visit COMPLEX history-TV transport is bounded by
the exact physically aggregated absolute kernel acting on output
TV profiles. This proof contains NO standalone history-cardinality
factor and imposes NO stochastic normalization on the signed G/E. -/
theorem source_original_finite_history_TV_forward_bound434
    (M : (X × S) → (X × S) → ℂ)
    (w : X × S → ℂ) (y : X) :
    sourceOriginalFiniteHistoryTVProfile434
      (fun z => sourceOriginalFiniteHistoryTVForward434 M w z.1 z.2) y ≤
    ∑ x : X,
      sourceOriginalFiniteHistoryTVKernel434 M x y *
        sourceOriginalFiniteHistoryTVProfile434 w x := by
  classical
  have hnorm (t : S) :
      ‖sourceOriginalFiniteHistoryTVForward434 M w y t‖ ≤
      ∑ x : X,∑ s : S,‖w (x,s) * M (x,s) (y,t)‖ := by
    unfold sourceOriginalFiniteHistoryTVForward434
    calc
      _ ≤ ∑ x : X, ‖∑ s : S,w (x,s)*M (x,s) (y,t)‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        exact norm_sum_le _ _
  unfold sourceOriginalFiniteHistoryTVProfile434
  calc
    _ ≤ ∑ t : S,∑ x : X,∑ s : S,
        ‖w (x,s) * M (x,s) (y,t)‖ := by
          apply Finset.sum_le_sum
          intro t ht
          exact hnorm t
    _ = ∑ x : X,∑ s : S,∑ t : S,
        ‖w (x,s) * M (x,s) (y,t)‖ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
    _ = ∑ x : X,∑ s : S,
        ‖w (x,s)‖ * (∑ t : S,‖M (x,s) (y,t)‖) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro s hs
          simp_rw [norm_mul]
          rw [Finset.mul_sum]
    _ ≤ ∑ x : X,∑ s : S,
        ‖w (x,s)‖ * sourceOriginalFiniteHistoryTVKernel434 M x y := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left
            (source_original_finite_history_TV_kernel_majorant434 M x y s)
            (norm_nonneg _)
    _ = _ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [←Finset.sum_mul]
          ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteFibreTVTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Total variation of the ACTUAL signed complex prefix after
projecting each joint (Fock, seen) state to its physical Fock output.
No assumption that all Fock×history combinations are reachable. -/
def sourceOriginalFiniteFibreTVProfile434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (w : H → ℂ) (x : X) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset H).filter (fun a => p a = x), ‖w a‖

/-- Exact fibrewise ABSOLUTE transfer cost from physical x to y,
maximised over only the genuine input histories in its fibre.
The empty input fibre has cost zero; no fictitious history is added. -/
def sourceOriginalFiniteFibreTVKernel434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (M : H → H → ℂ) (x y : X) : ℝ :=
  let S := (Finset.univ : Finset H).filter (fun a => p a = x)
  if h : S.Nonempty then
    S.sup' h (fun a =>
      ∑ b ∈ (Finset.univ : Finset H).filter (fun b => p b = y),
        ‖M a b‖)
  else 0

/-- The original chronological signed complex matrix transposes
with ONE shared Fock×seen intermediate state at each visit. -/
def sourceOriginalFiniteFibreTVForward434
    {H : Type} [Fintype H]
    (M : H → H → ℂ) (w : H → ℂ) (b : H) : ℂ :=
  ∑ a : H, w a * M a b

/-- Every individual real signed matrix row has the precise
physical-output fibre kernel bound. Inaccessible fibres cost ZERO. -/
theorem source_original_finite_fibre_TV_row_bound434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (M : H → H → ℂ) (a : H) (y : X) :
    (∑ b ∈ (Finset.univ : Finset H).filter (fun b => p b = y),
      ‖M a b‖) ≤
    sourceOriginalFiniteFibreTVKernel434 p M (p a) y := by
  classical
  have ha : a ∈ (Finset.univ : Finset H).filter
      (fun z => p z = p a) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  unfold sourceOriginalFiniteFibreTVKernel434
  dsimp only
  split_ifs with h
  · exact Finset.le_sup' (fun z : H =>
      ∑ b ∈ (Finset.univ : Finset H).filter (fun b => p b = y),
        ‖M z b‖) ha
  · exact False.elim (h ⟨a,ha⟩)

/-- TRUE finite forward transport of arbitrary complex signed prefixes,
aggregated by physical output but retaining cumulative seen in every
matrix coefficient. The exact fibrewise absolute row kernel does not
pay a separate |Hist| multiplicity, and empty reachability fibres
have cost zero. No stochastic/contraction hypothesis. -/
theorem source_original_finite_fibre_TV_forward_bound434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (M : H → H → ℂ) (w : H → ℂ) (y : X) :
    sourceOriginalFiniteFibreTVProfile434 p
      (sourceOriginalFiniteFibreTVForward434 M w) y ≤
    ∑ x : X, sourceOriginalFiniteFibreTVKernel434 p M x y *
      sourceOriginalFiniteFibreTVProfile434 p w x := by
  classical
  let S : X → Finset H := fun x =>
    (Finset.univ : Finset H).filter (fun a => p a = x)
  let K := sourceOriginalFiniteFibreTVKernel434 p M
  have hN (b : H) :
      ‖sourceOriginalFiniteFibreTVForward434 M w b‖ ≤
      ∑ a : H, ‖w a‖ * ‖M a b‖ := by
    unfold sourceOriginalFiniteFibreTVForward434
    calc
      _ ≤ ∑ a : H,‖w a*M a b‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [norm_mul]
  calc
    _ = ∑ b ∈ S y,
      ‖sourceOriginalFiniteFibreTVForward434 M w b‖ := rfl
    _ ≤ ∑ b ∈ S y,∑ a : H,‖w a‖ * ‖M a b‖ := by
      apply Finset.sum_le_sum
      intro b hb
      exact hN b
    _ = ∑ a : H,∑ b ∈ S y,‖w a‖ * ‖M a b‖ := by
      rw [Finset.sum_comm]
    _ = ∑ a : H,‖w a‖ * (∑ b ∈ S y,‖M a b‖) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ ≤ ∑ a : H,‖w a‖ * K (p a) y := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (source_original_finite_fibre_TV_row_bound434 p M a y)
        (norm_nonneg _)
    _ = ∑ x : X,∑ a ∈ S x,‖w a‖ * K (p a) y := by
      exact (Finset.sum_fiberwise (Finset.univ : Finset H)
        p (fun a => ‖w a‖ * K (p a) y)).symm
    _ = ∑ x : X,K x y *
      sourceOriginalFiniteFibreTVProfile434 p w x := by
      apply Finset.sum_congr rfl
      intro x hx
      change (∑ a ∈ S x,‖w a‖ * K (p a) y) =
        K x y * (∑ a ∈ S x,‖w a‖)
      have hp (a : H) (ha : a ∈ S x) : p a = x :=
        (Finset.mem_filter.mp ha).2
      calc
        _ = ∑ a ∈ S x, ‖w a‖ * K x y := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hp a ha]
        _ = _ := by
          rw [←Finset.sum_mul]
          ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteFibreTVSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Squared inverse-density L2 norm of the true L1 HISTORY variation,
fiberwise over the physical outputs of ANY original finite
Fock×seen carrier, with no |Hist| factor. -/
def sourceOriginalFiniteFibreTVInverseEnergy434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (π : X → ℝ) (w : H → ℂ) : ℝ :=
  ∑ x : X, (1/π x) *
    ‖(sourceOriginalFiniteFibreTVProfile434 p w x : ℂ)‖^2

/-- Exact physical fibre TV profile is nonnegative, including empty
fibres: it is simply the sum of norms of the true complex amplitudes. -/
theorem source_original_finite_fibre_TV_profile_nonneg434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (w : H → ℂ) (x : X) :
    0 ≤ sourceOriginalFiniteFibreTVProfile434 p w x := by
  unfold sourceOriginalFiniteFibreTVProfile434
  exact Finset.sum_nonneg (fun a ha => norm_nonneg _)

/-- True finite Fock×history fibre kernel is nonnegative for
every pair of physical outputs, even with an empty reachable fibre. -/
theorem source_original_finite_fibre_TV_kernel_nonneg434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (M : H → H → ℂ) (x y : X) :
    0 ≤ sourceOriginalFiniteFibreTVKernel434 p M x y := by
  classical
  unfold sourceOriginalFiniteFibreTVKernel434
  dsimp only
  split_ifs with hs
  · rcases hs with ⟨a,ha⟩
    calc
      0 ≤ ∑ b ∈ (Finset.univ : Finset H).filter (fun b => p b = y),
          ‖M a b‖ :=
        Finset.sum_nonneg (fun b hb => norm_nonneg _)
      _ ≤ _ := Finset.le_sup' (fun a =>
        ∑ b ∈ (Finset.univ : Finset H).filter (fun b => p b = y),
          ‖M a b‖) ha
  · exact le_refl _

/-- A genuine finite physical fibre kernel has a direct inverse
density Schur bound. R is the ACTUAL total incoming TV row bound;
D is the exact inverse-density outgoing bound. Neither is assumed
to be one or polynomial; any loss is visible in R*D. -/
theorem source_original_finite_fibre_TV_inverse_Schur434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (M : H → H → ℂ) (π : X → ℝ)
    (hπ : ∀ x,0 < π x)
    (R D : ℝ) (hR0 : 0 ≤ R)
    (hIncoming : ∀ y : X,
      (∑ x : X, sourceOriginalFiniteFibreTVKernel434 p M x y) ≤ R)
    (hOutgoing : ∀ x : X,
      (∑ y : X, sourceOriginalFiniteFibreTVKernel434 p M x y / π y) ≤
        D / π x)
    (w : H → ℂ) :
    sourceOriginalFiniteFibreTVInverseEnergy434 p π
      (sourceOriginalFiniteFibreTVForward434 M w) ≤
      R * D * sourceOriginalFiniteFibreTVInverseEnergy434 p π w := by
  classical
  let K := sourceOriginalFiniteFibreTVKernel434 p M
  let mass : X → ℝ := fun x => 1/π x
  let A : X → X → ℝ := fun y x => K x y / π y
  let v : X → ℂ := fun x => (sourceOriginalFiniteFibreTVProfile434 p w x:ℂ)
  let u : X → ℂ := fun y =>
    (sourceOriginalFiniteFibreTVProfile434 p
      (sourceOriginalFiniteFibreTVForward434 M w) y:ℂ)

  have hK (x y : X) : 0 ≤ K x y :=
    source_original_finite_fibre_TV_kernel_nonneg434 p M x y
  have hMass (y : X) : 0 ≤ mass y := by
    dsimp only [mass]
    exact one_div_nonneg.mpr (hπ y).le
  have hA (y x : X) : 0 ≤ A y x :=
    div_nonneg (hK x y) (hπ y).le
  have hRow (y : X) (hy : y ∈ (Finset.univ : Finset X)) :
      (∑ x : X,A y x) ≤ R * mass y := by
    change (∑ x : X,K x y / π y) ≤ R * (1/π y)
    calc
      _ = (∑ x : X,K x y) * (1/π y) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right (hIncoming y)
          (one_div_nonneg.mpr (hπ y).le)
  have hCol (x : X) (hx : x ∈ (Finset.univ : Finset X)) :
      (∑ y : X,A y x) ≤ D * mass x := by
    change (∑ y : X,K x y / π y) ≤ D*(1/π x)
    simpa only [K,div_eq_mul_inv,one_div,one_mul] using hOutgoing x
  have hv (x : X) : ‖v x‖ =
      sourceOriginalFiniteFibreTVProfile434 p w x := by
    dsimp only [v]
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (source_original_finite_fibre_TV_profile_nonneg434 p w x)]
  have hu (y : X) : ‖u y‖ =
      sourceOriginalFiniteFibreTVProfile434 p
        (sourceOriginalFiniteFibreTVForward434 M w) y := by
    dsimp only [u]
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (source_original_finite_fibre_TV_profile_nonneg434
        p (sourceOriginalFiniteFibreTVForward434 M w) y)]

  have hT (y : X) (hy : y ∈ (Finset.univ : Finset X)) :
      mass y * ‖u y‖ ≤ ∑ x : X,A y x * ‖v x‖ := by
    rw [hu]
    simp_rw [hv]
    change (1/π y) *
        sourceOriginalFiniteFibreTVProfile434 p
          (sourceOriginalFiniteFibreTVForward434 M w) y ≤
      ∑ x : X,K x y / π y *
        sourceOriginalFiniteFibreTVProfile434 p w x
    calc
      _ ≤ (1/π y)*(∑ x : X,
          K x y * sourceOriginalFiniteFibreTVProfile434 p w x) :=
        mul_le_mul_of_nonneg_left
          (source_original_finite_fibre_TV_forward_bound434 p M w y)
          (one_div_nonneg.mpr (hπ y).le)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hCore := source_original_finite_density_kernel_energy434
    (Finset.univ : Finset X) mass hMass A hA R D hR0
    hRow hCol v u hT
  change (∑ x : X,mass x * ‖u x‖^2) ≤
    R * D * (∑ x : X,mass x * ‖v x‖^2)
  exact hCore
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteFibreSparseTV -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- A signed finite Fock×seen density that has AT MOST ONE
nonzero history for each physical Fock output pays NO L1-history
squaring factor: L1-fibre variation squared is L2-fibre mass.
This applies to the actual original initial vacuum, not to all
later physical CLEAN histories. -/
theorem source_original_finite_fibre_sparse_TV_sq434
    {H X : Type} [Fintype H] [Fintype X] [DecidableEq X]
    (p : H → X) (w : H → ℂ)
    (hSparse : ∀ a b : H, p a = p b →
      w a ≠ 0 → w b ≠ 0 → a = b)
    (x : X) :
    (sourceOriginalFiniteFibreTVProfile434 p w x)^2 =
      ∑ a ∈ (Finset.univ : Finset H).filter
        (fun a => p a = x), ‖w a‖^2 := by
  classical
  let S : Finset H := (Finset.univ : Finset H).filter (fun a => p a = x)
  change (∑ a ∈ S,‖w a‖)^2 = ∑ a ∈ S,‖w a‖^2
  by_cases hn : ∃ a ∈ S,w a ≠ 0
  · rcases hn with ⟨a,ha,hwa⟩
    have hOther (b : H) (hb : b ∈ S) (hne : b ≠ a) :
        w b = 0 := by
      by_contra hwb
      have hpa : p a = x := (Finset.mem_filter.mp ha).2
      have hpb : p b = x := (Finset.mem_filter.mp hb).2
      have heq : b = a := hSparse b a (hpb.trans hpa.symm) hwb hwa
      exact hne heq
    have hLeft :
        (∑ b ∈ S, ‖w b‖) = ‖w a‖ := by
      apply Finset.sum_eq_single a
      · intro b hb hne
        simp only [hOther b hb hne,norm_zero]
      · exact False.elim ∘ (fun h => h ha)
    have hRight :
        (∑ b ∈ S, ‖w b‖^2) = ‖w a‖^2 := by
      apply Finset.sum_eq_single a
      · intro b hb hne
        simp only [hOther b hb hne,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
      · exact False.elim ∘ (fun h => h ha)
    rw [hLeft,hRight]
  · have hw (a : H) (ha : a ∈ S) : w a = 0 := by
      by_contra hwa
      exact hn ⟨a,ha,hwa⟩
    have hLeft : (∑ a ∈ S,‖w a‖) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hw a ha,norm_zero]
    have hRight : (∑ a ∈ S,‖w a‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hw a ha,norm_zero]
      norm_num
    rw [hLeft,hRight]
    norm_num
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedProjectedGESchedule -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- ACTUAL chronological projected G/E matrix schedule with
memoryOrientationK, alternating E signs and both OLD endpoints. -/
def sourceOriginalActualSignedProjectedGESchedule434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T : ℕ) (i : ℕ) (a b : H) : ℂ :=
  sourceOriginalActualSignedProjectedGEMatrix434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
    zeta theta (physicalAlternatingSign i) k N i T a b

/-- Every ACTUAL scheduled full G_i PEP_i is CLEAN_i + DIRTY_i
on the same chronological joint physical Fock×seen state. -/
theorem source_original_ACTUAL_signed_projected_schedule_split434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T i : ℕ) (a b : H) :
    sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns (fun _ _ => True)
      q rho Vs V mu K zeta theta k N T i a b =
    sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k N T i a b +
    sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k N T i a b := by
  exact source_original_ACTUAL_signed_projected_GE_clean_dirty434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
    zeta theta (physicalAlternatingSign i) k N i T a b

/-- Exact signed finite CLEAN-to-FULL Duhamel for the original
chronological G/E schedule, without any positive history maximum. -/
theorem source_original_ACTUAL_signed_projected_GE_Duhamel434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ) (f : H → ℂ) (a : H) :
    let Full := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns (fun _ _ => True)
      q rho Vs V mu K zeta theta k N T
    let Clean := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k N T
    let Dirty := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k N T
    sourceOriginalSignedMatrixChain434 Full n start f a -
      sourceOriginalSignedMatrixChain434 Clean n start f a =
    sourceOriginalSignedMatrixDirtyChain434 Clean Dirty n start f a := by
  dsimp only
  let Full := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns (fun _ _ => True)
    q rho Vs V mu K zeta theta k N T
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  have hFull : Full = sourceOriginalSignedKernelAdd434 Clean Dirty := by
    funext i a b
    exact source_original_ACTUAL_signed_projected_schedule_split434
      SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i a b
  change sourceOriginalSignedMatrixChain434 Full n start f a -
    sourceOriginalSignedMatrixChain434 Clean n start f a =
      sourceOriginalSignedMatrixDirtyChain434 Clean Dirty n start f a
  rw [hFull]
  exact source_original_signed_matrix_Duhamel434 Clean Dirty n start f a
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGEThetaLaurent -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE G_i P_T E_i P_T as a finite Laurent polynomial. Each
coefficient is a complex sum over genuine intermediate Fock×seen states,
and exponents are the ACTUAL signed integer return displacements.
NO independent theta or history sample is introduced. -/
def sourceOriginalActualProjectedGEThetaLaurent434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (N i T : ℕ) (a c : H) :
    AddMonoidAlgebra ℂ ℤ :=
  ∑ b : H,
    ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k b,
      AddMonoidAlgebra.single (o*k*(D:ℤ))
        (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
          q rho N i V mu a b *
        sourceOriginalActualSignedOLDMaskedEThetaMode434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta o k T b c D)

/-- Evaluation of the actual signed Laurent polynomial reproduces the
literal G_i P_T E_i P_T matrix entry at EVERY common theta. -/
theorem source_original_ACTUAL_projected_GE_theta_Laurent434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (N i T : ℕ) (a c : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualProjectedGEThetaLaurent434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta o k N i T a c) =
    sourceOriginalActualSignedProjectedGEMatrix434
      SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k N i T a c := by
  rw [source_original_ACTUAL_projected_GE_theta_modes434]
  unfold sourceOriginalActualProjectedGEThetaLaurent434
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro D hD
  exact source_original_ACTUAL_return_phase_eval_single434 theta o k D _

/-- All ORIGINAL alternating orientation and joint K chronology lives in
one exact theta-independent Laurent polynomial at each visit index. -/
def sourceOriginalActualProjectedGEScheduleLaurent434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta : ℝ)
    (k : ℤ) (N T : ℕ) (i : ℕ) (a b : H) :
    AddMonoidAlgebra ℂ ℤ :=
  sourceOriginalActualProjectedGEThetaLaurent434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
    zeta (physicalAlternatingSign i) k N i T a b

theorem source_original_ACTUAL_projected_GE_schedule_Laurent434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N T i : ℕ) (a b : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualProjectedGEScheduleLaurent434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta k N T i a b) =
      sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta k N T i a b := by
  exact source_original_ACTUAL_projected_GE_theta_Laurent434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
    zeta theta (physicalAlternatingSign i) k N i T a b
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGEFrequencyConstraint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The EXACT arithmetic Fourier coefficient of a TRUE physical
G_i P_T E_i P_T kernel: it is a signed sum over the ACTUAL Fock×seen
intermediate states and integer divisor D subject to o*k*D=d.
No artificial independent history or positive modulus is introduced. -/
theorem source_original_ACTUAL_projected_GE_Laurent_coeff434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (N i T : ℕ) (a c : H) (d : ℤ) :
    (sourceOriginalActualProjectedGEThetaLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k N i T a c).coeff d =
    ∑ b : H,
      ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k b,
        if o*k*(D:ℤ)=d then
          sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
            q rho N i V mu a b *
          sourceOriginalActualSignedOLDMaskedEThetaMode434
            SP sm BP bm J ell m cap patterns keep
            q rho Vs V mu K zeta o k T b c D
        else 0 := by
  classical
  simp only [sourceOriginalActualProjectedGEThetaLaurent434,
    AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The TRUE signed Fourier coefficient can only use arithmetic
frequencies divisible by the ORIGINAL integer Fourier parameter k.
This is a concrete support restriction for EVERY actual G/E step,
not a saving claim. -/
theorem source_original_ACTUAL_projected_GE_off_k_lattice_zero434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (N i T : ℕ) (a c : H) (d : ℤ)
    (hd : ¬ k ∣ d) :
    (sourceOriginalActualProjectedGEThetaLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k N i T a c).coeff d = 0 := by
  rw [source_original_ACTUAL_projected_GE_Laurent_coeff434]
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro D hD
  have hh : o*k*(D:ℤ) ≠ d := by
    intro heq
    apply hd
    refine ⟨o*(D:ℤ), ?_⟩
    nlinarith [heq]
  simp [hh]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentFrequencyLattice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- All nonzero TOTAL signed Fourier frequencies lie in the integer
lattice kℤ. This is a support predicate, not an absolute-value bound. -/
def sourceOriginalLaurentKSupported434 (k : ℤ)
    (P : AddMonoidAlgebra ℂ ℤ) : Prop :=
  ∀ d, ¬ k ∣ d → P.coeff d = 0

theorem source_original_Laurent_K_single434
    (k d : ℤ) (z : ℂ) (hd : k ∣ d) :
    sourceOriginalLaurentKSupported434 k
      (AddMonoidAlgebra.single d z) := by
  intro n hn
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hne : d ≠ n := by
    intro h
    exact hn (h ▸ hd)
  simp [hne]

theorem source_original_Laurent_K_zero434
    (k : ℤ) : sourceOriginalLaurentKSupported434 k 0 := by
  intro d hd
  simp [AddMonoidAlgebra.coeff_zero]

theorem source_original_Laurent_K_add434
    (k : ℤ) (P Q : AddMonoidAlgebra ℂ ℤ)
    (hP : sourceOriginalLaurentKSupported434 k P)
    (hQ : sourceOriginalLaurentKSupported434 k Q) :
    sourceOriginalLaurentKSupported434 k (P+Q) := by
  intro d hd
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    hP d hd, hQ d hd, add_zero]

theorem source_original_Laurent_K_sum434
    {I : Type} (k : ℤ) (s : Finset I)
    (F : I → AddMonoidAlgebra ℂ ℤ)
    (hF : ∀ i ∈ s, sourceOriginalLaurentKSupported434 k (F i)) :
    sourceOriginalLaurentKSupported434 k (∑ i ∈ s, F i) := by
  intro d hd
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hF i hi d hd)

theorem source_original_Laurent_K_mul434
    (k : ℤ) (P Q : AddMonoidAlgebra ℂ ℤ)
    (hP : sourceOriginalLaurentKSupported434 k P)
    (hQ : sourceOriginalLaurentKSupported434 k Q) :
    sourceOriginalLaurentKSupported434 k (P*Q) := by
  intro d hd
  rw [AddMonoidAlgebra.coeff_mul]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases heq : m+n=d
  · have hkm : k ∣ m := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hm) (hP m h)
    have hkn : k ∣ n := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hn) (hQ n h)
    exact False.elim (hd (heq ▸ (dvd_add hkm hkn)))
  · simp [heq]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedLaurentChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact common-theta polynomial action of any finite signed Fock×seen
matrix over the Laurent coefficient ring. State and seen never reset. -/
def sourceOriginalSignedLaurentAction434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (i : ℕ) (f : H → AddMonoidAlgebra ℂ ℤ) (a : H) :
    AddMonoidAlgebra ℂ ℤ :=
  ∑ b : H, M i a b * f b

/-- Chronological Laurent chain whose multiplication adds TOTAL signed
Fourier displacement across genuine visits. -/
def sourceOriginalSignedLaurentChain434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ) :
    (remaining start : ℕ) →
    (H → AddMonoidAlgebra ℂ ℤ) → H → AddMonoidAlgebra ℂ ℤ
  | 0, _, f => f
  | n+1, start, f =>
      sourceOriginalSignedLaurentAction434 M start
        (sourceOriginalSignedLaurentChain434 M n (start+1) f)

/-- Exact evaluation commutes with ANY finite chronological Laurent
chain: no positive TV bounds or independent Fourier phases. -/
theorem source_original_signed_Laurent_chain_eval434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (theta : ℝ) (n start : ℕ) (a : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalSignedLaurentChain434 M n start f a) =
    sourceOriginalSignedMatrixChain434
      (fun i x y => sourceOriginalActualThetaEval434 theta (M i x y))
      n start (fun b => sourceOriginalActualThetaEval434 theta (f b)) a := by
  induction n generalizing start a with
  | zero => rfl
  | succ n ih =>
      simp only [sourceOriginalSignedLaurentChain434,
        sourceOriginalSignedLaurentAction434,
        sourceOriginalSignedMatrixChain434,
        sourceOriginalSignedMatrixAction434, map_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [map_mul, ih (start+1) b]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalLaurentChronology -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- EXACT source G_i P_T E_i P_T chain in a single COMMON theta
Laurent ring, with real alternating orientation, literal KEEP
predicate, original joint K and full chronological seen. -/
theorem source_original_ACTUAL_physical_GE_Laurent_chain434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N T n start : ℕ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (a : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalSignedLaurentChain434
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta k N T)
        n start f a) =
      sourceOriginalSignedMatrixChain434
        (sourceOriginalActualSignedProjectedGESchedule434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta theta k N T)
        n start (fun b => sourceOriginalActualThetaEval434 theta (f b)) a := by
  rw [source_original_signed_Laurent_chain_eval434]
  congr 1
  funext i x y
  exact source_original_ACTUAL_projected_GE_schedule_Laurent434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
    zeta theta k N T i x y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedLaurentDirtyChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine first-DIRTY signed chronology over the common-theta Laurent
ring: CLEAN before the first insertion, FULL afterwards. Frequencies
add on multiplication, not by independently resampling theta. -/
def sourceOriginalSignedLaurentDirtyChain434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ) :
    (remaining start : ℕ) →
    (H → AddMonoidAlgebra ℂ ℤ) → H → AddMonoidAlgebra ℂ ℤ
  | 0, _, _ => fun _ => 0
  | n+1, start, f => fun a =>
      sourceOriginalSignedLaurentAction434 D start
        (sourceOriginalSignedLaurentChain434
          (fun i x y => C i x y + D i x y) n (start+1) f) a +
      sourceOriginalSignedLaurentAction434 C start
        (sourceOriginalSignedLaurentDirtyChain434 C D n (start+1) f) a

/-- The complete first-DIRTY Laurent chronology evaluates to the
EXACT original signed complex first-DIRTY matrix Duhamel expression.
No absolute values, independent histories, or new analytic bounds. -/
theorem source_original_signed_Laurent_DIRTY_chain_eval434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (theta : ℝ) (n start : ℕ) (a : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalSignedLaurentDirtyChain434 C D n start f a) =
    sourceOriginalSignedMatrixDirtyChain434
      (fun i x y => sourceOriginalActualThetaEval434 theta (C i x y))
      (fun i x y => sourceOriginalActualThetaEval434 theta (D i x y))
      n start (fun b => sourceOriginalActualThetaEval434 theta (f b)) a := by
  induction n generalizing start a with
  | zero =>
      simp [sourceOriginalSignedLaurentDirtyChain434,
        sourceOriginalSignedMatrixDirtyChain434]
  | succ n ih =>
      simp only [sourceOriginalSignedLaurentDirtyChain434,
        sourceOriginalSignedLaurentAction434,
        sourceOriginalSignedMatrixDirtyChain434,
        sourceOriginalSignedMatrixAction434,
        map_add, map_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro b hb
        rw [map_mul]
        congr 1
        rw [source_original_signed_Laurent_chain_eval434]
        congr 1
        funext i x y
        simp only [sourceOriginalSignedKernelAdd434, map_add]
      · apply Finset.sum_congr rfl
        intro b hb
        rw [map_mul,ih (start+1) b]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentLatticeChronology -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Every transition and suffix supported in the original k-frequency
lattice yields a supported next chronological Fock×seen action. -/
theorem source_original_Laurent_K_action434
    {H : Type} [Fintype H]
    (k : ℤ) (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (i : ℕ) (a : H)
    (hM : ∀ i a b, sourceOriginalLaurentKSupported434 k (M i a b))
    (hf : ∀ a, sourceOriginalLaurentKSupported434 k (f a)) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalSignedLaurentAction434 M i f a) := by
  unfold sourceOriginalSignedLaurentAction434
  apply source_original_Laurent_K_sum434
  intro b hb
  exact source_original_Laurent_K_mul434 k (M i a b) (f b)
    (hM i a b) (hf b)

/-- All actual chronological signed paths conserve their frequency
lattice: products ADD signed integer displacements on the one shared
Fourier variable, without resampling a seen history. -/
theorem source_original_Laurent_K_chain434
    {H : Type} [Fintype H]
    (k : ℤ) (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (hM : ∀ i a b, sourceOriginalLaurentKSupported434 k (M i a b))
    (hf : ∀ a, sourceOriginalLaurentKSupported434 k (f a))
    (n start : ℕ) (a : H) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalSignedLaurentChain434 M n start f a) := by
  induction n generalizing start a with
  | zero => exact hf a
  | succ n ih =>
      exact source_original_Laurent_K_action434
        k M (sourceOriginalSignedLaurentChain434 M n (start+1) f)
        start a hM (fun b => ih (start+1) b)

/-- First-DIRTY chronological expansion likewise keeps every
nonzero TOTAL phase at an integer multiple of the source shift k;
CLEAN prefix and complete PEP suffix share the actual finite state. -/
theorem source_original_Laurent_K_DIRTY_chain434
    {H : Type} [Fintype H]
    (k : ℤ) (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (hC : ∀ i a b, sourceOriginalLaurentKSupported434 k (C i a b))
    (hD : ∀ i a b, sourceOriginalLaurentKSupported434 k (D i a b))
    (hf : ∀ a, sourceOriginalLaurentKSupported434 k (f a))
    (n start : ℕ) (a : H) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalSignedLaurentDirtyChain434 C D n start f a) := by
  induction n generalizing start a with
  | zero =>
      exact source_original_Laurent_K_zero434 k
  | succ n ih =>
      change sourceOriginalLaurentKSupported434 k
        (sourceOriginalSignedLaurentAction434 D start
          (sourceOriginalSignedLaurentChain434
            (fun i x y => C i x y + D i x y) n (start+1) f) a +
          sourceOriginalSignedLaurentAction434 C start
            (sourceOriginalSignedLaurentDirtyChain434 C D n (start+1) f) a)
      apply source_original_Laurent_K_add434
      · apply source_original_Laurent_K_action434
          k D _ start a hD
        intro b
        apply source_original_Laurent_K_chain434
          k (fun i x y => C i x y + D i x y) f
          (fun i x y =>
            source_original_Laurent_K_add434 k (C i x y) (D i x y)
              (hC i x y) (hD i x y))
          hf
      · exact source_original_Laurent_K_action434
          k C _ start a hC (fun b => ih (start+1) b)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentFrequencyConvolution -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact signed convolution of integer TOTAL return frequencies.
Each summand couples the SAME intermediate chronological Fock×seen
state to its complementary signed displacement; no TV majorant. -/
theorem source_original_Laurent_actual_coeff_mul434
    (P Q : AddMonoidAlgebra ℂ ℤ) (d : ℤ) :
    (P*Q).coeff d =
    ∑ e ∈ P.coeff.support, P.coeff e * Q.coeff (d-e) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro e he
  have hEq (f : ℤ) : (e+f=d ↔ f=d-e) := by omega
  calc
    (∑ f ∈ Q.coeff.support,
      if e+f=d then P.coeff e * Q.coeff f else 0) =
        ∑ f ∈ Q.coeff.support,
          if f=d-e then P.coeff e * Q.coeff f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp only [hEq f]
    _ = if d-e ∈ Q.coeff.support then
          P.coeff e * Q.coeff (d-e) else 0 := by
      rw [Finset.sum_ite_eq']
    _ = P.coeff e * Q.coeff (d-e) := by
      by_cases hh : d-e ∈ Q.coeff.support
      · simp [hh]
      · have hz : Q.coeff (d-e) = 0 := by
          by_contra hn
          exact hh (Finsupp.mem_support_iff.mpr hn)
        simp [hh,hz]

/-- Exact coefficient recurrence for a true finite chronological
Laurent matrix action on the SAME Fock×seen state carrier. -/
theorem source_original_Laurent_actual_action_coeff434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (i : ℕ) (f : H → AddMonoidAlgebra ℂ ℤ)
    (a : H) (d : ℤ) :
    (sourceOriginalSignedLaurentAction434 M i f a).coeff d =
    ∑ b : H,
      ∑ e ∈ (M i a b).coeff.support,
        (M i a b).coeff e * (f b).coeff (d-e) := by
  unfold sourceOriginalSignedLaurentAction434
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  exact source_original_Laurent_actual_coeff_mul434 (M i a b) (f b) d

/-- Signed first-DIRTY coefficient recurrence. It keeps full
arithmetic frequency conservation at each true chronological state,
including ALL post-first-DIRTY paths and their complex interference. -/
theorem source_original_Laurent_actual_DIRTY_coeff_succ434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (n start : ℕ) (a : H) (d : ℤ) :
    (sourceOriginalSignedLaurentDirtyChain434
      C D (n+1) start f a).coeff d =
    (∑ b : H,
      ∑ e ∈ (D start a b).coeff.support,
        (D start a b).coeff e *
        (sourceOriginalSignedLaurentChain434
          (fun i x y => C i x y + D i x y)
          n (start+1) f b).coeff (d-e)) +
    (∑ b : H,
      ∑ e ∈ (C start a b).coeff.support,
        (C start a b).coeff e *
        (sourceOriginalSignedLaurentDirtyChain434
          C D n (start+1) f b).coeff (d-e)) := by
  change
    (sourceOriginalSignedLaurentAction434 D start
        (sourceOriginalSignedLaurentChain434
          (fun i x y => C i x y + D i x y)
          n (start+1) f) a +
     sourceOriginalSignedLaurentAction434 C start
        (sourceOriginalSignedLaurentDirtyChain434
          C D n (start+1) f) a).coeff d = _
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [source_original_Laurent_actual_action_coeff434]
  rw [source_original_Laurent_actual_action_coeff434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGEArithmeticConvolution -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact arithmetic single-frequency insertion:
an original physical return displacement e contributes to TOTAL
frequency d only via the signed future at complementary d-e. -/
theorem source_original_Laurent_single_future_coeff434
    (e d : ℤ) (z : ℂ) (F : AddMonoidAlgebra ℂ ℤ) :
    (AddMonoidAlgebra.single e z * F).coeff d =
      z * F.coeff (d-e) := by
  rw [source_original_Laurent_actual_coeff_mul434]
  by_cases hz : z = 0
  · simp [hz, AddMonoidAlgebra.single_zero]
  · rw [AddMonoidAlgebra.coeff_single,
      Finsupp.support_single_ne_zero e hz]
    simp [Finsupp.single_apply]

/-- TRUE G_i P_T E_i P_T with the exact original source divisor D.
Signed coefficient at total frequency d is a sum over the real
intermediate Fock×seen state and actual prime-product D, evaluated
against the SAME future F at d-orientation*k*D. This is a physical
arithmetic conservation law, not a positive-TV envelope. -/
theorem source_original_ACTUAL_GE_arithmetic_future_coeff434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (N i T : ℕ)
    (a c : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap)
    (F : AddMonoidAlgebra ℂ ℤ) (d : ℤ) :
    (sourceOriginalActualProjectedGEThetaLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k N i T a c * F).coeff d =
    ∑ b : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap,
      ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k b,
        (sourceOriginalActualSignedGhostMatrix434
          SP sm BP bm J ell cap q rho N i V mu a b *
         sourceOriginalActualSignedOLDMaskedEThetaMode434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta o k T b c D) *
          F.coeff (d-o*k*(D:ℤ)) := by
  unfold sourceOriginalActualProjectedGEThetaLaurent434
  simp only [Finset.sum_mul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro D hD
  rw [source_original_Laurent_single_future_coeff434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentStatePath -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- An ACTUAL ordered n-step path consists of the n successive
reachable Fock×seen states, rather than independently resampled
states for each source Fourier mode. -/
def sourceOriginalSignedLaurentPathWeight434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) :
    (n start : ℕ) → (a : H) → (Fin n → H) →
      AddMonoidAlgebra ℂ ℤ
  | 0, _, a, _ => f a
  | n+1, start, a, path =>
      M start a (path 0) *
        sourceOriginalSignedLaurentPathWeight434 M f
          n (start+1) (path 0) (Fin.tail path)

/-- Exact combinatorial expansion of the ORIGINAL chronological
Laurent matrix chain into genuine successive Fock×seen paths.
Each path's Laurent multiplication records the TOTAL signed
integer displacement; the actual state is passed to the next step. -/
theorem source_original_ACTUAL_signed_Laurent_state_path_sum434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (n start : ℕ) (a : H) :
    sourceOriginalSignedLaurentChain434 M n start f a =
    ∑ path : Fin n → H,
      sourceOriginalSignedLaurentPathWeight434 M f n start a path := by
  induction n generalizing start a with
  | zero =>
      simp only [sourceOriginalSignedLaurentChain434]
      simp [sourceOriginalSignedLaurentPathWeight434]
  | succ n ih =>
      change (∑ b : H, M start a b *
        sourceOriginalSignedLaurentChain434 M n (start+1) f b) = _
      rw [show
          (∑ path : Fin (n+1) → H,
            sourceOriginalSignedLaurentPathWeight434 M f (n+1) start a path) =
          ∑ pair : H × (Fin n → H),
            M start a pair.1 *
              sourceOriginalSignedLaurentPathWeight434 M f n
                (start+1) pair.1 pair.2 from by
          apply Fintype.sum_equiv
            ((Fin.consEquiv (fun _ : Fin (n+1) => H)).symm)
          intro path
          simp [sourceOriginalSignedLaurentPathWeight434]]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Prod.fst, Prod.snd]
      rw [←Finset.mul_sum,←ih (start+1) b]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentDirtyStatePath -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Complex signed amplitude on ONE fixed chronological state path,
with a CLEAN prefix, first DIRTY insertion, then FULL continuation.
Different insertion positions remain COHERENT within this SAME path. -/
def sourceOriginalSignedLaurentDirtyPathWeight434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) :
    (n start : ℕ) → (a : H) → (Fin n → H) →
      AddMonoidAlgebra ℂ ℤ
  | 0, _, _, _ => 0
  | n+1, start, a, path =>
      D start a (path 0) *
        sourceOriginalSignedLaurentPathWeight434 (fun i x y => C i x y + D i x y)
          f n (start+1) (path 0) (Fin.tail path) +
      C start a (path 0) *
        sourceOriginalSignedLaurentDirtyPathWeight434 C D f
          n (start+1) (path 0) (Fin.tail path)

/-- Exact FIRST-DIRTY state-path expansion over the ORIGINAL
chronological Fock×seen carrier. Summing true path amplitudes
commutes with the Duhamel insertion; no independent history,
positive operator or arithmetic saving is assumed. -/
theorem source_original_ACTUAL_signed_Laurent_DIRTY_state_path_sum434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (n start : ℕ) (a : H) :
    sourceOriginalSignedLaurentDirtyChain434 C D n start f a =
    ∑ path : Fin n → H,
      sourceOriginalSignedLaurentDirtyPathWeight434 C D f n start a path := by
  induction n generalizing start a with
  | zero =>
      simp [sourceOriginalSignedLaurentDirtyChain434,
        sourceOriginalSignedLaurentDirtyPathWeight434]
  | succ n ih =>
      change
        (∑ b : H, D start a b *
          sourceOriginalSignedLaurentChain434
            (fun i x y => C i x y + D i x y) n (start+1) f b) +
        (∑ b : H, C start a b *
          sourceOriginalSignedLaurentDirtyChain434 C D n (start+1) f b) = _
      calc
        _ = ∑ b : H,
          ((D start a b *
            ∑ tail : Fin n → H,
              sourceOriginalSignedLaurentPathWeight434
                (fun i x y => C i x y + D i x y) f n (start+1) b tail) +
          (C start a b *
            ∑ tail : Fin n → H,
              sourceOriginalSignedLaurentDirtyPathWeight434
                C D f n (start+1) b tail)) := by
            rw [←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b hb
            rw [source_original_ACTUAL_signed_Laurent_state_path_sum434]
            rw [ih (start+1) b]
        _ = ∑ b : H, ∑ tail : Fin n → H,
            (D start a b *
              sourceOriginalSignedLaurentPathWeight434
                (fun i x y => C i x y + D i x y) f n (start+1) b tail +
            C start a b *
              sourceOriginalSignedLaurentDirtyPathWeight434
                C D f n (start+1) b tail) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
        _ = ∑ pair : H × (Fin n → H),
              (D start a pair.1 *
                sourceOriginalSignedLaurentPathWeight434
                  (fun i x y => C i x y + D i x y)
                  f n (start+1) pair.1 pair.2 +
              C start a pair.1 *
                sourceOriginalSignedLaurentDirtyPathWeight434
                  C D f n (start+1) pair.1 pair.2) := by
            rw [Fintype.sum_prod_type]
        _ = ∑ path : Fin (n+1) → H,
            sourceOriginalSignedLaurentDirtyPathWeight434
              C D f (n+1) start a path := by
            apply Fintype.sum_equiv
              (Fin.consEquiv (fun _ : Fin (n+1) => H))
            intro pair
            have ht : Fin.tail ((Fin.consEquiv
                (fun _ : Fin (n+1) => H)) pair) = pair.2 := by
              cases pair with
              | mk b tail => rfl
            simp [sourceOriginalSignedLaurentDirtyPathWeight434, ht]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentDirtyPathGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- True complex-valued first-DIRTY Fock×seen path ensemble before
the source physical BIG baseline. Every chronological state is shared
between adjacent transitions. -/
def sourceOriginalSignedLaurentDIRTYPathEnsemble434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (w : H → ℂ) (n start : ℕ) : AddMonoidAlgebra ℂ ℤ :=
  ∑ a : H, AddMonoidAlgebra.single (0:ℤ) (w a) *
    sourceOriginalSignedLaurentDirtyChain434 C D n start f a

/-- A SINGLE actual chronological path's signed coefficient at the
TOTAL integer frequency d, including the authentic initial Fock mass
w(a) and all first-DIRTY insertion positions on that same path. -/
def sourceOriginalSignedLaurentDIRTYPathAmplitude434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (w : H → ℂ) (n start : ℕ)
    (p : H × (Fin n → H)) (d : ℤ) : ℂ :=
  w p.1 *
    (sourceOriginalSignedLaurentDirtyPathWeight434
      C D f n start p.1 p.2).coeff d

/-- Exact signed coefficient decomposition into ACTUAL first-DIRTY
state paths. The original multiple insertion positions within a path
have already interfered coherently in each coefficient. -/
theorem source_original_ACTUAL_Laurent_DIRTY_path_coeff434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (w : H → ℂ) (n start : ℕ) (d : ℤ) :
    (sourceOriginalSignedLaurentDIRTYPathEnsemble434
      C D f w n start).coeff d =
    ∑ p : H × (Fin n → H),
      sourceOriginalSignedLaurentDIRTYPathAmplitude434
        C D f w n start p d := by
  classical
  unfold sourceOriginalSignedLaurentDIRTYPathEnsemble434
  rw [AddMonoidAlgebra.coeff_sum,Finsupp.finset_sum_apply]
  calc
    _ = ∑ a : H, w a *
      (sourceOriginalSignedLaurentDirtyChain434 C D n start f a).coeff d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [source_original_Laurent_single_future_coeff434,sub_zero]
    _ = ∑ a : H, w a *
      (∑ path : Fin n → H,
        (sourceOriginalSignedLaurentDirtyPathWeight434
          C D f n start a path).coeff d) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [source_original_ACTUAL_signed_Laurent_DIRTY_state_path_sum434,
          AddMonoidAlgebra.coeff_sum,Finsupp.finset_sum_apply]
    _ = ∑ a : H, ∑ path : Fin n → H,
      w a * (sourceOriginalSignedLaurentDirtyPathWeight434
        C D f n start a path).coeff d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        rfl

/-- The actual coherent TOTAL-frequency energy is a signed
cross-path Gram: EVERY pair of chronological Fock×seen paths sharing
the SAME total integer frequency contributes star(A_p(d))*A_q(d).
Neither the off-diagonal terms nor same-frequency collisions vanish
by Fourier orthogonality. This is exact complex arithmetic. -/
theorem source_original_ACTUAL_Laurent_DIRTY_path_collision_gram434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (w : H → ℂ) (n start : ℕ) :
    let P := sourceOriginalSignedLaurentDIRTYPathEnsemble434
      C D f w n start
    (∑ d ∈ P.coeff.support,
      (((‖P.coeff d‖^2 : ℝ)) : ℂ)) =
      ∑ d ∈ P.coeff.support,
        ∑ p : H × (Fin n → H),
          ∑ q : H × (Fin n → H),
            star (sourceOriginalSignedLaurentDIRTYPathAmplitude434
              C D f w n start p d) *
              sourceOriginalSignedLaurentDIRTYPathAmplitude434
                C D f w n start q d := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  intro d hd
  let A := sourceOriginalSignedLaurentDIRTYPathAmplitude434
    C D f w n start
  have hc := source_original_ACTUAL_Laurent_DIRTY_path_coeff434
    C D f w n start d
  have hnorm (z : ℂ) :
      (((‖z‖^2 : ℝ) : ℂ)) = star z * z := by
    calc
      _ = z * star z := by
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.mul_conj z).symm
      _ = _ := mul_comm _ _
  rw [hnorm, hc]
  calc
    star (∑ p : H × (Fin n → H), A p d) *
        (∑ q : H × (Fin n → H), A q d) =
      (∑ p : H × (Fin n → H), star (A p d)) *
        (∑ q : H × (Fin n → H), A q d) := by
          rw [star_sum]
    _ = ∑ p : H × (Fin n → H),
          ∑ q : H × (Fin n → H),
            star (A p d) * A q d := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentDIRTYPathModeRecurrence -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- SAME fixed Fock×seen path: after choosing its first DIRTY event,
the arithmetic TOTAL-frequency condition is the original frequency
minus the exact local signed Fourier exponent. No independent
future-state averaging is introduced. -/
theorem source_original_ACTUAL_Laurent_DIRTY_path_mode_succ434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (n start : ℕ) (a : H) (path : Fin (n+1) → H) (d : ℤ) :
    (sourceOriginalSignedLaurentDirtyPathWeight434
      C D f (n+1) start a path).coeff d =
    (∑ e ∈ (D start a (path 0)).coeff.support,
      (D start a (path 0)).coeff e *
        (sourceOriginalSignedLaurentPathWeight434
          (fun i x y => C i x y + D i x y)
          f n (start+1) (path 0) (Fin.tail path)).coeff (d-e)) +
    (∑ e ∈ (C start a (path 0)).coeff.support,
      (C start a (path 0)).coeff e *
        (sourceOriginalSignedLaurentDirtyPathWeight434
          C D f n (start+1) (path 0) (Fin.tail path)).coeff (d-e)) := by
  change (D start a (path 0) *
      sourceOriginalSignedLaurentPathWeight434
        (fun i x y => C i x y + D i x y) f n (start+1)
        (path 0) (Fin.tail path) +
    C start a (path 0) *
      sourceOriginalSignedLaurentDirtyPathWeight434
        C D f n (start+1) (path 0) (Fin.tail path)).coeff d = _
  rw [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  rw [source_original_Laurent_actual_coeff_mul434]
  rw [source_original_Laurent_actual_coeff_mul434]

/-- Pointwise (fixed TOTAL integer frequency d) exact complex Gram
identity for REAL chronological Fock×seen path pairs.
No diagonal simplification or artificial independence of histories. -/
theorem source_original_ACTUAL_Laurent_DIRTY_path_gram_at_frequency434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (w : H → ℂ) (n start : ℕ) (d : ℤ) :
    let P := sourceOriginalSignedLaurentDIRTYPathEnsemble434 C D f w n start
    (((‖P.coeff d‖^2 : ℝ)) : ℂ) =
    ∑ p : H × (Fin n → H),
      ∑ q : H × (Fin n → H),
        star (sourceOriginalSignedLaurentDIRTYPathAmplitude434
          C D f w n start p d) *
        sourceOriginalSignedLaurentDIRTYPathAmplitude434
          C D f w n start q d := by
  classical
  dsimp only
  let A := sourceOriginalSignedLaurentDIRTYPathAmplitude434 C D f w n start
  have hc := source_original_ACTUAL_Laurent_DIRTY_path_coeff434 C D f w n start d
  have hnorm (z : ℂ) :
      (((‖z‖^2 : ℝ) : ℂ)) = star z * z := by
    calc
      _ = z * star z := by
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.mul_conj z).symm
      _ = _ := mul_comm _ _
  rw [hnorm,hc]
  calc
    star (∑ p : H × (Fin n → H), A p d) *
        (∑ q : H × (Fin n → H), A q d) =
      (∑ p : H × (Fin n → H), star (A p d)) *
        (∑ q : H × (Fin n → H), A q d) := by
          rw [star_sum]
    _ = ∑ p : H × (Fin n → H),
          ∑ q : H × (Fin n → H),
            star (A p d) * A q d := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentChronologicalSpectralRadius -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact signed coefficient convolution implies an additive
FREQUENCY RADIUS bound. It applies to true complex Laurent products,
without positive replacement or independent future samples. -/
theorem source_original_Laurent_signed_convolution_radius434
    (P Q : AddMonoidAlgebra ℂ ℤ) (B E : ℕ)
    (hP : ∀ e : ℤ, P.coeff e ≠ 0 → e.natAbs ≤ B)
    (hQ : ∀ e : ℤ, Q.coeff e ≠ 0 → e.natAbs ≤ E)
    (d : ℤ) (hne : (P*Q).coeff d ≠ 0) :
    d.natAbs ≤ B+E := by
  rw [source_original_Laurent_actual_coeff_mul434] at hne
  have he : ∃ e ∈ P.coeff.support,
      P.coeff e * Q.coeff (d-e) ≠ 0 := by
    by_contra hn
    have hz : (∑ e ∈ P.coeff.support,
        P.coeff e * Q.coeff (d-e)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      by_contra hprod
      exact hn ⟨e,he,hprod⟩
    exact hne hz
  obtain ⟨e,he,hprod⟩ := he
  have heB := hP e (left_ne_zero_of_mul hprod)
  have hfE := hQ (d-e) (right_ne_zero_of_mul hprod)
  have hTriangle := Int.natAbs_add_le (d-e) e
  have hsum : (d-e)+e = d := by omega
  rw [hsum] at hTriangle
  omega

/-- For a fixed REAL sequence of chronological states, the
SIGNED full Laurent path has total frequency at most n times
a uniform physical step radius plus its terminal radius. -/
theorem source_original_Laurent_actual_FULL_path_radius434
    {H : Type} [Fintype H]
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (B E : ℕ)
    (hM : ∀ i a b e, (M i a b).coeff e ≠ 0 → e.natAbs ≤ B)
    (hf : ∀ a e, (f a).coeff e ≠ 0 → e.natAbs ≤ E) :
    ∀ n start a (path : Fin n → H) d,
      (sourceOriginalSignedLaurentPathWeight434 M f n start a path).coeff d ≠ 0 →
      d.natAbs ≤ n*B+E := by
  intro n
  induction n with
  | zero =>
    intro start a path d hn
    change (f a).coeff d ≠ 0 at hn
    simpa using hf a d hn
  | succ n ih =>
    intro start a path d hn
    change (M start a (path 0) *
      sourceOriginalSignedLaurentPathWeight434 M f n
        (start+1) (path 0) (Fin.tail path)).coeff d ≠ 0 at hn
    have hr := source_original_Laurent_signed_convolution_radius434
      (M start a (path 0))
      (sourceOriginalSignedLaurentPathWeight434 M f n
        (start+1) (path 0) (Fin.tail path))
      B (n*B+E) (hM start a (path 0))
      (ih (start+1) (path 0) (Fin.tail path))
      d hn
    calc
      d.natAbs ≤ B+(n*B+E) := hr
      _ = (n+1)*B+E := by simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Both true CLEAN and DIRTY projected matrices obey the same
per-step frequency radius. Their sum is the actual post-first-DIRTY
FULL physical transition, not an independently sampled kernel. -/
theorem source_original_Laurent_actual_DIRTY_path_radius434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (B E : ℕ)
    (hC : ∀ i a b e, (C i a b).coeff e ≠ 0 → e.natAbs ≤ B)
    (hD : ∀ i a b e, (D i a b).coeff e ≠ 0 → e.natAbs ≤ B)
    (hf : ∀ a e, (f a).coeff e ≠ 0 → e.natAbs ≤ E) :
    ∀ n start a (path : Fin n → H) d,
      (sourceOriginalSignedLaurentDirtyPathWeight434
        C D f n start a path).coeff d ≠ 0 →
      d.natAbs ≤ n*B+E := by
  have hCD (i : ℕ) (a b : H) (e : ℤ)
      (hne : (C i a b+D i a b).coeff e ≠ 0) : e.natAbs ≤ B := by
    by_cases hc : (C i a b).coeff e = 0
    · have hd : (D i a b).coeff e ≠ 0 := by
        simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
          hc,zero_add] using hne
      exact hD i a b e hd
    · exact hC i a b e hc
  intro n
  induction n with
  | zero =>
    intro start a path d hn
    simp [sourceOriginalSignedLaurentDirtyPathWeight434] at hn
  | succ n ih =>
    intro start a path d hn
    let PF := sourceOriginalSignedLaurentPathWeight434
      (fun i x y => C i x y + D i x y) f n
        (start+1) (path 0) (Fin.tail path)
    let PD := sourceOriginalSignedLaurentDirtyPathWeight434
      C D f n (start+1) (path 0) (Fin.tail path)
    have ht : (D start a (path 0)*PF + C start a (path 0)*PD).coeff d ≠ 0 := by
      simpa only [sourceOriginalSignedLaurentDirtyPathWeight434,PF,PD] using hn
    rw [AddMonoidAlgebra.coeff_add,Finsupp.add_apply] at ht
    have hh : (D start a (path 0)*PF).coeff d ≠ 0 ∨
        (C start a (path 0)*PD).coeff d ≠ 0 := by
      by_contra h
      push_neg at h
      exact ht (by simp [h.1,h.2])
    rcases hh with hd | hc
    · have hP : ∀ e : ℤ, PF.coeff e ≠ 0 → e.natAbs ≤ n*B+E := by
        intro e he
        exact source_original_Laurent_actual_FULL_path_radius434
          (fun i x y => C i x y+D i x y) f B E hCD hf
          n (start+1) (path 0) (Fin.tail path) e he
      have hr := source_original_Laurent_signed_convolution_radius434
        (D start a (path 0)) PF B (n*B+E)
        (hD start a (path 0)) hP d hd
      calc
        d.natAbs ≤ B+(n*B+E) := hr
        _ = (n+1)*B+E := by simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · have hP : ∀ e : ℤ, PD.coeff e ≠ 0 → e.natAbs ≤ n*B+E := by
        intro e he
        exact ih (start+1) (path 0) (Fin.tail path) e he
      have hr := source_original_Laurent_signed_convolution_radius434
        (C start a (path 0)) PD B (n*B+E)
        (hC start a (path 0)) hP d hc
      calc
        d.natAbs ≤ B+(n*B+E) := hr
        _ = (n+1)*B+E := by simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
end Green64Analytic.CorrelationSquare

end

end

