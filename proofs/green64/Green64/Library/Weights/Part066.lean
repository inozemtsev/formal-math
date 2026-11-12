module

public import Green64.Library.Correlation.Part052
public import Green64.Library.Correlation.Part049

@[expose] public section

/-!
# Weights / Part066

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedFiniteMatrixAlgebra -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Basis vector at the EXACT original state: both output and
cumulative chronological history are part of the basis index. -/
def sourceOriginalSignedFiniteDelta434 {H : Type} [DecidableEq H]
    (b : H) : H → ℂ :=
  fun t => if t=b then 1 else 0

/-- Every test on a finite signed history carrier is exactly the sum
of its coordinate values on actual Fock × seen basis states. -/
theorem source_original_signed_finite_delta_expand434
    {H : Type} [Fintype H] [DecidableEq H] (f : H → ℂ) :
    (fun t => ∑ b : H, f b * sourceOriginalSignedFiniteDelta434 b t) = f := by
  classical
  funext t
  simp [sourceOriginalSignedFiniteDelta434]

/-- The exact finite complex kernel of ANY linear history operator.
No absolute values, independent histories or Markov approximation. -/
def sourceOriginalSignedFiniteMatrix434 {H : Type} [Fintype H] [DecidableEq H]
    (T : (H → ℂ) → H → ℂ) (a b : H) : ℂ :=
  T (sourceOriginalSignedFiniteDelta434 b) a

/-- Finite sum commutes with ANY additive signed observable on the
true finite Fock×seen state carrier. -/
theorem source_original_signed_finite_operator_sum434
    {H : Type} [Fintype H] [DecidableEq H]
    (T : (H → ℂ) → ℂ)
    (hadd : ∀ f g, T (fun t => f t+g t) = T f+T g)
    (hzero : T (fun _ => 0) = 0)
    (g : H → H → ℂ) (s : Finset H) :
    T (fun t => ∑ b ∈ s, g b t) = ∑ b ∈ s, T (g b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using hzero
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      calc
        T (fun t => g a t + ∑ b ∈ s, g b t) =
          T (g a) + T (fun t => ∑ b ∈ s, g b t) :=
            hadd (g a) (fun t => ∑ b ∈ s, g b t)
        _ = T (g a) + ∑ b ∈ s, T (g b) := by rw [ih]

/-- Exact signed matrix representation of a linear finite-history
operator. The kernel remembers the actual joint state (Fock, seen). -/
theorem source_original_signed_finite_matrix_apply434
    {H : Type} [Fintype H] [DecidableEq H]
    (T : (H → ℂ) → H → ℂ)
    (hadd : ∀ f g a, T (fun t => f t+g t) a = T f a+T g a)
    (hsmul : ∀ c f a, T (fun t => c*f t) a = c*T f a)
    (hzero : ∀ a, T (fun _ => 0) a = 0)
    (f : H → ℂ) (a : H) :
    T f a = ∑ b : H, sourceOriginalSignedFiniteMatrix434 T a b * f b := by
  classical
  have he := (source_original_signed_finite_delta_expand434 f).symm
  have hs := source_original_signed_finite_operator_sum434
    (fun g : H → ℂ => T g a)
    (fun u v => hadd u v a) (hzero a)
    (fun b t => f b * sourceOriginalSignedFiniteDelta434 b t) Finset.univ
  calc
    T f a = T (fun t => ∑ b : H,
        f b * sourceOriginalSignedFiniteDelta434 b t) a :=
          congrArg (fun g : H → ℂ => T g a) he
    _ = ∑ b : H, T (fun t => f b * sourceOriginalSignedFiniteDelta434 b t) a := hs
    _ = ∑ b : H, f b * T (sourceOriginalSignedFiniteDelta434 b) a := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hsmul (f b) (sourceOriginalSignedFiniteDelta434 b) a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [sourceOriginalSignedFiniteMatrix434,mul_comm]

/-- Exact signed finite prefix/suffix pairing: the outgoing prefix
density is the TRANSPOSE of the literal finite kernel, with no
absolute value or arbitrary history supremum. -/
theorem source_original_signed_finite_matrix_pairing434
    {H : Type} [Fintype H] [DecidableEq H]
    (T : (H → ℂ) → H → ℂ)
    (hadd : ∀ f g a, T (fun t => f t+g t) a = T f a+T g a)
    (hsmul : ∀ c f a, T (fun t => c*f t) a = c*T f a)
    (hzero : ∀ a, T (fun _ => 0) a = 0)
    (w f : H → ℂ) :
    (∑ a : H, w a * T f a) =
      ∑ b : H, (∑ a : H,
        w a * sourceOriginalSignedFiniteMatrix434 T a b) * f b := by
  classical
  calc
    _ = ∑ a : H, w a * ∑ b : H,
        sourceOriginalSignedFiniteMatrix434 T a b * f b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [source_original_signed_finite_matrix_apply434 T hadd hsmul hzero f a]
    _ = ∑ a : H, ∑ b : H,
        (w a * sourceOriginalSignedFiniteMatrix434 T a b) * f b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ b : H, ∑ a : H,
        (w a * sourceOriginalSignedFiniteMatrix434 T a b) * f b := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEMatrixDef -/

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

/-- Exact signed source E frame matrix on finite reachable Fock×seen
states. The literal keep may select true CLEAN, DIRTY or full E. -/
def sourceOriginalActualSignedEMatrix434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) :
    H → H → ℂ :=
  sourceOriginalSignedFiniteMatrix434
    (sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEThetaModes -/

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

/-- The TRUE source E kernel's finite divisor support at an actual
reachable Fock×seen input. SAME support for theta and theta=0. -/
def sourceOriginalActualSignedEThetaSupport434
    (o k : ℤ) (a : H) : Finset ℕ :=
  sourceOriginalActualFrameThetaSupport434 SP sm BP bm J ell m cap patterns
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
    a.val.2 o k

/-- Exact complex signed coefficient of physical E(a,b) at divisor D:
the original E is applied to the ONE actual Fock×seen basis vector.
All RAW/comparison K and numerical history restrictions survive. -/
def sourceOriginalActualSignedEThetaMode434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (a b : H) (D : ℕ) : ℂ :=
  sourceOriginalActualFrameThetaDMode434 SP sm BP bm J ell m cap patterns
    keep q rho Vs V mu K zeta o k
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
    a.val.2
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalSignedFiniteDelta434 b)) D

/-- Every entry of the LITERAL signed finite E matrix is an exact finite
Fourier polynomial of the ORIGINAL source divisor phase. Both
Fock and chronological seen are retained in the matrix indices. -/
theorem source_original_ACTUAL_signed_E_theta_modes434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (a b : H) :
    sourceOriginalActualSignedEMatrix434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k a b =
    ∑ D ∈ sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k a,
      sourceOriginalActualSignedEThetaMode434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta o k a b D *
      originalReturnPhase theta o k D := by
  unfold sourceOriginalActualSignedEMatrix434
    sourceOriginalSignedFiniteMatrix434
    sourceOriginalActualSignedFiniteE434
  exact source_original_ACTUAL_frame_E_theta_D_modes434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
    zeta theta o k
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
    a.val.2
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalSignedFiniteDelta434 b))
end Green64Analytic.CorrelationSquare

end

end

