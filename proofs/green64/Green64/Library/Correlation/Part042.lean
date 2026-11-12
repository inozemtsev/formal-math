module

public import Green64.Library.Weights.FiniteMatrixArray
public import Green64.Library.Correlation.Part041
public import Green64.Library.Correlation.B26FrozenCleanPhysicalFourier
public import Green64.Library.Weights.Part042
public import Green64.Library.Analysis.Estimates.Part010

@[expose] public section

/-!
# Correlation / Part042

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalMatrixMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

/-- A two-periodic sequence of row matrices is exactly a power of its
first ordered pair; no commuting or self-adjointness premise is used. -/
theorem b650_matrix_chain_period_two434 {X : Type} [Fintype X] [DecidableEq X]
    (T : ℕ → Matrix X X ℂ) (hT : ∀ i, T (i+2)=T i) (R s : ℕ) :
    b650MatrixChain434 T (2*R) s = (T s * T (s+1))^R := by
  induction R generalizing s with
  | zero => simp [b650MatrixChain434]
  | succ R ih =>
    rw [Nat.mul_succ]
    change T s * (T (s+1) * b650MatrixChain434 T (2*R) (s+1+1)) =
      (T s * T (s+1))^(R+1)
    rw [ih]
    have h0 : T (s+1+1)=T s := by simpa only [Nat.add_assoc] using hT s
    have h1 : T (s+1+1+1)=T (s+1) := by simpa only [Nat.add_assoc] using hT (s+1)
    rw [h0,h1,pow_succ']
    exact (mul_assoc _ _ _).symm

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local instance b650MomentFrameFintype434 :
    Fintype (MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- The literal physical alternating rows are exactly (A A*)^R.
The backward matrix is the proved whole original physical adjoint. -/
theorem b650_physical_matrix_chain_moment434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) (R : ℕ) :
    b650MatrixChain434
      (fun i => b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta (physicalAlternatingSign i) k) (2*R) 0 =
    (b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta 1 k *
      (b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta 1 k).conjTranspose)^R := by
  rw [b650_matrix_chain_period_two434]
  · simp only [physicalAlternatingSign,show Even 0 by decide,ite_true,
      Nat.zero_add,show ¬ Even 1 by decide,ite_false]
    rw [b650_integer_matrix_adjoint434]
  · intro i
    have hsign : physicalAlternatingSign (i+2)=physicalAlternatingSign i := by
      simp [physicalAlternatingSign,Nat.even_add]
    rw [hsign]

/-- Complete exact physical moment array expansion. All frame draws,
all physical positions and all target marks remain in the sum. The two
endpoint functions may test only POSITION return, not mark return. -/
theorem b650_physical_matrix_moment_array434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) (R : ℕ)
    (a b : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions → ℂ) :
    let A := b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta 1 k
    (∑ x, a x * (((A*A.conjTranspose)^R).mulVec b) x) =
    ∑ states : Fin (2*R+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions,
      ∑ frames : Fin (2*R) → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        a (states 0) *
          (∏ i : Fin (2*R), b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns
            positions q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
            (states i.castSucc) (states i.succ) (frames i)) *
        b (states (Fin.last (2*R))) := by
  dsimp only
  rw [← b650_physical_matrix_chain_moment434 SP smallMod BP bigMod J ell m patterns
    positions q Vsmall Vbig Knu zeta k R]
  have hh := b650_matrix_chain_frame_array434
    (fun i x y f => b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns
      positions q Vsmall Vbig Knu zeta (physicalAlternatingSign i) k x y f)
    (2*R) 0 a b
  change (∑ x, a x *
    ((b650MatrixChain434
      (fun i => b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta (physicalAlternatingSign i) k) (2*R) 0).mulVec b) x) = _ at hh
  simpa only [Nat.zero_add] using hh
end Green64FullPhysicalE

end

end

/-! ## PhysicalRootArray -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local instance b650RootArrayFrameFintype434 :
    Fintype (MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- Original physical row operator in a finite signed integer window. -/
def b650IntegerPhysicalOperator434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) :
    EuclideanSpace ℂ (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) →ₗ[ℂ]
    EuclideanSpace ℂ (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) :=
  (b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
    q Vsmall Vbig Knu zeta 1 k).toEuclideanLin

/-- The source vector of ALL ordered marks at one position, with the
original physical state mass. Its norm is allowed to depend on n. -/
def b650IntegerPhysicalRoot434 (positions : Finset ℤ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (n : ℤ) :
    EuclideanSpace ℂ (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) :=
  b650PositionRoot434 (fun x => x.val.1.val)
    (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig) n

/-- Source-exact moment-to-array identity. The root tests only equality
of the first and last physical POSITIONS to n. Both final mark lists
remain free. Both original V^-M masses appear once outside the full
array sum; no independent Haar mass or mark-fibre normalization occurs. -/
theorem b650_physical_root_moment_array434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (hVs : ∀ g, 0 < Vsmall g) (hVb : ∀ g, 0 < Vbig g)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) (R : ℕ) (n : ℤ) :
    let A := b650IntegerPhysicalOperator434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta k
    let u := b650IntegerPhysicalRoot434 SP smallMod BP bigMod J ell positions Vsmall Vbig n
    inner ℂ u (((A.comp A.adjoint)^R) u) =
    (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ) *
      ∑ states : Fin (2*R+1) →
        B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions,
      ∑ frames : Fin (2*R) → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        if (states 0).val.1.val=n ∧ (states (Fin.last (2*R))).val.1.val=n then
          ∏ i : Fin (2*R), b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns
            positions q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
            (states i.castSucc) (states i.succ) (frames i)
        else 0 := by
  dsimp only [b650IntegerPhysicalOperator434,b650IntegerPhysicalRoot434]
  rw [b650_euclidean_positive_moment434]
  rw [b650_position_root_pairing434 _ _
    (le_of_lt (b650_integer_state_mass_positive434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig hVs hVb))]
  rw [b650_physical_matrix_moment_array434 SP smallMod BP bigMod J ell m patterns
    positions q Vsmall Vbig Knu zeta k R]
  congr 1
  apply Finset.sum_congr rfl
  intro states hs
  apply Finset.sum_congr rfl
  intro frames hf
  by_cases h0 : (states 0).val.1.val=n <;>
    by_cases hN : (states (Fin.last (2*R))).val.1.val=n <;>
    simp only [h0,hN,ite_true,ite_false,and_self,and_false,false_and,one_mul,mul_one,
      zero_mul,mul_zero]
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalActualOrientedComparisonResidual -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Actual comparison residual in the ORIGINAL oriented edge scalar with
a fixed positive SMALL/shared divisor c. The auxiliary/active ban is NOT
inserted here: its actual collision remainder is a separate obligation. -/
noncomputable def sourceOriginalProbeOrientedDivisorError434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ) (c : ℕ)
    (ζ theta : ℝ) (o k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  (∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    originalEdgeScalar
      (sourceOriginalActualPrimitiveComparisonKernel434 Q
        (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
        (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
        hA hB (sourceOriginalProbeCellA434 m P V ν hA)
        (sourceOriginalProbeCellB434 m P V ν hB)
        (sourceOriginalGramPrimeProduct434 SA ab.1) XA
        (sourceOriginalGramPrimeProduct434 SB ab.2) XB (ν.1.card+ν.2.card))
      ζ theta (c*(sourceOriginalGramPrimeProduct434 SA ab.1 *
        sourceOriginalGramPrimeProduct434 SB ab.2)) o k) -
    originalEdgeScalar σ ζ theta (c*(XA*XB)) o k

/-- Exact whole-residual conjugation. In particular the complex Knu
is conjugated as required by the original negative orientation. -/
theorem source_original_probe_oriented_divisor_negative434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ) (c : ℕ) (ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeOrientedDivisorError434
      J ell m hmJ ν P V Q hA hB xi c ζ theta (-1) k source target =
    star (sourceOriginalProbeOrientedDivisorError434
      J ell m hmJ ν P V Q hA hB xi c ζ theta 1 k source target) := by
  unfold sourceOriginalProbeOrientedDivisorError434
  dsimp only
  simp only [source_original_edge_scalar_negative_conjugate434,
    star_sub,star_sum,star_mul,Complex.star_def,Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro ab hab
  ring

/-- The original full physical divisor phase transfers exactly to the
proved comparison at frequency -c*theta, with a unit Mellin scalar.
This is uniform in c; it does not require c to be polynomially bounded. -/
theorem source_original_probe_oriented_divisor_positive434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hPositive : ∀ g p, p ∈ P g → 0<p)
    (Q : ℕ) (hA hB xi : ℝ) (c : ℕ) (hc : 0<c)
    (ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hSource : 0 < sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
    (hTarget : 0 < sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) :
    sourceOriginalProbeOrientedDivisorError434
      J ell m hmJ ν P V Q hA hB xi c ζ theta 1 k source target =
    sourceOriginalPureMellinPhase434 ζ c *
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k source target := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  have haux (ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB) :
      0 < sourceOriginalGramPrimeProduct434 SA ab.1 *
        sourceOriginalGramPrimeProduct434 SB ab.2 :=
    Nat.mul_pos
      (Finset.prod_pos (fun z _ => hPositive z.val.1 _ (ab.1 z).property))
      (Finset.prod_pos (fun z _ => hPositive z.val.1 _ (ab.2 z).property))
  unfold sourceOriginalProbeOrientedDivisorError434
    sourceOriginalProbeSignedMajorFourierError434
  dsimp only
  rw [source_original_edge_scalar_positive_divisor434
    _ ζ theta k c _ hc (Nat.mul_pos hTarget hSource)]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ab hab
  rw [source_original_edge_scalar_positive_divisor434 _ ζ theta k c _ hc (haux ab)]
  unfold sourceOriginalPureMellinPhase434
  ring

/-- The literal physical bilinear pairing with this divisor scalar.
Both full endpoint laws and arbitrary mark-dependent tests are unchanged. -/
theorem source_original_probe_oriented_divisor_pair_norm434
    {G X : Type} [DecidableEq G] [Fintype X]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hPositive : ∀ g p, p ∈ P g → 0<p)
    (Q : ℕ) (hA hB xi : ℝ) (c : ℕ) (hc : 0<c)
    (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (src tgt : X → ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hSrc : ∀ s, 0 < sourceOriginalProbeFreeSourceX434 J ell m hmJ ν (src s))
    (hTgt : ∀ t, 0 < sourceOriginalProbeFreeTargetX434 J ell m hmJ ν (tgt t))
    (w : X → ℝ) (f g : X → ℂ) :
    ‖(∑ ab : X × X, ((w ab.1*w ab.2:ℝ):ℂ)*star (f ab.1)*g ab.2*
      sourceOriginalProbeOrientedDivisorError434
        J ell m hmJ ν P V Q hA hB xi c ζ theta o k (src ab.1) (tgt ab.2))‖ =
    ‖(∑ ab : X × X, ((w ab.1*w ab.2:ℝ):ℂ)*
      star ((if o=1 then f else fun s => star (f s)) ab.1)*
      ((if o=1 then g else fun t => star (g t)) ab.2)*
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k
        (src ab.1) (tgt ab.2))‖ := by
  classical
  have he (s t : X) := source_original_probe_oriented_divisor_positive434
    J ell m hmJ ν P V hPositive Q hA hB xi c hc ζ theta k
    (src s) (tgt t) (hSrc s) (hTgt t)
  rcases ho with rfl | rfl
  · simp only [ite_true]
    simp_rw [he]
    have hm (ab : X × X) :
        ((w ab.1*w ab.2:ℝ):ℂ)*star (f ab.1)*g ab.2*
          (sourceOriginalPureMellinPhase434 ζ c *
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k
              (src ab.1) (tgt ab.2)) =
        sourceOriginalPureMellinPhase434 ζ c *
          (((w ab.1*w ab.2:ℝ):ℂ)*star (f ab.1)*g ab.2*
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k
              (src ab.1) (tgt ab.2)) := by ring
    simp_rw [hm]
    rw [← Finset.mul_sum,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
  · simp only [show (-1:ℤ) ≠ 1 by norm_num,ite_false]
    simp_rw [source_original_probe_oriented_divisor_negative434,he]
    have hm (ab : X × X) :
        ((w ab.1*w ab.2:ℝ):ℂ)*star (f ab.1)*g ab.2*
          star (sourceOriginalPureMellinPhase434 ζ c *
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k
              (src ab.1) (tgt ab.2)) =
        star (sourceOriginalPureMellinPhase434 ζ c) *
          star (((w ab.1*w ab.2:ℝ):ℂ)*star (star (f ab.1))*star (g ab.2)*
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ (-(c:ℝ)*theta) k
              (src ab.1) (tgt ab.2)) := by
      simp only [star_mul,star_star,Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
      ring
    simp_rw [hm]
    rw [← Finset.mul_sum,← star_sum,norm_mul,norm_star,norm_star,
      source_original_pure_mellin_phase_norm_one434,one_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalGlobalOrientedComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- PROVED complete physical comparison for both literal original orientations
and every positive frozen SMALL/shared divisor. The threshold precedes c.
The actual auxiliary/active ban and full CLEAN reconstruction remain separate. -/
theorem eventually_source_original_CANONICAL_GLOBAL_ORIENTED_DIVISOR_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H Bgoal : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D)
    (hSumBudget : Bgoal+(2*dscale+4)+2 ≤ Bsave) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (hQlower : L^D ≤ (Qchar:ℝ))
      (c : ℕ) (hc : 0<c) (o : ℤ) (ho : o=1 ∨ o= -1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : β) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    ∀ (sourceTest targetTest : X → ℂ),
    let ES : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
    let ET : ℝ := ∑ v : X, w v*‖targetTest v‖^2
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) * star (sourceTest ab.1)*targetTest ab.2 *
        (sourceOriginalProbeOrientedDivisorError434
            J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi c ζ theta o k
            (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
         ))‖^2 ≤ L^(-Bgoal)*ES*ET := by
  obtain ⟨Y0,hBase⟩ :=
    eventually_source_original_CANONICAL_GLOBAL_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bgoal
      hgamma hd hD hB hH hCs hC4 hWidthBudget hDropBudget hExponent hMinorBudget hSumBudget
  refine ⟨Y0,?_⟩
  filter_upwards [hBase] with L hGlobal
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower c hc o ho
  intro sourceTest targetTest
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : β) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let vals : X → ∀ g, Fin (t g) → ℕ := fun s g i => (s g i).val
  let f : X → ℂ := if o=1 then sourceTest else fun s => star (sourceTest s)
  let g : X → ℂ := if o=1 then targetTest else fun v => star (targetTest v)
  have hPositive (g : β) (p : ℕ) (hp : p ∈ d.Tb g) : 0<p :=
    (d.hTbPrime g p hp).pos
  have hOutputs (s : X) :=
    source_original_actual_free_outputs_positive434 J ell m hmJ ν d.Tb hPositive s
  have hNorm := source_original_probe_oriented_divisor_pair_norm434
    (G := β) (X := X) J ell m hmJ ν d.Tb d.Vbig hPositive
    Qchar hA hB xi c hc ζ theta o k ho vals vals
    (fun s => (hOutputs s).1) (fun s => (hOutputs s).2)
    w sourceTest targetTest
  have hSaved := @hGlobal ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ (-(c:ℝ)*theta) k hZeta hQlower f g
  change ‖(∑ ab : X × X, ((w ab.1*w ab.2:ℝ):ℂ)*star (f ab.1)*g ab.2*
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ (-(c:ℝ)*theta) k
        (vals ab.1) (vals ab.2))‖^2 ≤
      L^(-Bgoal)*(∑ s : X,w s*‖f s‖^2)*(∑ v : X,w v*‖g v‖^2) at hSaved
  have hEf : (∑ s : X,w s*‖f s‖^2) = ∑ s : X,w s*‖sourceTest s‖^2 := by
    by_cases ho1 : o=1 <;> simp only [f,ho1,ite_true,ite_false,norm_star]
  have hEg : (∑ v : X,w v*‖g v‖^2) = ∑ v : X,w v*‖targetTest v‖^2 := by
    by_cases ho1 : o=1 <;> simp only [g,ho1,ite_true,ite_false,norm_star]
  change ‖(∑ ab : X × X, ((w ab.1*w ab.2:ℝ):ℂ)*star (sourceTest ab.1)*
      targetTest ab.2*sourceOriginalProbeOrientedDivisorError434
        J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi c ζ theta o k
        (vals ab.1) (vals ab.2))‖^2 ≤
      L^(-Bgoal)*(∑ s : X,w s*‖sourceTest s‖^2)*(∑ v : X,w v*‖targetTest v‖^2)
  rw [hNorm]
  rw [hEf,hEg] at hSaved
  exact hSaved
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeMemoryPattern -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The canonical two-block probe is an ACTUAL original Memory pattern,
with its real freed first-J slots and original per-group bound m. -/
noncomputable def sourceOriginalProbeMemoryPattern434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) : SourcePattern G J m where
  free := sourceOriginalProbeFreedSlots434 J m hmJ ν
  free_bound := source_original_probe_freed_card_le_m434 J m hmJ ν

/-- The literal Memory shared-copy slots equal the source comparison
shared slots. This includes the last-ell exclusion and original indices. -/
theorem source_original_probe_memory_shared_slots434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g =
      sourceOriginalProbeSharedSlots434 J ell m hmJ ν g := by
  classical
  let C := sourceOriginalProbeFreedSlots434 J m hmJ ν g
  ext i
  change (i ∈ Finset.univ.filter (fun i : Fin (J+ell) =>
      i.val < J ∧ i.val ∉ C.image Fin.val)) ↔
    i ∈ (Finset.univ \ C).image (fun j : Fin J => j.castAdd ell)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨hi,hnot⟩
    let j : Fin J := ⟨i.val,hi⟩
    have hj : j ∉ C := by
      intro hj
      exact hnot ⟨j,hj,rfl⟩
    exact ⟨j,hj,Fin.ext rfl⟩
  · rintro ⟨j,hj,hji⟩
    have hv : j.val=i.val := congrArg Fin.val hji
    refine ⟨by omega,?_⟩
    rintro ⟨z,hz,hzi⟩
    have he : z=j := Fin.ext (hzi.trans hv.symm)
    exact hj (he ▸ hz)

/-- Every original Memory free coordinate is the actual comparison
coordinate through the already verified canonical slot bijection. -/
noncomputable def sourceOriginalProbeMemoryFreeEquiv434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) ≃
      {i : Fin (J+ell) //
        i ∉ sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g} :=
  (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g).trans
    (Equiv.subtypeEquivRight (fun i => by rw [source_original_probe_memory_shared_slots434]))

/-- The ACTUAL Memory auxiliary mass is precisely the original harmonic
product on its labelled freed slots; no injectivity or tilting occurs. -/
theorem source_original_probe_memory_aux_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bigMod : (g : G) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
    (J m : ℕ) (hmJ : m≤J) (ν : SourceOriginalProbePattern434 G m)
    (V : G → ℝ)
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    sourceAuxMass BP bigMod J m V (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux =
      ∏ g : G, ∏ j : (sourceOriginalProbeFreedSlots434 J m hmJ ν g),
        sourcePrimeSharedAtom434 (V g) (bigMod g (aux g j)) := by
  simp only [sourceAuxMass,sourcePrimeSharedAtom434,mul_comm]
  rfl

/-- Exact separation of the literal B26 frozen divisor into a shared
constant and the genuine freed auxiliary product, with all multiplicities. -/
theorem source_original_probe_memory_frozen_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bigMod : (g : G) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
    (J ell m : ℕ) (hmJ : m≤J) (ν : SourceOriginalProbePattern434 G m)
    (dsmall : ℕ)
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (a : SourceOriginalB26Active434 BP J ell)
    (sigma : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a sigma =
    (dsmall * ∏ g : G, ∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g,
      bigMod g (a g (sigma g i))) *
    (∏ g : G, ∏ j : (sourceOriginalProbeFreedSlots434 J m hmJ ν g),
      bigMod g (aux g j)) := by
  unfold sourceOriginalB26FrozenD434
  simp_rw [source_original_probe_memory_shared_slots434]
  rw [Finset.prod_mul_distrib]
  simp only [mul_assoc]
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeMemoryAuxReindex -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Every selected A/B auxiliary coordinate occupies its actual group and
first-J freed slot in the original Memory pattern. -/
noncomputable def sourceOriginalProbeMemoryAuxSlot434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) :
    SourceOriginalProbeAuxIndex434 m ν →
      (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g) := by
  intro z
  cases z with
  | inl a =>
    exact ⟨a.val.1,⟨a.val.2.castLE hmJ,
      (source_original_probe_freed_first_m_iff434 J m hmJ ν _ _).2 (Or.inl a.property)⟩⟩
  | inr b =>
    exact ⟨b.val.1,⟨b.val.2.castLE hmJ,
      (source_original_probe_freed_first_m_iff434 J m hmJ ν _ _).2 (Or.inr b.property)⟩⟩

theorem source_original_probe_memory_aux_slot_bijective434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2) :
    Function.Bijective (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν) := by
  classical
  constructor
  · intro u v huv
    have hg := congrArg (fun z : (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g) => z.1) huv
    have hi := congrArg (fun z : (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g) =>
      z.2.val.val) huv
    cases u with
    | inl a =>
      cases v with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact Prod.ext hg (Fin.ext hi)
      | inr b =>
        have hp : a.val=b.val := Prod.ext hg (Fin.ext hi)
        exact (Finset.disjoint_left.mp hDisj a.property (hp.symm ▸ b.property)).elim
    | inr a =>
      cases v with
      | inl b =>
        have hp : a.val=b.val := Prod.ext hg (Fin.ext hi)
        exact (Finset.disjoint_left.mp hDisj b.property (hp ▸ a.property)).elim
      | inr b =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact Prod.ext hg (Fin.ext hi)
  · rintro ⟨g,j⟩
    obtain ⟨r,hr,hrj⟩ := Finset.mem_image.mp j.property
    have hsel := (Finset.mem_filter.mp hr).2
    rcases hsel with hA | hB
    · refine ⟨Sum.inl ⟨(g,r),hA⟩,?_⟩
      dsimp only [sourceOriginalProbeMemoryAuxSlot434]
      apply congrArg (fun z : sourceOriginalProbeFreedSlots434 J m hmJ ν g =>
        (⟨g,z⟩ : Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g))
      apply Subtype.ext
      exact hrj
    · refine ⟨Sum.inr ⟨(g,r),hB⟩,?_⟩
      dsimp only [sourceOriginalProbeMemoryAuxSlot434]
      apply congrArg (fun z : sourceOriginalProbeFreedSlots434 J m hmJ ν g =>
        (⟨g,z⟩ : Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g))
      apply Subtype.ext
      exact hrj

/-- Actual coordinate reindexing; repeated numerical prime values are
allowed and no coordinate is dropped or counted twice. -/
noncomputable def sourceOriginalProbeMemoryAuxEquiv434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2) :
    SourceOriginalProbeAuxIndex434 m ν ≃
      (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g) :=
  Equiv.ofBijective (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν)
    (source_original_probe_memory_aux_slot_bijective434 J m hmJ ν hDisj)

/-- The hypothesis on the coordinate bijection holds for the genuine
original two-block family, by its actual group disjointness. -/
theorem source_original_probe_memory_actual_pattern_disjoint434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
    Disjoint ν.1 ν.2 := by
  have hm := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  exact Finset.disjoint_left.mp hBlocks
    (Finset.mem_product.mp (hm.2.1 hzA)).1
    (Finset.mem_product.mp (hm.2.2.2 hzB)).1

/-- Exact labelled product transfer. Instantiating F by the prime value
gives D_A*D_B; instantiating by 1/(p V_g) gives the true auxiliary mass. -/
theorem source_original_probe_memory_aux_product_transfer434
    {G M : Type} [Fintype G] [DecidableEq G] [CommMonoid M]
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (F : (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g) → M) :
    (∏ g : G, ∏ j : sourceOriginalProbeFreedSlots434 J m hmJ ν g, F ⟨g,j⟩) =
    (∏ a : ν.1, F (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν (Sum.inl a))) *
    (∏ b : ν.2, F (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν (Sum.inr b))) := by
  classical
  let e := sourceOriginalProbeMemoryAuxEquiv434 J m hmJ ν hDisj
  have he := Fintype.prod_equiv e (fun z => F (e z)) F (by intro z;rfl)
  calc
    _ = ∏ z : (Σ g : G, sourceOriginalProbeFreedSlots434 J m hmJ ν g),F z := by
      rw [Fintype.prod_sigma]
    _ = ∏ z : SourceOriginalProbeAuxIndex434 m ν,F (e z) := he.symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeMemoryAssignments -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual dependent auxiliary assignment space, with repeated
numerical prime values permitted, is exactly the two selected tuples. -/
noncomputable def sourceOriginalProbeMemoryAssignmentEquiv434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2) :
    SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) ≃
      ((a : ν.1) → BP a.val.1) × ((b : ν.2) → BP b.val.1) :=
  (Equiv.piCurry (fun g (_ : sourceOriginalProbeFreedSlots434 J m hmJ ν g) =>
    BP g)).symm.trans
  ((Equiv.piCongrLeft
    (fun z : (Σ g : G,sourceOriginalProbeFreedSlots434 J m hmJ ν g) => BP z.1)
    (sourceOriginalProbeMemoryAuxEquiv434 J m hmJ ν hDisj)).symm.trans
    (Equiv.sumPiEquivProdPi (fun z => BP
      (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν z).1)))

/-- No summation multiplicity or cardinality factor enters this actual
assignment reindexing. -/
theorem source_original_probe_memory_assignment_sum434
    {G R : Type} [Fintype G] [DecidableEq G] [AddCommMonoid R]
    (BP : G → Type) [∀ g,Fintype (BP g)]
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (F : (((a : ν.1) → BP a.val.1) × ((b : ν.2) → BP b.val.1)) → R) :
    (∑ aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      F (sourceOriginalProbeMemoryAssignmentEquiv434 BP J m hmJ ν hDisj aux)) =
      ∑ ab, F ab := by
  classical
  exact Fintype.sum_equiv
    (sourceOriginalProbeMemoryAssignmentEquiv434 BP J m hmJ ν hDisj)
    _ F (fun _ => rfl)

/-- Exact ORIGINAL harmonic mass under the dependent assignment equivalence. -/
theorem source_original_probe_memory_assignment_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bigMod : (g : G) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (V : G → ℝ)
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    sourceAuxMass BP bigMod J m V (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux =
      (∏ a : ν.1,sourcePrimeSharedAtom434 (V a.val.1)
        (bigMod a.val.1 ((sourceOriginalProbeMemoryAssignmentEquiv434
          BP J m hmJ ν hDisj aux).1 a))) *
      (∏ b : ν.2,sourcePrimeSharedAtom434 (V b.val.1)
        (bigMod b.val.1 ((sourceOriginalProbeMemoryAssignmentEquiv434
          BP J m hmJ ν hDisj aux).2 b))) := by
  rw [source_original_probe_memory_aux_mass434]
  exact source_original_probe_memory_aux_product_transfer434
    J m hmJ ν hDisj (fun z => sourcePrimeSharedAtom434 (V z.1)
      (bigMod z.1 (aux z.1 z.2)))

/-- For the genuine prime carriers the target is literally the two
SourceOriginalGramPrimeTuple434 spaces used by the analytic estimate. -/
noncomputable def sourceOriginalProbeMemoryPrimeAssignmentEquiv434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2) :
    SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) ≃
      SourceOriginalGramPrimeTuple434 (fun a : ν.1 => P a.val.1) ×
      SourceOriginalGramPrimeTuple434 (fun b : ν.2 => P b.val.1) :=
  sourceOriginalProbeMemoryAssignmentEquiv434 _ J m hmJ ν hDisj

/-- Exact weighted auxiliary sum, including arbitrary dependence on both
tuples. This does not assume the integrand factors. -/
theorem source_original_probe_memory_weighted_assignment_sum434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (V : G → ℝ)
    (F : (SourceOriginalGramPrimeTuple434 (fun a : ν.1 => P a.val.1) ×
      SourceOriginalGramPrimeTuple434 (fun b : ν.2 => P b.val.1)) → ℂ) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      (sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux : ℂ) *
      F (sourceOriginalProbeMemoryPrimeAssignmentEquiv434 P J m hmJ ν hDisj aux)) =
    ∑ ab,
      ((sourceOriginalGramPrimeMass434 (fun a : ν.1 => P a.val.1)
          (fun a => sourcePrimeSharedAtom434 (V a.val.1)) ab.1 : ℂ) *
       (sourceOriginalGramPrimeMass434 (fun b : ν.2 => P b.val.1)
          (fun b => sourcePrimeSharedAtom434 (V b.val.1)) ab.2 : ℂ)) * F ab := by
  classical
  rw [← source_original_probe_memory_assignment_sum434
    (fun g => {p : ℕ // p ∈ P g}) J m hmJ ν hDisj]
  apply Finset.sum_congr rfl
  intro aux haux
  rw [source_original_probe_memory_assignment_mass434
    _ (fun _ p => p.val) J m hmJ ν hDisj V aux]
  simp only [sourceOriginalGramPrimeMass434, Complex.ofReal_mul,
    Complex.ofReal_prod, sourceOriginalProbeMemoryPrimeAssignmentEquiv434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26SharedFreeEquiv -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Every literal active endpoint is its true shared assignment together
with the actual comparison free-mark array. No distinctness is imposed. -/
noncomputable def sourceOriginalB26ActiveSplitEquiv434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m) :
    ((g : G) → Fin (J+ell) → BP g) ≃
      ((g : G) → sourceBigShared J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g) ×
      ((g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g) where
  toFun s := (fun g i => s g i.val,
    fun g j => s g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g j).val)
  invFun su g i := if hi : i ∈ sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g then su.1 g ⟨i,hi⟩
    else su.2 g ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm ⟨i,hi⟩)
  left_inv s := by
    funext g i
    dsimp only
    split_ifs with hi
    · rfl
    · have he := (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).apply_symm_apply ⟨i,hi⟩
      exact congrArg (s g) (congrArg Subtype.val he)
  right_inv su := by
    apply Prod.ext
    · funext g i
      dsimp only
      rw [dif_pos i.property]
    · funext g j
      dsimp only
      rw [dif_neg (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g j).property]
      exact congrArg (su.2 g)
        ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm_apply_apply j)

noncomputable def sourceOriginalB26SharedPrimeMass434
    {G : Type} [Fintype G] [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ)
    (s : (g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g) : ℝ :=
  ∏ g : G,∏ i,mu g (s g i)

/-- Exact product-law splitting under the literal endpoint equivalence. -/
theorem source_original_B26_active_split_mass434
    {G : Type} [Fintype G] [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (s : (g : G) → Fin (J+ell) → BP g) :
    (∏ g : G,∏ i : Fin (J+ell),mu g (s g i)) =
    sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu
      (sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν s).1 *
    (∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
      mu g ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν s).2 g j)) := by
  classical
  unfold sourceOriginalB26SharedPrimeMass434
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  have he := Fintype.prod_equiv
    (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g)
    (fun j => mu g (s g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g j).val))
    (fun i => mu g (s g i.val)) (fun _ => rfl)
  change (∏ i : Fin (J+ell),mu g (s g i)) =
    (∏ i : sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g,
      mu g (s g i.val)) *
    (∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
      mu g (s g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g j).val))
  rw [he]
  convert! (Fintype.prod_subtype_mul_prod_subtype
    (fun i => i ∈ sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g)
    (fun i => mu g (s g i))).symm using 1
  congr 1 <;> apply Finset.prod_congr (by ext i; simp) (by intro i hi; rfl)

/-- Exact disintegration of an arbitrary full-label test and its actual
harmonic/product mass, without conditional normalization or history count. -/
theorem source_original_B26_active_split_weighted_sum434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ)
    (F : ((g : G) → Fin (J+ell) → BP g) → ℝ) :
    (∑ s : ((g : G) → Fin (J+ell) → BP g),
      (∏ g : G,∏ i : Fin (J+ell),mu g (s g i))*F s) =
    ∑ h : ((g : G) → sourceBigShared J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g),
      ∑ u : ((g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g),
        sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu h *
        (∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),mu g (u g j)) *
        F ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν).symm (h,u)) := by
  classical
  let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
  have he := Fintype.sum_equiv e
    (fun s => (∏ g : G,∏ i : Fin (J+ell),mu g (s g i))*F s)
    (fun hu => sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu hu.1 *
      (∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),mu g (hu.2 g j)) *
      F (e.symm hu)) (by
        intro s
        rw [source_original_B26_active_split_mass434 BP J ell m hmJ ν mu s]
        simp only [e,Equiv.symm_apply_apply])
  exact he.trans (Fintype.sum_prod_type _)

/-- True shared assignment law is normalized independently of J and ell. -/
theorem source_original_B26_shared_prime_mass_total434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (hMass : ∀ g,∑ p : BP g,mu g p=1) :
    (∑ h : ((g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g),
      sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu h) = 1 := by
  classical
  unfold sourceOriginalB26SharedPrimeMass434
  have hprod := (Fintype.prod_sum (fun (g : G)
    (h : sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g) =>
      ∏ i,mu g (h i))).symm
  rw [hprod]
  have hg (g : G) :
      (∑ a : sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g,
        ∏ i,mu g (a i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hMass,Finset.prod_const_one]
  simp only [hg,Finset.prod_const_one]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26SharedFreshLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact target shared-copy law after the true active-state splitting.
The surviving law is the original free prime product, with no extra
normalization and with repeated numerical primes still allowed. -/
theorem source_original_B26_fresh_law_on_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ)
    (h h' : (g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g)
    (u v : (g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g) :
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
      ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν).symm (h,u))
      ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν).symm (h',v))
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) =
    if h'=h then
      ((∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
        mu g (v g j) : ℝ):ℂ) else 0 := by
  classical
  let E := fun g => sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g
  let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
  by_cases hh : h'=h
  · subst h'
    rw [if_pos rfl]
    unfold sourceOriginalB26FrozenFreshLaw434
    push_cast
    apply Finset.prod_congr rfl
    intro g hg
    have hpoint (i : Fin (J+ell)) :
        (if i ∈ E g then
          (if e.symm (h,v) g i = e.symm (h,u) g i then (1:ℂ) else 0)
         else (mu g (e.symm (h,v) g i):ℂ)) =
        if hi : i ∈ E g then 1 else
          (mu g (v g ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm ⟨i,hi⟩)):ℂ) := by
      by_cases hi : i ∈ E g
      · simp [e,sourceOriginalB26ActiveSplitEquiv434,E,hi]
      · simp [e,sourceOriginalB26ActiveSplitEquiv434,E,hi]
    change (∏ i : Fin (J+ell),
      if i ∈ E g then
        (if e.symm (h,v) g i=e.symm (h,u) g i then (1:ℂ) else 0)
      else (mu g (e.symm (h,v) g i):ℂ)) = ∏ j, (mu g (v g j):ℂ)
    simp_rw [hpoint]
    have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin (J+ell) => i ∈ E g)
      (fun i => if hi : i ∈ E g then (1:ℂ) else
        (mu g (v g ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm ⟨i,hi⟩)):ℂ))
    have hs : (∏ i : {i : Fin (J+ell) // i ∉ E g},
        (mu g (v g ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm i)):ℂ)) =
      ∏ i : Fin (J+ell),if hi : i ∈ E g then (1:ℂ) else
        (mu g (v g ((sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm ⟨i,hi⟩)):ℂ) := by
      simp only [Subtype.property,dite_true,Finset.prod_const_one,one_mul] at hsplit
      convert! hsplit using 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [dite_eq_right i.property]
    rw [← hs]
    exact Fintype.prod_equiv
      (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g).symm
      _ _ (fun _ => rfl)
  · rw [if_neg hh]
    have hdiff : ∃ g,∃ i : E g,h' g i ≠ h g i := by
      by_contra hn
      apply hh
      funext g i
      by_contra hi
      exact hn ⟨g,i,hi⟩
    obtain ⟨g,i,hi⟩ := hdiff
    unfold sourceOriginalB26FrozenFreshLaw434
    apply Finset.prod_eq_zero (Finset.mem_univ g)
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    have him : i.val ∈ E g := i.property
    simp [sourceOriginalB26ActiveSplitEquiv434,E] at him hi ⊢
    exact hi

/-- Both independently sampled endpoint permutations are retained by
the literal fresh law; passing to permuted arrays is an exact reindex. -/
theorem source_original_B26_fresh_law_permuted434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (mu : (g : G) → BP g → ℝ)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau =
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat
      (fun g i => s g (sigma g i)) (fun g i => t g (tau g i))
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) := by
  unfold sourceOriginalB26FrozenFreshLaw434
  apply Finset.prod_congr rfl
  intro g hg
  have he := Fintype.prod_equiv (tau g)
    (fun i => if (tau g).symm (tau g i) ∈ sourceBigShared J ell m pat g then
      (if t g (tau g i) = s g (sigma g ((tau g).symm (tau g i))) then (1:ℂ) else 0)
      else (mu g (t g (tau g i)):ℂ))
    (fun i => if (tau g).symm i ∈ sourceBigShared J ell m pat g then
      (if t g i = s g (sigma g ((tau g).symm i)) then (1:ℂ) else 0)
      else (mu g (t g i):ℂ)) (fun _ => rfl)
  simp only [Equiv.symm_apply_apply,Equiv.refl_symm,Equiv.refl_apply] at he ⊢
  convert! he.symm using 1 <;> congr!
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26SharedPairDisintegration -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The literal CLEAN two-endpoint prime pairing disintegrates over the
SAME shared assignment and two independent free assignments. The complex
test is arbitrary and may couple every source and target label. -/
theorem source_original_B26_shared_free_pairing434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ)
    (K : ((g : G) → Fin (J+ell) → BP g) →
      ((g : G) → Fin (J+ell) → BP g) → ℂ) :
    (∑ s : ((g : G) → Fin (J+ell) → BP g),
      ∑ t : ((g : G) → Fin (J+ell) → BP g),
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i) : ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) * K s t) =
    ∑ h : ((g : G) → sourceBigShared J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g),
      ∑ u : ((g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g),
        ∑ v : ((g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g),
          ((sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu h *
            (∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),mu g (u g j)) *
            (∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),mu g (v g j)) : ℝ):ℂ) *
          K ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν).symm (h,u))
            ((sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν).symm (h,v)) := by
  classical
  let H := ((g : G) → sourceBigShared J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g)
  let X := ((g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → BP g)
  let A := ((g : G) → Fin (J+ell) → BP g)
  let e : A ≃ H × X := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
  let wH : H → ℝ := sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu
  let wX : X → ℝ := fun u => ∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),mu g (u g j)
  let wA : A → ℝ := fun s => ∏ g : G,∏ i : Fin (J+ell),mu g (s g i)
  let fresh : A → A → ℂ := fun s t =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
  have hmass (hu : H × X) : wA (e.symm hu) = wH hu.1*wX hu.2 := by
    have hh := source_original_B26_active_split_mass434 BP J ell m hmJ ν mu (e.symm hu)
    change wA (e.symm hu) = wH (e (e.symm hu)).1*wX (e (e.symm hu)).2 at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hfresh (hu hv : H × X) :
      fresh (e.symm hu) (e.symm hv) = if hv.1=hu.1 then (wX hv.2:ℂ) else 0 :=
    source_original_B26_fresh_law_on_split434 BP J ell m hmJ ν mu hu.1 hv.1 hu.2 hv.2
  have htarget (s : A) :
      (∑ t : A,(wA s:ℂ)*fresh s t*K s t) =
      ∑ hv : H × X,(wA s:ℂ)*fresh s (e.symm hv)*K s (e.symm hv) := by
    apply Fintype.sum_equiv e
    intro t
    simp only [Equiv.symm_apply_apply]
  have hsource :
      (∑ s : A,∑ hv : H × X,(wA s:ℂ)*fresh s (e.symm hv)*K s (e.symm hv)) =
      ∑ hu : H × X,∑ hv : H × X,
        (wA (e.symm hu):ℂ)*fresh (e.symm hu) (e.symm hv)*
          K (e.symm hu) (e.symm hv) := by
    apply Fintype.sum_equiv e
    intro s
    simp only [Equiv.symm_apply_apply]
  have hinner (hu : H × X) :
      (∑ hv : H × X,(wA (e.symm hu):ℂ)*fresh (e.symm hu) (e.symm hv)*
        K (e.symm hu) (e.symm hv)) =
      ∑ v : X,((wH hu.1*wX hu.2*wX v:ℝ):ℂ)*
        K (e.symm hu) (e.symm (hu.1,v)) := by
    simp_rw [hmass,hfresh]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Complex.ofReal_mul]
    rw [Finset.sum_eq_single hu.1]
    · rw [if_pos rfl]
    · intro x hx hne
      rw [if_neg hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  change (∑ s : A,∑ t : A,(wA s:ℂ)*fresh s t*K s t) = _
  simp_rw [htarget]
  rw [hsource]
  simp_rw [hinner]
  exact Fintype.sum_prod_type _

/-- Original harmonic/product mass is invariant under each independent
endpoint permutation; there is no factorial or permutation-count loss. -/
theorem source_original_B26_endpoint_permutation_mass434
    {G : Type} [Fintype G] [DecidableEq G] (BP : G → Type)
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (s : (g : G) → Fin M → BP g)
    (sigma : BigGroupPerm (BG := G) M) :
    (∏ g : G,∏ i : Fin M,mu g (s g (sigma g i))) =
      ∏ g : G,∏ i : Fin M,mu g (s g i) := by
  apply Finset.prod_congr rfl
  intro g hg
  exact Fintype.prod_equiv (sigma g) _ _ (fun _ => rfl)
end Green64Analytic.CorrelationSquare

end

