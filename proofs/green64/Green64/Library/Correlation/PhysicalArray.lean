module

public import Green64.Library.Weights.IntegerNativeRow
public import Green64.Library.Analysis.Estimates.AllPrimeDamping

@[expose] public section

/-!
# Correlation / PhysicalArray

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalArray -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The pair of complete anchors obtained from the ONE physical integer. -/
def b653IntegerAnchor434 (n : ℤ) : B643AllPrimeAnchor434 SP smallMod BP bigMod :=
  ((fun g p => (n : ZMod (smallMod g p))), (fun g p => (n : ZMod (bigMod g p))))

/-- Exact signed physical steps. Mark equality is imposed only where
already required by the original row; no endpoint mark return is added. -/
def b653IntegerArraySteps434 (positions : Finset ℤ) {N : ℕ} (k : ℤ)
    (states : Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : Prop :=
  ∀ i : Fin N, (states i.succ).val.1.val = (states i.castSucc).val.1.val +
    physicalAlternatingSign i.val*k*
      (b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns (states i.castSucc).val.2 (frames i) : ℤ)

/-- Literal product of the source physical frames with exactly one
initial physical mark mass. There is no initial Haar mass. -/
def b653IntegerArrayWeight434 (positions : Finset ℤ) {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ)
    (states : Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℂ :=
  (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ) *
  ∏ i : Fin N, b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
    q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
    (states i.castSucc) (states i.succ) (frames i)

theorem b653_integer_array_transport434 (positions : Finset ℤ) {N : ℕ} (k : ℤ)
    (states : Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (hs : b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k states frames) :
    ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns
      (fun t => (states t).val.2) frames k i := by
  intro i
  exact b650_integer_residue_transport434 SP smallMod BP bigMod J ell positions
    (states i.castSucc) (states i.succ) _ (hs i)

/-- Exact physical array factorization for every positive length. All
frames, zero rows, ordered marks and auxiliary repetitions are retained.
The two endpoint sqrt(q) factors combine to the source visit powers. -/
theorem b653_integer_array_weight434 (positions : Finset ℤ) (n : ℕ)
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ)
    (states : Fin (n+2) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b653IntegerArrayWeight434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta k states frames =
    if b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k states frames then
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun t => (states t).val.2) frames) *
      (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun t => (states t).val.2) frames) k
        (b653IntegerAnchor434 SP smallMod BP bigMod (states 0).val.1.val) : ℂ)
    else 0 := by
  let native := fun t => (states t).val.2
  let ω := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns native frames
  by_cases hs : b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k states frames
  · rw [ite_eq_left hs]
    have ht := b653_integer_array_transport434 SP smallMod BP bigMod J ell m patterns positions k states frames hs
    let ES (i : Fin (n+1)) : ℂ := ∏ g : SG,
      ((Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((native i.castSucc).1 g) *
        Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((native i.succ).1 g) : ℝ) : ℂ)
    let EB (i : Fin (n+1)) : ℂ := ∏ g : BG,
      ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((native i.castSucc).2 g) *
        Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((native i.succ).2 g) : ℝ) : ℂ)
    have hpairS := memory_ind_BIG_Fin_pair_sourceQ_complex SP smallMod q hq n (J+ell) (fun t => (native t).1)
    have hpairB := memory_ind_BIG_Fin_pair_sourceQ_complex BP bigMod q hq n (J+ell) (fun t => (native t).2)
    have hp : (∏ i : Fin (n+1), b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
        (states i.castSucc) (states i.succ) (frames i)) =
      (∏ i : Fin (n+1), b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
        Vsmall Vbig Knu zeta 0 k ω i) *
      b643AllPrimeVisitDamping434 SP smallMod BP bigMod J ell q native := by
      calc
        _ = ∏ i : Fin (n+1), b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
            Vsmall Vbig Knu zeta 0 k ω i * (ES i*EB i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [b650_integer_frame_native434,ite_eq_left (hs i)]
          exact (b643_all_prime_row_weight434 SP smallMod BP bigMod J ell m patterns
            q Vsmall Vbig Knu zeta 0 k native frames i).trans (ite_eq_left (ht i))
        _ = _ := by
          rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
          congr 1
          exact congrArg₂ (fun a b : ℂ => a*b) hpairS hpairB
    have hd := b643_all_prime_transport_damping434 SP smallMod BP bigMod J ell m patterns
      q k native frames ht
    have ha : ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((native 0).1 g)),
        (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((native 0).2 g))) =
        b653IntegerAnchor434 SP smallMod BP bigMod (states 0).val.1.val := by
      apply Prod.ext
      · funext g p
        exact (states 0).property.1 g p
      · funext g p
        exact (states 0).property.2 g p
    rw [ha] at hd
    unfold b653IntegerArrayWeight434
    rw [hp,hd]
    unfold b650IntegerStateMass434 b643AllPrimeWeight434
    push_cast
    exact (mul_assoc _ _ _).symm
  · rw [ite_eq_right hs]
    unfold b653IntegerArrayWeight434
    suffices hz : (∏ i : Fin (n+1), b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
        (states i.castSucc) (states i.succ) (frames i))=0 by rw [hz,mul_zero]
    obtain ⟨i,hi⟩ := not_forall.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [b650_integer_frame_native434,ite_eq_right hi]
end Green64FullPhysicalE

end

end

