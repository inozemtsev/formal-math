module

public import Green64.Library.Analysis.Estimates.AllPrimeRow

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeArray

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeArray -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
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

/-- All original SMALL and BIG source visit damping, with correct
sqrt(q) at the two endpoints and q internally. -/
def b643AllPrimeVisitDamping434 {N : ℕ} (q : ℝ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) : ℂ :=
  (∏ t : Fin (N+1), ∏ g : SG, ((sourceVisitQ q N t.val ^
    (Green64SmallHaar.omega (smallMod g)
      (Green64SmallHaar.residues (smallMod g) (J+ell) ((states t).1 g))-(J+ell)) : ℝ) : ℂ)) *
  (∏ t : Fin (N+1), ∏ g : BG, ((sourceVisitQ q N t.val ^
    (Green64SmallHaar.omega (bigMod g)
      (Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g))-(J+ell)) : ℝ) : ℂ))

private theorem b643_all_rows {n : ℕ}
    (q : ℝ) (hq : 0≤q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    (∏ i : Fin (n+1), memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta (physicalAlternatingSign i.val) k
      (states i.castSucc) (states i.succ) (frames i).1.1 (frames i).1.2
      (frames i).2.1 (frames i).2.2.1 (frames i).2.2.2.1 (frames i).2.2.2.2) =
    if ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i then
      (∏ i : Fin (n+1), b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
        Vsmall Vbig Knu zeta theta k
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) i) *
      b643AllPrimeVisitDamping434 SP smallMod BP bigMod J ell q states
    else 0 := by
  by_cases ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i
  · rw [ite_eq_left ht]
    let ES (i : Fin (n+1)) : ℂ := ∏ g : SG,
      ((Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((states i.castSucc).1 g) *
        Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((states i.succ).1 g) : ℝ) : ℂ)
    let EB (i : Fin (n+1)) : ℂ := ∏ g : BG,
      ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.castSucc).2 g) *
        Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.succ).2 g) : ℝ) : ℂ)
    have hs := memory_ind_BIG_Fin_pair_sourceQ_complex SP smallMod q hq n (J+ell) (fun t => (states t).1)
    have hb := memory_ind_BIG_Fin_pair_sourceQ_complex BP bigMod q hq n (J+ell) (fun t => (states t).2)
    calc
      _ = ∏ i : Fin (n+1), b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
          Vsmall Vbig Knu zeta theta k
          (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) i * (ES i*EB i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (b643_all_prime_row_weight434 SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k states frames i).trans (ite_eq_left (ht i))
      _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
        congr 1
        exact congrArg₂ (fun a b : ℂ => a*b) hs hb
  · rw [ite_eq_right ht]
    obtain ⟨i,hi⟩ := not_forall.mp ht
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [b643_all_prime_row_weight434,ite_eq_right hi]

/-- Exact full original array weight, including zeros, BOTH initial
Haar factors and BOTH initial mark masses. The new coefficient contains
no SMALL or BIG residues; all residue dependence is in transport/damping. -/
theorem b643_all_prime_array_weight434
    (q : ℝ) (hq : 0≤q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (n : ℕ)
    (states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k states frames =
    ((∏ g : SG, (Green64SmallHaar.haarAtomMass (smallMod g) : ℂ)) *
      (∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ))) *
    (if ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i then
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) *
      b643AllPrimeVisitDamping434 SP smallMod BP bigMod J ell q states
    else 0) := by
  unfold memoryIndOriginalArrayWeight
  rw [b643_all_rows SP smallMod BP bigMod J ell m patterns q hq Vsmall Vbig Knu zeta theta k states frames]
  by_cases ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i
  · rw [ite_eq_left ht,ite_eq_left ht]
    have hs := memory_ind_BIG_true_group_mass_split SP smallMod (J+ell) Vsmall
    have hb := memory_ind_BIG_true_group_mass_split BP bigMod (J+ell) Vbig
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow] at hs hb
    rw [hs,hb]
    unfold b643AllPrimeWeight434
    ac_rfl
  · rw [ite_eq_right ht,ite_eq_right ht,mul_zero,mul_zero]
end Green64FullPhysicalE

end

end

