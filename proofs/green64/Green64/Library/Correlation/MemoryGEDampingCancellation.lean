module

public import Green64.Library.Correlation.Part027
public import Green64.Library.Weights.GhostOldDampingCancellation
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Correlation / MemoryGEDampingCancellation

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryGEDampingCancellation -/

section

open Classical
open scoped BigOperators
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Passing from ordered source Fock representatives to the genuine
symmetric output does not change the OLD damping. No orbit-size or
factorial loss, even with repeated numerical prime/residue atoms. -/
theorem source_original_memory_OLD_projection434
    (rho : ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x := by
  unfold sourceOriginalMemoryOldOutput434 sourceOriginalMemoryOldInput434
  apply Finset.prod_congr rfl
  intro g hg
  congr 1
  change (Green64Fock.fockMultiset ((x.2 g).2)).countP
    (fun a => a.2 = 0) = Green64PhysicalEdge.oldZeroCount ((x.2 g).2)
  rw [Green64Fock.fockMultiset, Multiset.coe_countP]
  exact Green64MemoryGhostOp.source_original_GHOST_Fock_list_count434 ((x.2 g).2)

/-- ALL original BIG groups in the actual physical G_i. The real
coefficients q_i, eta_i, V_g, zero-supported mu and both endpoint
OLD factors are preserved. This is the exact cancellation in the
source Memory equations, not an independently chosen signed kernel. -/
theorem source_original_memory_G_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0) (N i : ℕ)
    (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      physicalVisitGKernel SP smallMod BP bigMod (J+ell) cap
        q rho N i Vb mu x y *
      sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho y =
    physicalVisitGKernel SP smallMod BP bigMod (J+ell) cap
      q 1 N i Vb mu x y := by
  classical
  unfold physicalVisitGKernel
  by_cases h : x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1
  · simp only [if_pos h, Complex.ofReal_one, one_pow, div_one]
    unfold sourceOriginalMemoryOldInput434
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g hg
    exact Green64MemoryGhostOp.source_original_GHOST_actual_Fock_rho_cancellation434
      rho (sourceVisitQ q N i) (sourceVisitEta q N i) (Vb g) hrho
      (mu g) ((x.2 g).2) ((y.2 g).2)
  · simp only [if_neg h, mul_zero, zero_mul]

/-- Exact ORIGINAL coherent E-G-E block. The middle two OLD factors
cancel against the true source ghost/birth denominators BEFORE any
absolute-value or Gram estimate. Both E kernels retain their entire
signed Nu sums, actual auxiliaries, moving D, complex K, independent
permutations and store/promote branches. Arbitrary left/right phases
cover the genuine alternating source steps. The remaining rho factors
belong only to the outside physical endpoints.
This identity does not assert a small norm of the rho=1 block and
therefore does not close signed local transference. -/
theorem source_original_memory_EGE_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0) (N i : ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (KL KR : SourcePatternK BP J ell m patterns)
    (zetaL thetaL zetaR thetaR : ℝ) (oL oR k : ℤ)
    (x u v : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu KL zetaL thetaL oL k x
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap u) *
     physicalVisitGKernel SP smallMod BP bigMod (J+ell) cap
       q rho N i Vb mu u v) *
     orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
       q rho Vs Vb mu KR zetaR thetaR oR k v y =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      ((orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu KL zetaL thetaL oL k x
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap u) *
       physicalVisitGKernel SP smallMod BP bigMod (J+ell) cap
         q 1 N i Vb mu u v) *
       orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
         q 1 Vs Vb mu KR zetaR thetaR oR k v y) *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y := by
  rw [source_original_memory_OLD_kernel_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu KL
    zetaL thetaL oL k x
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap u)]
  rw [source_original_memory_OLD_kernel_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu KR
    zetaR thetaR oR k v y]
  rw [source_original_memory_OLD_projection434 SP smallMod BP bigMod J ell cap rho u]
  calc
    _ = sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      ((orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu KL zetaL thetaL oL k x
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap u) *
       (sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho u *
        physicalVisitGKernel SP smallMod BP bigMod (J+ell) cap
          q rho N i Vb mu u v *
        sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho v)) *
       orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
         q 1 Vs Vb mu KR zetaR thetaR oR k v y) *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y := by ring
    _ = _ := by
      rw [source_original_memory_G_rho_cancellation434
        SP smallMod BP bigMod J ell cap q rho hrho N i Vb mu u v]


/-- The NORMALIZED Gram of the ORIGINAL physical E kernel, with its
real source Haar/active/Fock mass and real symmetric target orbit mass.
OLD changes the source weight by |Rrho(x)|^2 and puts two factors at
the target endpoints. The full coherent signed Nu sum stays inside
both Gram factors. This is the source-faithful replacement for treating
OLD_h as an unrelated historical scalar. No Schur saving is asserted. -/
theorem source_original_memory_OLD_normalized_Gram434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) :
    let normKernel := fun (r : ℝ)
      (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) =>
      orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
        q r Vs Vb mu K zeta theta o k x y /
      ((Real.sqrt (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vs mu y) : ℝ) : ℂ)
    ∀ y z : FullPhysicalOutput SP smallMod BP bigMod (J+ell),
      (∑ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x : ℂ) *
        star (normKernel rho x y) * normKernel rho x z) =
      (star (sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y) *
        sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho z) *
      (∑ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x : ℂ) *
        star (sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x) *
        sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
        star (normKernel 1 x y) * normKernel 1 x z) := by
  classical
  dsimp only
  intro y z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [source_original_memory_OLD_kernel_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu K zeta theta o k x y,
    source_original_memory_OLD_kernel_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu K zeta theta o k x z]
  simp only [star_mul, star_div₀]
  ring


/-- Actual single G birth witness, before any endpoint aggregation.
Thus an arbitrary chronological eligibility test can be retained. -/
private theorem actual_ghost_witness_rho434
    {P : Type} [Fintype P] [DecidableEq P]
    {modulus : P → ℕ} [∀ p, NeZero (modulus p)] {B : ℕ}
    (rho q eta V : ℝ) (hrho : rho ≠ 0) (mu : P → ℝ)
    (s t : Green64Fock.FockState (Green64Fock.Atom P modulus) B)
    (c : GhostWitnessChoice (Green64Fock.fockToList s)
      (fun a : Green64Fock.Atom P modulus => a.2 = 0) B) :
    (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount s *
      ghostWitnessTerm (Green64Fock.fockToList s) (Green64Fock.fockToList t)
        (fun a : Green64Fock.Atom P modulus => a.2 = 0) B
        (-(eta : ℂ)/(rho : ℂ)) ((q : ℂ)/(rho : ℂ)^2)
        (-(eta : ℂ)*(V : ℂ)/(rho : ℂ))
        (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ))) c *
      (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount t =
    ghostWitnessTerm (Green64Fock.fockToList s) (Green64Fock.fockToList t)
      (fun a : Green64Fock.Atom P modulus => a.2 = 0) B
      (-(eta : ℂ)) (q : ℂ) (-(eta : ℂ)*(V : ℂ))
      (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ))) c := by
  have hr : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho
  rw [← Green64MemoryGhostOp.source_original_GHOST_Fock_zero_count434 s,
    ← Green64MemoryGhostOp.source_original_GHOST_Fock_zero_count434 t]
  unfold ghostWitnessTerm
  by_cases hout : Green64MemoryGhostOp.afterGhost
      (Green64Fock.fockToList s) c.1.1 c.2.2 = Green64Fock.fockToList t
  · simp only [if_pos hout]
    by_cases hz : ∀ j, (c.2.2 j).2 = 0
    · rw [← hout]
      exact Green64MemoryGhostOp.source_original_GHOST_rho_term_cancellation434
        (Green64Fock.fockToList s)
        (fun a : Green64Fock.Atom P modulus => a.2 = 0)
        c.1.1 (Finset.mem_powerset.mp c.1.property) c.2.2 hz
        (rho : ℂ) (-(eta : ℂ)) (q : ℂ) (-(eta : ℂ)*(V : ℂ)) hr
        (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ)))
    · obtain ⟨j, hj⟩ := not_forall.mp hz
      have hprod :
          (∏ l : Fin c.2.1.val,
            Green64Fock.sourceBirthNu (fun p => (mu p : ℂ)) (c.2.2 l)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j)
          (Green64Fock.birthMass_nonzero_residue _ (c.2.2 j) hj)
      simp only [Green64MemoryGhostOp.sourceGhostTerm, hprod, mul_zero, zero_mul]
  · simp only [if_neg hout, mul_zero, zero_mul]

/-- Original all-group witness coefficient, preserving the complete
fresh atom list, OLD subset, 1/b!, signs and repeated-value multiplicity.
This strengthens the aggregated G identity to the actual birth carrier. -/
theorem source_original_memory_G_WITNESS_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0) (N i : ℕ)
    (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) :
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N i Vb mu x y c *
      sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho y =
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q 1 N i Vb mu x y c := by
  classical
  unfold physicalGBranchTerm
  by_cases h : x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1
  · simp only [if_pos h, Complex.ofReal_one, one_pow, div_one]
    unfold sourceOriginalMemoryOldInput434
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g hg
    exact actual_ghost_witness_rho434
      rho (sourceVisitQ q N i) (sourceVisitEta q N i) (Vb g) hrho
      (mu g) ((x.2 g).2) ((y.2 g).2) (c g)
  · simp only [if_neg h, mul_zero, zero_mul]

/-- ORIGINAL oriented E WITH its genuine chronological distinct-birth
indicator and seen-set update. No auxiliary label or OLD promotion
is reclassified as a birth and no history is discarded here. -/
theorem source_original_memory_BIRTH_MARKED_E_OLD_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x seen F =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k x seen
        (fun y nextSeen => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho y * F y nextSeen) := by
  classical
  unfold physicalOrientedBirthMarkedE
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen z
  · simp only [if_pos h]
    rw [source_original_memory_OLD_source_coefficient_sandwich434
      SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
      K zeta theta o k x z]
    ring
  · simp only [if_neg h, mul_zero]

/-- ORIGINAL G WITH its genuine chronological birth filter. The
two OLD factors cancel on every surviving witness, and the same
actual updated seen-set is passed to the arbitrary complex observable.
This identity cannot be obtained merely by forgetting history after
summing G: it uses the witness identity above. -/
theorem source_original_memory_BIRTH_MARKED_G_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0) (N i : ℕ)
    (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      physicalGBirthMarkedRow SP smallMod BP bigMod (J+ell) cap
        q rho N i Vb mu x seen
        (fun y nextSeen => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho y * F y nextSeen) =
    physicalGBirthMarkedRow SP smallMod BP bigMod (J+ell) cap
      q 1 N i Vb mu x seen F := by
  classical
  unfold physicalGBirthMarkedRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : physicalGhostBatchEligible SP smallMod BP bigMod
      (J+ell) cap x seen c
  · simp only [if_pos h]
    rw [source_original_memory_OLD_projection434
      SP smallMod BP bigMod J ell cap rho y]
    calc
      _ = (sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
          q rho N i Vb mu x y c *
        sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho y) *
        F (physicalFockProjection SP smallMod BP bigMod (J+ell) cap y)
          (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
            (J+ell) cap x c).toFinset) := by ring
      _ = _ := by
        rw [source_original_memory_G_WITNESS_rho_cancellation434
          SP smallMod BP bigMod J ell cap q rho hrho N i Vb mu x y c]
  · simp only [if_neg h, mul_zero]
end Green64FullPhysicalE

end

