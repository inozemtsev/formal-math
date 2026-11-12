module

public import Green64.Library.Correlation.Part024
public import Green64.Library.Correlation.Part022
public import Green64.Library.Correlation.MemorySourceRootLifespanReadout
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part014
public import Green64.Library.Correlation.Part018

@[expose] public section

/-!
# Correlation / Part025

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryB1bFullEBigRows -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- One TRUE source BIG prime's original E_i coefficient includes
post-G old rho, pre-next-G old rho, promoted V^-1, and fresh
mu-tilde exactly once. No SMALL/aux/K factor is inserted here. -/
def memoryOriginalEPerPrimeRow
    (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
    (life : (g : BG) → BP g → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (i : ℕ)
    (rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP) : ℂ :=
  memoryPrimitiveERhoPerPrimeFactor (bigMod gp.1) (A gp.1)
    (life gp.1) offset i rho gp.2 *
  (if memorySchedulePromote (A gp.1 gp.2) (life gp.1 gp.2) i
     then (1/(Vbig gp.1 : ℂ)) else 1) *
  (if memoryScheduleFresh (A gp.1 gp.2) (life gp.1 gp.2) i
     then (mu gp.1 gp.2 : ℂ) else 1)

/-- Full TRUE original E_i BIG row, preserving the exact two ordered
OLD rho counts, all promotions and all fresh mu integrations, equals
a product over the genuine source numerical prime/lifespan choices.
No new factor of V, no symmetry normalization, no surrogate E kernel. -/
theorem memory_source_frozen_E_BIG_row_prime_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0)
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R)) :
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    (∏ g : BG,
      (rho : ℂ) ^
        ((memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          false i.val).countP (fun z => z.2 = 0) +
         (memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          true (i.val+1)).countP (fun z => z.2 = 0)) *
      ((1/(Vbig g : ℂ)) ^
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)).card *
      (∏ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
          (f.2.2.1 g j)) : ℂ)))) =
    (∏ gp : PhysicalSourcePrime BP,
      memoryOriginalEPerPrimeRow BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val rho Vbig mu gp) := by
  dsimp only
  have hOld := memory_source_frozen_E_rho_group_prime_product SP smallMod
    BP bigMod J ell m patterns ω life k rho i
  have hNew := memory_source_frozen_E_V_mu_prime_product SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hn mu i
  dsimp only at hOld hNew
  rw [Finset.prod_mul_distrib]
  rw [hOld, hNew]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro gp hgp
  unfold memoryOriginalEPerPrimeRow
  ring
end Green64FullPhysicalE

end

end

/-! ## MemorySourceRootActualPrimeProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Prime-side coefficient identity on EVERY original contributing indexed
root, with the EXACT lifespan choose used by the original forward profile.
No lifespan-fit, zero-hit, reconstruction or weighted-fibre premise is added. -/
theorem memory_source_root_actual_prime_product_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
      (∏ gp : PhysicalSourcePrime BP,
        physicalActualSourcePrimeScalar SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k (2*R) H gp.1 gp.2 (memoryFiniteLifeErase (life gp.1 gp.2))) =
    (∏ gp : PhysicalSourcePrime BP,
      (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
        (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k (2*R) H gp.1 gp.2) (2*R))) *
    (∏ gp : PhysicalSourcePrime BP,
      (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k (2*R) H t : ZMod (bigMod gp.1 gp.2)))
        (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k (2*R) H gp.1 gp.2) (2*R+1) (life gp.1 gp.2) : ℂ)) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hl := Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  unfold physicalSourceBaselineProduct
  push_cast
  rw [← Fintype.prod_sigma (fun gp : PhysicalSourcePrime BP =>
    (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ))]
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro gp hgp
  apply memory_actual_source_prime_scalar_frozen_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H
  · exact hd.big_injective
  · exact hVac
  · exact hl gp.1
  · exact ne_of_gt hd.rho_pos
  · exact ne_of_gt (hd.Vbig_pos gp.1)
  · exact ne_of_gt (physicalSourceBaseline_positive_above_visits BP bigMod q (2*R)
      gp.1 gp.2 (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.big_above_visits gp.1 gp.2))
end Green64FullPhysicalE

end

end

/-! ## MemorySourceRootFrozenPrimeProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Prime-side coefficient identity on EVERY original contributing indexed
root, with the EXACT lifespan choose used by the original forward profile.
No lifespan-fit, zero-hit, reconstruction or weighted-fibre premise is added. -/
theorem memory_source_root_actual_prime_product_frozen_coordinates
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
      (∏ gp : PhysicalSourcePrime BP,
        physicalActualSourcePrimeScalar SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k (2*R) H gp.1 gp.2 (memoryFiniteLifeErase (life gp.1 gp.2))) =
    (∏ gp : PhysicalSourcePrime BP,
      (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns
          (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig mu k (2*R) H) ⟨gp.1,gp.2⟩) (2*R))) *
    (∏ gp : PhysicalSourcePrime BP,
      (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
          (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig mu k (2*R) H) k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns
          (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig mu k (2*R) H) ⟨gp.1,gp.2⟩) (2*R+1) (life gp.1 gp.2) : ℂ)) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hl := Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have ht := memory_source_root_actual_prime_product_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd w
  refine ht.trans ?_
  simp_rw [memory_actual_frozen_visits_exact]
  congr 1
  apply Finset.prod_congr rfl
  intro gp hgp
  apply congrArg Complex.ofReal
  apply memory_frozen_prime_supported_offset_congr
  · exact memory_actual_finite_schedule_support SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H hd.big_injective hVac gp.1
      (life gp.1) (hl gp.1) gp.2
  · intro t ht
    exact congrArg (fun z : ℤ => (z : ZMod (bigMod gp.1 gp.2)))
      (memory_actual_frozen_offset_exact SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k (2*R) H t (Nat.le_of_lt_succ ht)).symm
end Green64FullPhysicalE

end

end

/-! ## MemorySourceRunNormalization -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact new-run counting on original frozen coordinates: the hypothesis hs
is literal lifespan support, and ha is original edge compatibility. Neither
is a weighted fibre equation. -/
theorem memory_source_frozen_new_active_card
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
          ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (2*R))
    (ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i)
    (g : BG) :
    ((Finset.univ.image (ω.2.1 i.succ g).val) \
      (Finset.univ.image (ω.2.1 i.castSucc g).val)).card =
      Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g) := by
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  let f := ω.2.2 i
  let x := fun j => (ω.2.1 i.castSucc g).val (f.2.1 g j)
  let y := fun j => (ω.2.1 i.succ g).val (f.2.2.1 g j)
  have hy : Function.Injective y := (ω.2.1 i.succ g).property.comp (f.2.2.1 g).injective
  have hc : ∀ j l, x j = y l ↔ j ∈ sourceBigShared J ell m (patterns f.1.1) g ∧ j = l := by
    intro j l
    constructor
    · intro he
      have ht := memory_source_active_continuation_is_shared SP smallMod BP bigMod J ell m
        hd.small_prime hd.big_prime hd.big_injective hd.disjoint
        (patterns f.1.1) f.1.2 ix iy ha.2.2.1 f.2.1 f.2.2.1 f.2.2.2.1
        (physicalAlternatingSign i.val) k ha.1 hd.k_ne hd.big_above_k
        (memory_frozen_source_lift_BIG_edge SP smallMod BP bigMod J ell m patterns
          ω life k hs i ha) g j l he
      exact ⟨ht.1,ht.2.symm⟩
    · rintro ⟨hj,rfl⟩
      exact ha.2.2.2 g j hj
  have ht := memory_new_active_card (J+ell) x y hy
    (sourceBigShared J ell m (patterns f.1.1) g) hc
  have hximg : Finset.univ.image x = Finset.univ.image (ω.2.1 i.castSucc g).val := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨f.2.1 g j,rfl⟩
    · rintro ⟨j,rfl⟩; exact ⟨(f.2.1 g).symm j, by simp [x]⟩
  have hyimg : Finset.univ.image y = Finset.univ.image (ω.2.1 i.succ g).val := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨f.2.2.1 g j,rfl⟩
    · rintro ⟨j,rfl⟩; exact ⟨(f.2.2.1 g).symm j, by simp [y]⟩
  simpa only [hximg,hyimg,f] using ht

/-- Total maximal active runs are the literal initial marks plus all true
unshared target slots. Both sampled endpoint permutations are retained. -/
theorem memory_source_frozen_run_sum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
          ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (ha : ∀ i : Fin (2*R),
      memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i)
    (g : BG) :
    (∑ p : BP g, memoryFrozenPrimeRuns
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩) (2*R)) =
      J+ell + ∑ i : Fin (2*R), Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g) := by
  let B : ℕ → Finset (BP g) := fun t =>
    if ht : t < 2*R+1 then Finset.univ.image (ω.2.1 ⟨t,ht⟩ g).val else ∅
  have hAB : ∀ p t, t ≤ 2*R →
      (t ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔ p ∈ B t) := by
    intro p t ht
    have hlt : t < 2*R+1 := Nat.lt_succ_of_le ht
    simp only [B, hlt, dite_true, Finset.mem_image, Finset.mem_univ, true_and,
      memoryFrozenSourceVisits, Finset.mem_filter]
    constructor
    · rintro ⟨i,⟨j,hj⟩,hi⟩
      have hie : i = ⟨t,hlt⟩ := Fin.ext hi
      exact ⟨j,hie ▸ hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨⟨t,hlt⟩,⟨j,hj⟩,rfl⟩
  have ht := memory_frozen_runs_sum
    (fun p : BP g => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    B (2*R) hAB
  have hzero : (B 0).card = J+ell := by
    simp only [B, Nat.zero_lt_succ, dite_true]
    rw [Finset.card_image_of_injective _ (ω.2.1 ⟨0,by omega⟩ g).property]
    simp
  have hstep : ∀ i ∈ Finset.range (2*R),
      (B (i+1) \ B i).card =
        if hi : i < 2*R then Green64SmallHaar.unsharedSlots (J+ell)
          (sourceBigShared J ell m (patterns (ω.2.2 ⟨i,hi⟩).1.1) g) else 0 := by
    intro i hi
    have hil : i < 2*R := Finset.mem_range.mp hi
    have h1 : i+1 < 2*R+1 := by omega
    have h0 : i < 2*R+1 := by omega
    simp only [B, h1, h0, hil, dite_true]
    exact memory_source_frozen_new_active_card SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig k R hd ω life hs ⟨i,hil⟩ (ha ⟨i,hil⟩) g
  rw [ht,hzero,Finset.sum_fin_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl hstep

/-- Exact explicit V factor already included in the original frozen weight.
No orbit or full-weight identity is assumed. -/
theorem memory_source_frozen_run_V_normalization
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
          ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (ha : ∀ i : Fin (2*R),
      memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i) :
    (∏ gp : PhysicalSourcePrime BP,
      (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (2*R))) =
    (∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)) *
      (∏ i : Fin (2*R), ∏ g : BG, 1/(Vbig g : ℂ)^
        Green64SmallHaar.unsharedSlots (J+ell)
          (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g)) := by
  rw [Fintype.prod_sigma]
  conv_lhs =>
    arg 2; ext g
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
    rw [memory_source_frozen_run_sum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig k R hd ω life hs ha g]
    rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp only [one_div_pow]
end Green64FullPhysicalE

end

end

/-! ## MemoryActualSourceRunNormalization -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Schedule support sees only its original finite lifespan carrier. -/
theorem memory_schedule_support_offset_congr {n : ℕ} (p : ℕ)
    (h1 h2 : ℕ → ZMod p) (A : Finset ℕ) (l : MemoryLifespanChoice n)
    (he : ∀ t < n, h1 t = h2 t)
    (hs : MemoryFrozenScheduleSupport p h1 A l) :
    MemoryFrozenScheduleSupport p h2 A l := by
  cases l with
  | none => exact hs
  | some az =>
    refine ⟨hs.1, ?_, ?_, hs.2.2.2⟩
    · intro t ht
      obtain ⟨ha,hz,hh⟩ := hs.2.1 t ht
      refine ⟨ha,hz,?_⟩
      rw [← he t (lt_of_le_of_lt hz az.2.isLt), ← he az.1.val az.1.isLt]
      exact hh
    · rw [← he az.2.val az.2.isLt, ← he az.1.val az.1.isLt]
      exact hs.2.2.1

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Explicit original V normalization on EVERY contributing original indexed
root. Full ghost sectors and endpoint permutations remain in the frozen path.
Support and all edge conditions are derived; no fibre equation is a premise. -/
theorem memory_source_root_actual_run_V_normalization
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H
    (∏ gp : PhysicalSourcePrime BP,
      (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (2*R))) =
    (∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)) *
      (∏ i : Fin (2*R), ∏ g : BG, 1/(Vbig g : ℂ)^
        Green64SmallHaar.unsharedSlots (J+ell)
          (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g)) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig mu k (2*R) H
  let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hl := Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  apply memory_source_frozen_run_V_normalization SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig k R hd ω (fun gp => life gp.1 gp.2)
  · intro gp
    have hs := memory_actual_finite_schedule_support SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H hd.big_injective hVac
      gp.1 (life gp.1) (hl gp.1) gp.2
    rw [← memory_actual_frozen_visits_exact] at hs
    apply memory_schedule_support_offset_congr _ _ _ _ _ ?_ hs
    intro t ht
    exact congrArg (fun z : ℤ => (z : ZMod (bigMod gp.1 gp.2)))
      (memory_actual_frozen_offset_exact SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k (2*R) H t (Nat.le_of_lt_succ ht)).symm
  · exact memory_actual_frozen_edge_allowed SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenWeightRunFactorization -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The literal residual source coefficient, retaining Nu/auxiliary, all
four endpoint permutations, original SMALL kernel, reversed K and phase.
Only the explicit BIG V^-t mark normalization is separated. -/
def memoryFrozenSourceResidualEdgeWeight {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (i : Fin N) : ℂ :=
  let f := ω.2.2 i
  let D := memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i
  let o := physicalAlternatingSign i.val
  if memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i then
    (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell) (o*k*(D : ℤ))
      (fun _ _ => originalEdgeScalar
        (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
          (fun g j => (ω.2.1 i.castSucc g).val (f.2.1 g j))
          (fun g j => (ω.2.1 i.succ g).val (f.2.2.1 g j)))
        zeta theta D o k)
      f.2.2.2.1 f.2.2.2.2 (ω.1 i.castSucc) (ω.1 i.succ)
  else 0


/-- Factorization of the EXISTING frozen edge coefficient, also on zero
or incompatible coefficients; no division by K or kernel values is used. -/
theorem memory_frozen_source_edge_residual_factorization {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) (i : Fin N) :
    memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω i =
    (∏ g : BG, 1/(Vbig g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g)) *
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω i := by
  unfold memoryFrozenSourceEdgeWeight memoryFrozenSourceResidualEdgeWeight
  split_ifs <;> ring

/-- Exact separation of the original frozen weight's existing V factors.
This is a universal definition identity, with no lifespan or support premise. -/
theorem memory_frozen_source_weight_residual_factorization {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) :
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω =
    (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    ((∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)) *
      (∏ i : Fin N, ∏ g : BG, 1/(Vbig g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g))) *
    (∏ i : Fin N, memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω i) := by
  unfold memoryFrozenSourceWeight
  simp_rw [memory_frozen_source_edge_residual_factorization]
  rw [Finset.prod_mul_distrib]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bEFrameResidualPrime -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

/-- The ORIGINAL E_i full physical scalar = literal source residual
edge (Nu, auxiliary, four endpoint permutations, orientation, K,
SMALL Haar) times exactly one BIG prime schedule rho/V/mu product.
Source frozen coefficient is assumed nonzero only to derive the
actual frame compatibility and prime support. -/
theorem memory_source_E_frame_eq_residual_times_prime_rows
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0)
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R)) :
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) =
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i *
    (∏ gp : PhysicalSourcePrime BP,
      memoryOriginalEPerPrimeRow BP bigMod A L offset i.val rho Vbig mu gp) := by
  dsimp only
  let hp : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m
    patterns ω life k q hp
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns
      ω k i := by
    have he : memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m
        patterns q Vsmall Vbig Knu zeta theta k ω i ≠ 0 := by
      have hW := left_ne_zero_of_mul hn
      have hprod := right_ne_zero_of_mul hW
      exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ _)
    by_contra hnot
    simp only [memoryFrozenSourceEdgeWeight, if_neg hnot] at he
    exact he rfl
  have hbig := memory_source_frozen_E_BIG_row_prime_product SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hn mu i
  dsimp only at hbig
  conv_rhs => rw [← hbig]
  unfold memoryPrimitiveEFrameCoefficient memoryFrozenSourceResidualEdgeWeight
  rw [if_pos ha]
  simp only [memoryFrozenSourceIndependentLift, memoryFrozenSourceD,
    memoryIndependentD, Green64SmallHaar.marks]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bProductReassembly -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Pure FINITE factorization of the exact source shape: original G_i
and E_i per-prime factors, original residual E_i, and terminal G_N.
No cancellation or positivity is assumed; in particular zero source
coefficients are preserved. -/
theorem memory_finite_real_GE_terminal_prime_reassembly
    {I P : Type} [Fintype I] [Fintype P]
    (G E : I → P → ℂ) (T : P → ℂ) (res : I → ℂ) :
    (∏ i : I,
      (∏ p : P, G i p) * (res i * ∏ p : P, E i p)) *
      (∏ p : P, T p) =
    (∏ i : I, res i) *
      (∏ p : P, (∏ i : I, G i p * E i p) * T p) := by
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := G)]
  rw [Finset.prod_comm (f := E)]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFullGEResidualPrime -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 850000
set_option maxRecDepth 2500

/-- The entire TRUE source primitive G_0 E_0 ... G_N scalar
is exactly the original residual E-edge product times a product
of true per-prime G/E visit factors (including the terminal G_N).
Every rho, V, mu-tilde factor remains in its original source
definition, as do K_nu, aux, four permutations and SMALL Haar
inside the unchanged residual E_i factor. No cancellation and no
hypothesis beyond original nonzero frozen profile/source domain. -/
theorem memory_source_original_GE_product_prime_residual_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let EC := fun i : Fin (2*R) =>
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        A L offset i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k hs i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k hs i.succ)
        q rho Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
    let Gp := fun (i : Fin (2*R)) (gp : PhysicalSourcePrime BP) =>
      memoryPrimitiveGPerPrimeFactor BP bigMod A L offset
        i.val q rho (2*R) Vbig mu gp
    let Ep := fun (i : Fin (2*R)) (gp : PhysicalSourcePrime BP) =>
      memoryOriginalEPerPrimeRow BP bigMod A L offset
        i.val rho Vbig mu gp
    let Tp := fun (gp : PhysicalSourcePrime BP) =>
      memoryPrimitiveGPerPrimeFactor BP bigMod A L offset
        (2*R) q rho (2*R) Vbig mu gp
    let Res := fun i : Fin (2*R) =>
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i
    (∏ i : Fin (2*R),
      memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset
        i.val q rho (2*R) Vbig mu * EC i) *
      memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset
        (2*R) q rho (2*R) Vbig mu =
    (∏ i : Fin (2*R), Res i) *
      (∏ gp : PhysicalSourcePrime BP,
        (∏ i : Fin (2*R), Gp i gp * Ep i gp) * Tp gp) := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let EC := fun i : Fin (2*R) =>
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ)
      q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
  let Gp := fun (i : Fin (2*R)) (gp : PhysicalSourcePrime BP) =>
    memoryPrimitiveGPerPrimeFactor BP bigMod A L offset
      i.val q rho (2*R) Vbig mu gp
  let Ep := fun (i : Fin (2*R)) (gp : PhysicalSourcePrime BP) =>
    memoryOriginalEPerPrimeRow BP bigMod A L offset
      i.val rho Vbig mu gp
  let Tp := fun (gp : PhysicalSourcePrime BP) =>
    memoryPrimitiveGPerPrimeFactor BP bigMod A L offset
      (2*R) q rho (2*R) Vbig mu gp
  let Res := fun i : Fin (2*R) =>
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω i
  have hG (i : Fin (2*R)) :
      memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset
        i.val q rho (2*R) Vbig mu =
      ∏ gp : PhysicalSourcePrime BP, Gp i gp :=
    memory_original_G_unordered_eq_true_prime_product
      BP bigMod A L offset i.val q rho (2*R) Vbig mu
  have hN :
      memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset
        (2*R) q rho (2*R) Vbig mu =
      ∏ gp : PhysicalSourcePrime BP, Tp gp :=
    memory_original_G_unordered_eq_true_prime_product
      BP bigMod A L offset (2*R) q rho (2*R) Vbig mu
  have hE (i : Fin (2*R)) :
      EC i = Res i * (∏ gp : PhysicalSourcePrime BP, Ep i gp) :=
    memory_source_E_frame_eq_residual_times_prime_rows
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life hn mu i
  calc
    _ = (∏ i : Fin (2*R),
          (∏ gp : PhysicalSourcePrime BP, Gp i gp) *
          (Res i * (∏ gp : PhysicalSourcePrime BP, Ep i gp))) *
          (∏ gp : PhysicalSourcePrime BP, Tp gp) := by
            rw [hN]
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            rw [hG i]
            change (∏ gp : PhysicalSourcePrime BP, Gp i gp) * EC i =
              (∏ gp : PhysicalSourcePrime BP, Gp i gp) *
                (Res i * (∏ gp : PhysicalSourcePrime BP, Ep i gp))
            rw [hE i]
    _ = _ := memory_finite_real_GE_terminal_prime_reassembly Gp Ep Tp Res
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bActualFibrePrimeResidual -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- Full ORIGINAL nonzero frozen root-profile fibre = original BIG baseline
 times the REAL initial Hilbert mass, all literal residual E edge weights
 and one product of actual prime/lifespan G/E schedule factors including
 terminal G_N. This is not yet the frozen RHS coefficient identity: initial
 Hilbert / run-V / prime baseline factorization remains to be proved. -/
theorem memory_source_original_nonzero_fibre_true_prime_residual_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ) *
    (∏ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i) *
    (∏ gp : PhysicalSourcePrime BP,
      (∏ i : Fin (2*R),
        memoryPrimitiveGPerPrimeFactor BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp *
        memoryOriginalEPerPrimeRow BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          i.val rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp) *
      memoryPrimitiveGPerPrimeFactor BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        (2*R) q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp) := by
  have hRoot := memory_source_nonzero_root_fibre_exact_complete_GN_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hGE := memory_source_original_GE_product_prime_residual_exact
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  let b : ℂ := (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ)
  let h : ℂ := (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ)
  let ge : ℂ :=     (∏ i : Fin (2*R),
      memoryPrimitiveGUnorderedCoefficient BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) *
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.succ)
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i))
  let gn : ℂ :=     memoryPrimitiveGUnorderedCoefficient BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
  let output : ℂ :=     (∏ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i) *
    (∏ gp : PhysicalSourcePrime BP,
      (∏ i : Fin (2*R),
        memoryPrimitiveGPerPrimeFactor BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp *
        memoryOriginalEPerPrimeRow BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          i.val rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp) *
      memoryPrimitiveGPerPrimeFactor BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        (2*R) q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp)
  dsimp only at hRoot hGE
  change _ = b * h * ge * gn at hRoot
  change ge * gn = output at hGE
  calc
    _ = b * h * ge * gn := hRoot
    _ = b * h * (ge * gn) := by ring
    _ = b * h * output := by rw [hGE]
    _ = _ := by dsimp only [b,h,output]; ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bInitialVacuumHilbert -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The actual ORIGINAL frozen profile starts with genuine BIG Fock
vacuum, not an assumed empty unordered memory carrier. Hence its
literal initial Hilbert weight is exactly SMALL Haar times the
BIG ACTIVE-slot product, with NO hidden Fock factorial or second
V normalization. Valid for every original frozen profile and ANY
lifespan choices, including zero-weight profiles. -/
theorem memory_source_frozen_initial_vacuum_Hilbert_mass {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (Vsmall : SG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
        patterns ω life k hcap true ⟨0,Nat.succ_pos N⟩) =
    Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall *
      (∏ g : BG, activeMass (J+ell) (mu g)
        ((ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val)) := by
  unfold fullPhysicalMass bigGroupStateMass
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  have hVac :
      (((memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hcap true ⟨0,Nat.succ_pos N⟩).2 g).2) =
      Green64Fock.vacuumState
        (Green64Fock.Atom (BP g) (bigMod g)) (cap g) :=
    Green64Fock.fockMultiset_empty_implies_vacuum _
      ((memory_frozen_source_physical_vacua SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap).1 g)
  unfold bigStateMass
  rw [hVac, Green64Fock.vacuum_fockMass]
  simp only [mul_one]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bInitialActivePrimes -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Real ORIGINAL frozen initial BIG active-coordinate Hilbert mass is
the product of exactly one mu-tilde per numerical prime whose literal
source active visit set contains 0. This is a bijection using the
injective ORIGINAL active marks; no artificial occupancy surjection. -/
theorem memory_source_original_initial_active_prime_mass {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (mu : (g : BG) → BP g → ℝ) :
    (∏ g : BG, (activeMass (J+ell) (mu g)
      ((ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val) : ℂ)) =
    ∏ gp : PhysicalSourcePrime BP,
      if 0 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp
      then (mu gp.1 gp.2 : ℂ) else 1 := by
  conv_rhs => rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  let target := (ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val
  have hset :
      ((Finset.univ : Finset (BP g)).filter (fun p =>
        0 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)) =
      (Finset.univ : Finset (Fin (J+ell))).image target := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image]
    exact memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω
      ⟨0,Nat.succ_pos N⟩ g p
  have hinj : Function.Injective target := (ω.2.1 ⟨0,Nat.succ_pos N⟩ g).property
  unfold activeMass
  push_cast
  rw [← Finset.prod_filter]
  rw [hset]
  rw [Finset.prod_image (fun a ha b hb he => hinj he)]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bInitialPhysicalPrime -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The unchanged ORIGINAL frozen profile initial physical Hilbert
mass has EXACTLY one SMALL Haar state mass, and a BIG mu-tilde
factor for every genuinely active prime at time zero.
There is no source initial Fock memory / 1/j! / V double charge.
This holds even when the frozen coefficient is zero. -/
theorem memory_source_frozen_initial_physical_mass_prime_exact {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (Vsmall : SG → ℝ)
    (mu : (g : BG) → BP g → ℝ) :
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
        patterns ω life k hcap true ⟨0,Nat.succ_pos N⟩) : ℂ) =
    (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
      (∏ gp : PhysicalSourcePrime BP,
        if 0 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp
        then (mu gp.1 gp.2 : ℂ) else 1) := by
  have hHil := memory_source_frozen_initial_vacuum_Hilbert_mass SP smallMod
    BP bigMod J ell m cap patterns ω life k hcap Vsmall mu
  have hMu := memory_source_original_initial_active_prime_mass SP smallMod
    BP J ell m patterns ω mu
  calc
    _ = (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
        (∏ g : BG, (activeMass (J+ell) (mu g)
          ((ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val) : ℂ)) := by
            rw [hHil]
            push_cast
            rfl
    _ = _ := by rw [hMu]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bOriginalPrimitivePrimeScalar -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- One physical prime's actual complete coefficient, DEFINED from
the proven genuine source G/E index coefficients: initial active mu,
all G/E rows and terminal G_N. It is ONLY an abbreviation for the
true physical scalar, not an axiom asserting equality to the frozen
`memoryFrozenPrimeOperationalScalar`; that equality remains B1b debt. -/
def memoryOriginalPrimitivePrimeScalar
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ)
    (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP) : ℂ :=
  (if 0 ∈ A gp.1 gp.2 then (mu gp.1 gp.2 : ℂ) else 1) *
  (∏ i : Fin N,
    memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
      i.val q rho N Vbig mu gp *
    memoryOriginalEPerPrimeRow BP bigMod A life offset
      i.val rho Vbig mu gp) *
  memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
    N q rho N Vbig mu gp

/-- The unchanged BIG baseline prefactor is literally the product of
one per-prime baseline, not an independently invented baseline. -/
theorem memory_source_original_baseline_sigma
    (q : ℝ) (N : ℕ) :
    (physicalSourceBaselineProduct BP bigMod q N : ℂ) =
    ∏ gp : PhysicalSourcePrime BP,
      (physicalSourceBaseline BP bigMod q N gp.1 gp.2 : ℂ) := by
  unfold physicalSourceBaselineProduct
  push_cast
  exact (Fintype.prod_sigma (fun gp : PhysicalSourcePrime BP =>
    (physicalSourceBaseline BP bigMod q N gp.1 gp.2 : ℂ))).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bActualFibreOperationalPrime -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- Complete ORIGINAL nonzero frozen root fibre = exactly one SMALL Haar
 state mass times literal residual E edges, and per-prime true operational
 physical schedule factors each with its own ORIGINAL baseline. The latter
 remain to be identified with the separately checked frozen prime terms. -/
theorem memory_source_original_nonzero_fibre_operational_prime_factor
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    (∏ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i) *
    (∏ gp : PhysicalSourcePrime BP,
      (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ) *
      memoryOriginalPrimitivePrimeScalar BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (2*R) (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp) := by
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let B : ℂ := (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ)
  let H : ℂ := (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ)
  let Sm : ℂ := (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ)
  let Res : ℂ := (∏ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i)
  let b : PhysicalSourcePrime BP → ℂ := fun gp =>
    (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ)
  let mu0 : PhysicalSourcePrime BP → ℂ := fun gp =>
    if 0 ∈ A gp.1 gp.2 then (mu gp.1 gp.2 : ℂ) else 1
  let Rpr : PhysicalSourcePrime BP → ℂ := fun gp =>
    (∏ i : Fin (2*R),
      memoryPrimitiveGPerPrimeFactor BP bigMod A L offset i.val q rho (2*R) Vbig mu gp *
      memoryOriginalEPerPrimeRow BP bigMod A L offset i.val rho Vbig mu gp) *
    memoryPrimitiveGPerPrimeFactor BP bigMod A L offset (2*R) q rho (2*R) Vbig mu gp
  have hRoot := memory_source_original_nonzero_fibre_true_prime_residual_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hHil := memory_source_frozen_initial_physical_mass_prime_exact SP smallMod
    BP bigMod J ell m cap patterns ω life k hd.cap_saturated Vsmall mu
  have hBase := memory_source_original_baseline_sigma BP bigMod q (2*R)
  change _ = B * H * Res * (∏ gp : PhysicalSourcePrime BP, Rpr gp) at hRoot
  change H = Sm * (∏ gp : PhysicalSourcePrime BP, mu0 gp) at hHil
  change B = (∏ gp : PhysicalSourcePrime BP, b gp) at hBase
  have hprod :
      (∏ gp : PhysicalSourcePrime BP, b gp) *
      (∏ gp : PhysicalSourcePrime BP, mu0 gp) *
      (∏ gp : PhysicalSourcePrime BP, Rpr gp) =
      ∏ gp : PhysicalSourcePrime BP, b gp * (mu0 gp * Rpr gp) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro gp hgp
    ring
  calc
    _ = B * H * Res * (∏ gp : PhysicalSourcePrime BP, Rpr gp) := hRoot
    _ = (∏ gp : PhysicalSourcePrime BP, b gp) *
        (Sm * (∏ gp : PhysicalSourcePrime BP, mu0 gp)) * Res *
        (∏ gp : PhysicalSourcePrime BP, Rpr gp) := by rw [hBase, hHil]
    _ = Sm * Res * ((∏ gp : PhysicalSourcePrime BP, b gp) *
        (∏ gp : PhysicalSourcePrime BP, mu0 gp) *
        (∏ gp : PhysicalSourcePrime BP, Rpr gp)) := by ring
    _ = Sm * Res * (∏ gp : PhysicalSourcePrime BP,
        b gp * (mu0 gp * Rpr gp)) := by rw [hprod]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro gp hgp
      unfold memoryOriginalPrimitivePrimeScalar
      ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cAbsentPrimeExact -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 5000000

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (A : (g : BG) → BP g → Finset ℕ)
variable (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
variable (offset : ℕ → ℤ) (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ)

/-- On a genuine absent source prime (literal original lifespan none,
original active set empty), the TRUE primitive physical one-prime G/E
coefficient is exactly one, matching the previously proved frozen
operational prime scalar. All G/E birth/death/promotion/OLD predicates
are proved false from the genuine empty lifespan; no new normalization. -/
theorem memory_source_original_absent_prime_operational_exact
    (gp : PhysicalSourcePrime BP)
    (hl : life gp.1 gp.2 = none)
    (hA : A gp.1 gp.2 = ∅) :
    memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
      q rho Vbig mu gp =
    memoryFrozenPrimeOperationalScalar BP bigMod q rho N
      Vbig gp.1 gp.2
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2) := by
  have hBirth (i : ℕ) : gp.2 ∉ memoryGhostBirthSet (A gp.1) (life gp.1) i := by
    intro hmem
    have h : memoryScheduleGhostBirth (A gp.1 gp.2) (life gp.1 gp.2) i :=
      (Finset.mem_filter.mp hmem).2
    simp [memoryScheduleGhostBirth, hl] at h
  have hDeath (i : ℕ) : gp.2 ∉ memoryGhostDeathSet (A gp.1) (life gp.1) i := by
    intro hmem
    have h : memoryScheduleTerminate (A gp.1 gp.2) (life gp.1 gp.2) i :=
      (Finset.mem_filter.mp hmem).2
    simp [memoryScheduleTerminate, hl] at h
  have hZero (i : ℕ) : gp.2 ∉ memoryZeroBeforeSet (bigMod gp.1) (A gp.1)
      (life gp.1) offset i := by
    intro hmem
    have h := (Finset.mem_filter.mp hmem).2.1
    simp [memoryScheduleBefore, hl] at h
  have hContinue (i : ℕ) : gp.2 ∉ memoryContinuingZeroSet
      (bigMod gp.1) (A gp.1) (life gp.1) offset i := by
    intro hmem
    exact hZero i ((Finset.mem_sdiff.mp hmem).1)
  have hG (i : ℕ) : memoryPrimitiveGPerPrimeFactor BP bigMod A life offset i
      q rho N Vbig mu gp = 1 := by
    simp [memoryPrimitiveGPerPrimeFactor, hBirth, hDeath, hContinue]
  have hE (i : ℕ) : memoryOriginalEPerPrimeRow BP bigMod A life offset i
      rho Vbig mu gp = 1 := by
    simp [memoryOriginalEPerPrimeRow, memoryPrimitiveERhoPerPrimeFactor,
      memoryScheduleAfter, memoryScheduleBefore, memorySchedulePromote,
      memoryScheduleFresh, hl]
  simp [memoryOriginalPrimitivePrimeScalar, memoryFrozenPrimeOperationalScalar,
    hA, hl, hG, hE]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cScheduleIndicators -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- All true original lifespan memory-residue zero tests, whether
G-before or G-after, use the SAME frozen birth anchor. -/
theorem memory_original_some_life_residue_zero_iff
    (p : ℕ) (h : ℕ → ZMod p) (n : ℕ)
    (az : Fin n × Fin n) (i : ℕ) :
    memoryScheduleResidue p h (some az) i = 0 ↔
    h i = h az.1.val := by
  simp [memoryScheduleResidue,sub_eq_zero]

/-- Original finite-life G-before rho test is literally the
first OLD rho factor in the previously compiled operational row. -/
theorem memory_original_some_life_before_zero_iff
    (p : ℕ) (h : ℕ → ZMod p) (A : Finset ℕ)
    (n : ℕ) (az : Fin n × Fin n) (i : ℕ) :
    (memoryScheduleBefore A (some az) i ∧
      memoryScheduleResidue p h (some az) i = 0) ↔
    ((az.1.val < i ∧ i ≤ az.2.val ∧ i ∉ A) ∧
      h i = h az.1.val) := by
  simp only [memoryScheduleBefore,memory_original_some_life_residue_zero_iff]

/-- Original finite-life G-after rho test is literally the
last OLD rho factor in the previously compiled operational row. -/
theorem memory_original_some_life_after_zero_iff
    (p : ℕ) (h : ℕ → ZMod p) (A : Finset ℕ)
    (n : ℕ) (az : Fin n × Fin n) (i : ℕ) :
    (memoryScheduleAfter A (some az) i ∧
      memoryScheduleResidue p h (some az) i = 0) ↔
    ((az.1.val ≤ i ∧ i < az.2.val ∧ i ∉ A) ∧
      h i = h az.1.val) := by
  simp only [memoryScheduleAfter,memory_original_some_life_residue_zero_iff]

/-- Original ghost death test, including a zero atom at its natural
lifespan endpoint, is the operational row's exact death branch. -/
theorem memory_original_some_life_death_iff
    (A : Finset ℕ) (n : ℕ) (az : Fin n × Fin n) (i : ℕ) :
    memoryScheduleTerminate A (some az) i ↔
      (az.2.val = i ∧ i ∉ A) := by
  rfl

/-- Original ghost birth test is the operational row's exact first
endpoint (inactive) branch. -/
theorem memory_original_some_life_ghost_birth_iff
    (A : Finset ℕ) (n : ℕ) (az : Fin n × Fin n) (i : ℕ) :
    memoryScheduleGhostBirth A (some az) i ↔
      (az.1.val = i ∧ i ∉ A) := by
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cBirthCount -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- For one ORIGINAL represented lifespan the G ghost-birth mu factor
occurs at most once, precisely at its actual birth visit a, if a is
inactive. This counts the genuine source G event, not an abstract
one-prime normalizer. -/
theorem memory_source_one_life_ghost_birth_mu_product
    (N : ℕ) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1)) (mu : ℂ) :
    (∏ t ∈ Finset.range (N+1),
      if memoryScheduleGhostBirth A (some az) t then mu else 1) =
    if az.1.val ∉ A then mu else 1 := by
  have hs := Finset.prod_eq_single (s := Finset.range (N+1))
    (f := fun t : ℕ => if memoryScheduleGhostBirth A (some az) t then mu else 1)
    az.1.val
    (by
      intro t ht hne
      have hh : az.1.val ≠ t := Ne.symm hne
      simp [memoryScheduleGhostBirth,hh])
    (by
      intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr az.1.isLt)))
  simpa only [memoryScheduleGhostBirth,eq_self_iff_true,true_and] using hs
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cChronologicalRhoShift -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Exact finite chronological reindexing of the TRUE G_i / E_i
memory clock: post-G_i rho belongs to visit i, while pre-G_(i+1)
rho is charged at visit i+1. The terminal G_N and both boundary
vacuums are retained. No division by rho (zero permitted). -/
theorem memory_source_finite_rho_chronological_shift
    (N : ℕ) (G Pre Post : ℕ → ℂ)
    (hPre0 : Pre 0 = 1)
    (hPostN : Post N = 1) :
    (∏ i ∈ Finset.range N, G i * (Post i * Pre (i+1))) * G N =
    ∏ i ∈ Finset.range (N+1), (Pre i * G i * Post i) := by
  have hG := Finset.prod_range_succ G N
  have hPre := Finset.prod_range_succ' Pre N
  have hPost := Finset.prod_range_succ Post N
  simp_rw [Finset.prod_mul_distrib]
  rw [hPre0,mul_one] at hPre
  rw [hPostN,mul_one] at hPost
  rw [hG,hPre,hPost]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cFreshMuCount -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- The original E_i fresh-active mu is charged at most once,
precisely at visit a-1 if the lifespan's first visit a>0 is active
and it was not already active at a-1. No source-side counting
surrogate or independent endpoint assumption. -/
theorem memory_source_one_life_fresh_mu_product
    (N : ℕ) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1)) (mu : ℂ) :
    (∏ t ∈ Finset.range N,
      if memoryScheduleFresh A (some az) t then mu else 1) =
    if 0 < az.1.val ∧ az.1.val ∈ A ∧ az.1.val-1 ∉ A
      then mu else 1 := by
  by_cases ha : az.1.val = 0
  · have hz (t : ℕ) : ¬ memoryScheduleFresh A (some az) t := by
      simp only [memoryScheduleFresh]
      intro hf
      omega
    simp [ha,hz]
  · have hpos : 0 < az.1.val := Nat.pos_of_ne_zero ha
    let t0 := az.1.val-1
    have ht0 : t0 < N := by
      have hlt := az.1.isLt
      dsimp only [t0]
      omega
    have hsingle := Finset.prod_eq_single
      (s := Finset.range N)
      (f := fun t : ℕ => if memoryScheduleFresh A (some az) t then mu else 1)
      t0
      (by
        intro t ht hne
        have hf : ¬ memoryScheduleFresh A (some az) t := by
          intro he
          simp only [memoryScheduleFresh] at he
          have heq : t=t0 := by dsimp only [t0]; omega
          exact hne heq
        simp only [hf,ite_false])
      (by
        intro hn
        exact False.elim (hn (Finset.mem_range.mpr ht0)))
    have hsucc : t0+1=az.1.val := by dsimp only [t0]; omega
    rw [hsingle]
    by_cases hA : az.1.val ∈ A
    · by_cases hbefore : t0 ∈ A
      · have hprev : az.1.val-1 ∈ A := by simpa [t0] using hbefore
        simp [memoryScheduleFresh,hsucc,hA,hbefore,hprev,hpos]
      · have hprev : az.1.val-1 ∉ A := by simpa [t0] using hbefore
        simp [memoryScheduleFresh,hsucc,hA,hbefore,hprev,hpos]
    · simp [memoryScheduleFresh,hsucc,hA,hpos]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cRhoBoundary -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- The original finite lifespan source has no OLD pending prime
before G_0, including in the absent-prime case. Consequently the
pre-G_0 rho indicator is exactly one for any source residue clock. -/
theorem memory_original_source_pre_first_rho_one
    (n : ℕ) (A : Finset ℕ)
    (l : MemoryLifespanChoice (n+1))
    (p : ℕ) (h : ℕ → ZMod p) (rho : ℝ) :
    (if memoryScheduleBefore A l 0 ∧
        memoryScheduleResidue p h l 0 = 0
      then (rho : ℂ) else 1) = 1 := by
  cases l with
  | none => simp [memoryScheduleBefore]
  | some az =>
    simp [memoryScheduleBefore]

/-- No genuine original lifespan endpoint can lie past the final visit
n, so the post-G_n OLD pending rho indicator is exactly one. This is
derived from the original Fin(n+1) endpoint, not a terminal axiom. -/
theorem memory_original_source_post_last_rho_one
    (n : ℕ) (A : Finset ℕ)
    (l : MemoryLifespanChoice (n+1))
    (p : ℕ) (h : ℕ → ZMod p) (rho : ℝ) :
    (if memoryScheduleAfter A l n ∧
        memoryScheduleResidue p h l n = 0
      then (rho : ℂ) else 1) = 1 := by
  cases l with
  | none => simp [memoryScheduleAfter]
  | some az =>
    have hz : ¬ n < az.2.val := Nat.not_lt.mpr (Nat.le_of_lt_succ az.2.isLt)
    simp [memoryScheduleAfter,hz]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cDisjointRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- Exact disjoint decomposition of two original G-memory events,
with zero treated by ordinary source finite-set subtraction. -/
theorem memory_original_G_disjoint_coefficients
    (p : P) (alpha chi : ℂ) :
    (if p ∈ memoryGhostDeathSet A life i then alpha else 1) *
      (if p ∈ memoryContinuingZeroSet modulus A life offset i then chi else 1) =
    (if p ∈ memoryGhostDeathSet A life i then alpha
     else if p ∈ memoryZeroBeforeSet modulus A life offset i then chi else 1) := by
  by_cases hd : p ∈ memoryGhostDeathSet A life i
  · simp [memoryContinuingZeroSet,hd]
  · simp [memoryContinuingZeroSet,hd]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cGClockRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)
variable (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ)
variable (gp : PhysicalSourcePrime BP)

def memoryOriginalPrimePreRho : ℂ :=
  if memoryScheduleBefore (A gp.1 gp.2) (life gp.1 gp.2) i ∧
    memoryScheduleResidue (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2))) (life gp.1 gp.2) i = 0
  then (rho : ℂ) else 1

def memoryOriginalPrimePostRho : ℂ :=
  if memoryScheduleAfter (A gp.1 gp.2) (life gp.1 gp.2) i ∧
    memoryScheduleResidue (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2))) (life gp.1 gp.2) i = 0
  then (rho : ℂ) else 1

/-- The literal memory source row at one visit, BEFORE the unique
mu-tilde birth/active factor is inserted, and with BOTH genuine
chronological rho indicators. -/
def memoryOriginalPrimeClockRow : ℂ :=
  memoryOriginalPrimePreRho BP bigMod A life offset i rho gp *
  (if gp.2 ∈ memoryGhostDeathSet (A gp.1) (life gp.1) i then
    -(sourceVisitEta q N i : ℂ) / (rho : ℂ)
   else if gp.2 ∈ memoryZeroBeforeSet (bigMod gp.1) (A gp.1)
     (life gp.1) offset i then
    (sourceVisitQ q N i : ℂ) / (rho : ℂ)^2
   else 1) *
  (if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) i then
    -(sourceVisitEta q N i : ℂ) * (Vbig gp.1 : ℂ) / (rho : ℂ)
   else 1) *
  memoryOriginalPrimePostRho BP bigMod A life offset i rho gp

/-- The G_i birth mu is extracted EXACTLY ONCE from the true
ORIGINAL G branch. The four local clock factors then coincide with
the physical operational source row (before rho, death/continuation,
birth, after rho), without any schedule-support or nonzero premise. -/
theorem memory_original_G_clock_row_mu_factor
    (mu : (g : BG) → BP g → ℝ) :
    memoryOriginalPrimePreRho BP bigMod A life offset i rho gp *
      memoryPrimitiveGPerPrimeFactor BP bigMod A life offset i
        q rho N Vbig mu gp *
      memoryOriginalPrimePostRho BP bigMod A life offset i rho gp =
    memoryOriginalPrimeClockRow BP bigMod A life offset i
      q rho N Vbig gp *
      (if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) i
       then (mu gp.1 gp.2 : ℂ) else 1) := by
  have hdc := memory_original_G_disjoint_coefficients
    (bigMod gp.1) (A gp.1) (life gp.1) offset i gp.2
    (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
    ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
  unfold memoryOriginalPrimeClockRow memoryPrimitiveGPerPrimeFactor
  rw [← mul_assoc]
  rw [hdc]
  by_cases hb : gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) i
  · simp only [hb,if_true]
    ring
  · simp only [hb,if_false,mul_one]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cLiteralRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Literal four-factor operational visit row from the already checked
frozen prime scalar, with before/after OLD rho clock kept separate. -/
def memoryOriginalLiteralPrimeRow
    (A : Finset ℕ) (N : ℕ) (az : Fin (N+1) × Fin (N+1))
    (h : ℕ → ZMod (bigMod g p)) (q rho : ℝ) (V : ℝ) (i : ℕ) : ℂ :=
  let a := az.1.val
  let z := az.2.val
  (if (a < i ∧ i ≤ z ∧ i ∉ A) ∧ h i = h a
      then (rho : ℂ) else 1) *
  (if (z = i ∧ i ∉ A) ∧ h i = h a
      then -(sourceVisitEta q N i : ℂ) / (rho : ℂ)
   else if (a < i ∧ i ≤ z ∧ i ∉ A) ∧ h i = h a
      then (sourceVisitQ q N i : ℂ) / (rho : ℂ)^2
   else 1) *
  (if (a = i ∧ i ∉ A) ∧ h i = h a
      then -(sourceVisitEta q N i : ℂ) * (V : ℂ) / (rho : ℂ)
   else 1) *
  (if (a ≤ i ∧ i < z ∧ i ∉ A) ∧ h i = h a
      then (rho : ℂ) else 1)

/-- A supported ORIGINAL represented prime's true G/E OLD clock is
pointwise the PRECISE operational `localRow` inside the frozen-prime
scalar. The death and first-birth residue tests are proved from
the original lifespan endpoint residue equality; no hit assumption
is supplied independently. -/
theorem memory_source_supported_clock_row_is_literal
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ) (Vbig : BG → ℝ)
    (gp : PhysicalSourcePrime BP)
    (az : Fin (N+1) × Fin (N+1))
    (hl : life gp.1 gp.2 = some az)
    (hs : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2))
    (i : ℕ) :
    memoryOriginalPrimeClockRow BP bigMod A life offset
      i q rho N Vbig gp =
    memoryOriginalLiteralPrimeRow BP bigMod (g:=gp.1) (p:=gp.2)
      (A gp.1 gp.2) N az
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      q rho (Vbig gp.1) i := by
  let H : ℕ → ZMod (bigMod gp.1 gp.2) :=
    fun t => (offset t : ZMod (bigMod gp.1 gp.2))
  have hsup : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      H (A gp.1 gp.2) (some az) := by
    simpa only [hl] using hs
  have hendl : H az.2.val = H az.1.val := hsup.2.2.1
  have hdead : (gp.2 ∈ memoryGhostDeathSet (A gp.1) (life gp.1) i) ↔
       ((az.2.val = i ∧ i ∉ A gp.1 gp.2) ∧ H i = H az.1.val) := by
    constructor
    · intro hmem
      have ht : memoryScheduleTerminate (A gp.1 gp.2) (life gp.1 gp.2) i :=
        (Finset.mem_filter.mp hmem).2
      have hti : az.2.val = i ∧ i ∉ A gp.1 gp.2 := by
        simpa only [hl, memoryScheduleTerminate] using ht
      exact ⟨hti, by simpa only [← hti.1] using hendl⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [hl, memoryScheduleTerminate] using h.1⟩
  have hborn : (gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) i) ↔
       ((az.1.val = i ∧ i ∉ A gp.1 gp.2) ∧ H i = H az.1.val) := by
    constructor
    · intro hmem
      have ht : memoryScheduleGhostBirth (A gp.1 gp.2) (life gp.1 gp.2) i :=
        (Finset.mem_filter.mp hmem).2
      have hti : az.1.val = i ∧ i ∉ A gp.1 gp.2 := by
        simpa only [hl, memoryScheduleGhostBirth] using ht
      exact ⟨hti, by simpa only [← hti.1]⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [hl, memoryScheduleGhostBirth] using h.1⟩
  have hbzero : (gp.2 ∈ memoryZeroBeforeSet (bigMod gp.1) (A gp.1)
        (life gp.1) offset i) ↔
      ((az.1.val < i ∧ i ≤ az.2.val ∧ i ∉ A gp.1 gp.2) ∧
        H i = H az.1.val) := by
    simp only [memoryZeroBeforeSet,Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [hl,memoryScheduleBefore,memoryScheduleResidue,sub_eq_zero]
    rfl
  unfold memoryOriginalPrimeClockRow memoryOriginalPrimePreRho
    memoryOriginalPrimePostRho memoryOriginalLiteralPrimeRow
  dsimp only
  simp only [hl, memoryScheduleBefore, memoryScheduleAfter,
    memoryScheduleResidue,sub_eq_zero]
  simp only [hdead,hbzero,hborn]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cChronologicalEExtra -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- A genuine extra E_i contribution (promotion or fresh-mu) survives
the chronological G_i/E_i/G_N reindexing EXACTLY ONCE. This identity
uses no cancellation, works with zero-valued source coefficients,
and never charges terminal G_N an extra E_N step. -/
theorem memory_source_finite_clock_shift_with_E_extra
    (N : ℕ) (G Pre Post Extra : ℕ → ℂ)
    (hPre0 : Pre 0 = 1) (hPostN : Post N = 1) :
    (∏ i ∈ Finset.range N,
      G i * (Post i * Pre (i+1) * Extra i)) * G N =
    (∏ i ∈ Finset.range (N+1), Pre i * G i * Post i) *
      (∏ i ∈ Finset.range N, Extra i) := by
  have hclock := memory_source_finite_rho_chronological_shift
    N G Pre Post hPre0 hPostN
  have heq :
      (∏ i ∈ Finset.range N,
        G i * (Post i * Pre (i+1) * Extra i)) =
      (∏ i ∈ Finset.range N, G i * (Post i * Pre (i+1))) *
      (∏ i ∈ Finset.range N, Extra i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    _ = ((∏ i ∈ Finset.range N, G i * (Post i * Pre (i+1))) * G N) *
          (∏ i ∈ Finset.range N, Extra i) := by ring
    _ = _ := by rw [hclock]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cOriginalPrimeClockFactor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Exact ORIGINAL E_i non-rho factor for one prime: promoted
V^{-1} and a genuinely fresh active BIG mu. -/
def memoryOriginalPrimeEExtra
    (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
    (life : (g : BG) → BP g → MemoryLifespanChoice n)
    (i : ℕ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP) : ℂ :=
  (if memorySchedulePromote (A gp.1 gp.2) (life gp.1 gp.2) i
    then (1/(Vbig gp.1 : ℂ)) else 1) *
  (if memoryScheduleFresh (A gp.1 gp.2) (life gp.1 gp.2) i
    then (mu gp.1 gp.2 : ℂ) else 1)

/-- The original one-prime physical G_0 E_0 ... G_N coefficient,
with actual source OLD/ghost witness weights, is EXACTLY the
product of the literal operational visit rows, plus the source
initial-active/ghost-birth mu factors and REAL E_i V/fresh factors.
All time shifts, boundaries, and ordering are proved; none is
assumed from a probability kernel or from a frozen-target identity. -/
theorem memory_original_primitive_prime_chronological_rows
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ)
    (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP) :
    memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
      q rho Vbig mu gp =
    (if 0 ∈ A gp.1 gp.2 then (mu gp.1 gp.2 : ℂ) else 1) *
    (∏ t ∈ Finset.range (N+1),
      memoryOriginalPrimeClockRow BP bigMod A life offset t
        q rho N Vbig gp *
      (if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) t
        then (mu gp.1 gp.2 : ℂ) else 1)) *
    (∏ t ∈ Finset.range N,
      memoryOriginalPrimeEExtra BP A life t Vbig mu gp) := by
  let G : ℕ → ℂ := fun t =>
    memoryPrimitiveGPerPrimeFactor BP bigMod A life offset t q rho N Vbig mu gp
  let E : ℕ → ℂ := fun t =>
    memoryOriginalEPerPrimeRow BP bigMod A life offset t rho Vbig mu gp
  let Pre : ℕ → ℂ := fun t =>
    memoryOriginalPrimePreRho BP bigMod A life offset t rho gp
  let Post : ℕ → ℂ := fun t =>
    memoryOriginalPrimePostRho BP bigMod A life offset t rho gp
  let Extra : ℕ → ℂ := fun t =>
    memoryOriginalPrimeEExtra BP A life t Vbig mu gp
  let Row : ℕ → ℂ := fun t =>
    memoryOriginalPrimeClockRow BP bigMod A life offset t q rho N Vbig gp
  let Birth : ℕ → ℂ := fun t =>
    if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) t
      then (mu gp.1 gp.2 : ℂ) else 1
  let Input : ℂ := if 0 ∈ A gp.1 gp.2 then (mu gp.1 gp.2 : ℂ) else 1
  have hPre : Pre 0 = 1 := memory_original_source_pre_first_rho_one
    N (A gp.1 gp.2) (life gp.1 gp.2) (bigMod gp.1 gp.2)
    (fun t => (offset t : ZMod (bigMod gp.1 gp.2))) rho
  have hPost : Post N = 1 := memory_original_source_post_last_rho_one
    N (A gp.1 gp.2) (life gp.1 gp.2) (bigMod gp.1 gp.2)
    (fun t => (offset t : ZMod (bigMod gp.1 gp.2))) rho
  have hE (t : ℕ) : E t = Post t * Pre (t+1) * Extra t := by
    unfold E Post Pre Extra memoryOriginalEPerPrimeRow
      memoryPrimitiveERhoPerPrimeFactor memoryOriginalPrimeEExtra
      memoryOriginalPrimePreRho memoryOriginalPrimePostRho
    ring
  have hG (t : ℕ) : Pre t * G t * Post t = Row t * Birth t :=
    memory_original_G_clock_row_mu_factor BP bigMod A life offset
      t q rho N Vbig gp mu
  have hRaw :
      memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
        q rho Vbig mu gp =
      Input * ((∏ t ∈ Finset.range N, G t * E t) * G N) := by
    unfold memoryOriginalPrimitivePrimeScalar
    change Input * (∏ t : Fin N, G t.val * E t.val) * G N = _
    rw [Fin.prod_univ_eq_prod_range (fun t => G t * E t) N]
    ring
  have hPE :
      (∏ t ∈ Finset.range N, G t * E t) =
      (∏ t ∈ Finset.range N,
        G t * (Post t * Pre (t+1) * Extra t)) := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [hE t]
  have hGR :
      (∏ t ∈ Finset.range (N+1), Pre t * G t * Post t) =
      (∏ t ∈ Finset.range (N+1), Row t * Birth t) := by
    apply Finset.prod_congr rfl
    intro t ht
    exact hG t
  calc
    _ = Input * ((∏ t ∈ Finset.range N,
          G t * (Post t * Pre (t+1) * Extra t)) * G N) := by
          rw [hRaw,hPE]
    _ = Input * ((∏ t ∈ Finset.range (N+1),
          Pre t * G t * Post t) * (∏ t ∈ Finset.range N, Extra t)) := by
          rw [memory_source_finite_clock_shift_with_E_extra
            N G Pre Post Extra hPre hPost]
    _ = Input * ((∏ t ∈ Finset.range (N+1),
          Row t * Birth t) * (∏ t ∈ Finset.range N, Extra t)) := by
          rw [hGR]
    _ = _ := by dsimp only [Input,Row,Birth,Extra]; ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cUniqueMuCharge -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Exact one-time charging of the ORIGINAL physical BIG mu-tilde:
either the initial active slot at t=0, the true ghost birth at t=a,
or the true E fresh-active slot at t=a-1. These are exclusive and
exhaustive when the source lifespan supports all active labels.
In particular, multiple disjoint active runs NEVER duplicate mu:
later runs contribute only promotion V^{-1}. -/
theorem memory_source_one_supported_life_exact_mu
    (N : ℕ) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1))
    (hA : ∀ t ∈ A, az.1.val ≤ t)
    (mu : ℂ) :
    (if 0 ∈ A then mu else 1) *
      (∏ t ∈ Finset.range (N+1),
        if memoryScheduleGhostBirth A (some az) t then mu else 1) *
      (∏ t ∈ Finset.range N,
        if memoryScheduleFresh A (some az) t then mu else 1) = mu := by
  rw [memory_source_one_life_ghost_birth_mu_product]
  rw [memory_source_one_life_fresh_mu_product]
  by_cases ha : az.1.val ∈ A
  · by_cases hz : az.1.val = 0
    · have h0 : 0 ∈ A := by simpa only [hz] using ha
      simp [h0,hz]
    · have hpos : 0 < az.1.val := Nat.pos_of_ne_zero hz
      have hnotzero : 0 ∉ A := by
        intro h
        have hh := hA 0 h
        omega
      have hbefore : az.1.val-1 ∉ A := by
        intro h
        have hh := hA (az.1.val-1) h
        omega
      simp [ha,hz,hpos,hnotzero,hbefore]
  · have hnotzero : 0 ∉ A := by
      intro h
      have hh := hA 0 h
      have heq : az.1.val = 0 := by omega
      exact ha (heq ▸ h)
    simp [ha,hnotzero]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cPromotionShift -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- A true source E_i OLD-memory promotion is exactly the SAME prime
event counted by the literal frozen-prime operational scalar at visit
i+1. The upper bound i<z is derived from the actual active lifespan
support, not assumed; i+1 and i are distinct chronological clocks. -/
theorem memory_source_true_promotion_is_next_visit
    (N : ℕ) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1))
    (hA : ∀ t ∈ A, az.1.val ≤ t ∧ t ≤ az.2.val)
    (i : ℕ) (hi : i < N) :
    memorySchedulePromote A (some az) i ↔
      ((i+1) ∈ A ∧ 0 < i+1 ∧ az.1.val ≤ (i+1)-1 ∧
       (i+1)-1 < az.2.val ∧ (i+1)-1 ∉ A) := by
  simp only [memorySchedulePromote]
  constructor
  · rintro ⟨hnot,hactive,hlo⟩
    have hhi := (hA (i+1) hactive).2
    refine ⟨hactive,by omega,by omega,by omega,?_⟩
    simpa only [Nat.add_sub_cancel_right] using hnot
  · rintro ⟨hactive,hpos,hlo,hhi,hnot⟩
    exact ⟨by simpa only [Nat.add_sub_cancel_right] using hnot,
      hactive,by omega⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cPromotionProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- The product of ORIGINAL E_i promotion factors at i=0,...,N-1
is exactly ONE V^{-1} for each source frozen operational promotion
at t=1,...,N. The t=0 boundary contributes one. No V normalizer is
inserted or canceled speculatively, including for zero weights. -/
theorem memory_source_promotion_V_product_clock_exact
    (N : ℕ) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1))
    (hA : ∀ t ∈ A, az.1.val ≤ t ∧ t ≤ az.2.val)
    (Vinv : ℂ) :
    (∏ i ∈ Finset.range N,
      if memorySchedulePromote A (some az) i then Vinv else 1) =
    Vinv ^ ((Finset.range (N+1)).filter (fun t =>
      t ∈ A ∧ 0 < t ∧ az.1.val ≤ t-1 ∧ t-1 < az.2.val ∧ t-1 ∉ A)).card := by
  let P : ℕ → Prop := fun t =>
    t ∈ A ∧ 0 < t ∧ az.1.val ≤ t-1 ∧ t-1 < az.2.val ∧ t-1 ∉ A
  have h0 : ¬ P 0 := by simp [P]
  have heq :
      (∏ i ∈ Finset.range N,
        if memorySchedulePromote A (some az) i then Vinv else 1) =
      ∏ i ∈ Finset.range N,
        if P (i+1) then Vinv else 1 := by
    apply Finset.prod_congr rfl
    intro i hi
    exact if_congr
      (memory_source_true_promotion_is_next_visit N A az hA i
        (Finset.mem_range.mp hi)) rfl rfl
  rw [heq]
  have hmove := Finset.prod_range_succ'
    (fun t : ℕ => if P t then Vinv else 1) N
  have hboundary :
      (∏ i ∈ Finset.range (N+1), if P i then Vinv else 1) =
      ∏ i ∈ Finset.range N, if P (i+1) then Vinv else 1 := by
    simpa only [if_neg h0,mul_one] using hmove
  rw [← hboundary]
  rw [← Finset.prod_filter]
  rw [Finset.prod_const]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cPhysicalMuReassembly -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Finite original-physical source factor accounting:
all OLD/ghost G rows stay in the physical clock, the initial,
G-birth, and E-fresh mu collectively charge exactly one mu,
and the source E-promotions remain in their own V^{-1} product.
This is valid for zero-valued factors without cancellation. -/
theorem memory_finite_one_mu_reassembly
    (N : ℕ) (Input mu : ℂ)
    (Row Birth Promo Fresh : ℕ → ℂ)
    (hmu : Input *
      (∏ t ∈ Finset.range (N+1), Birth t) *
      (∏ i ∈ Finset.range N, Fresh i) = mu) :
    Input *
      (∏ t ∈ Finset.range (N+1), Row t * Birth t) *
      (∏ i ∈ Finset.range N, Promo i * Fresh i) =
    (∏ t ∈ Finset.range (N+1), Row t) * mu *
      (∏ i ∈ Finset.range N, Promo i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  calc
    _ = (∏ t ∈ Finset.range (N+1), Row t) *
       (Input * (∏ t ∈ Finset.range (N+1), Birth t) *
        (∏ i ∈ Finset.range N, Fresh i)) *
       (∏ i ∈ Finset.range N, Promo i) := by ring
    _ = _ := by rw [hmu]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cSourceMuPromotion -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]

/-- True ORIGINAL source prime G/E first-coordinate factors contribute
exactly one mu in total, no matter whether its first appearance is
initially active, born into pending memory, or fresh through E.
Multiple later active runs are NOT counted as new mu draws. -/
theorem memory_original_prime_source_mu_once
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (gp : PhysicalSourcePrime BP)
    (az : Fin (N+1) × Fin (N+1))
    (hl : life gp.1 gp.2 = some az)
    (hA : ∀ t ∈ A gp.1 gp.2, az.1.val ≤ t)
    (mu : ℂ) :
    (if 0 ∈ A gp.1 gp.2 then mu else 1) *
      (∏ t ∈ Finset.range (N+1),
        if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) t
        then mu else 1) *
      (∏ t ∈ Finset.range N,
        if memoryScheduleFresh (A gp.1 gp.2) (life gp.1 gp.2) t
        then mu else 1) = mu := by
  simp only [memoryGhostBirthSet,Finset.mem_filter,Finset.mem_univ,
    true_and,hl]
  exact memory_source_one_supported_life_exact_mu N
    (A gp.1 gp.2) az hA mu

/-- The physical ORIGINAL source E memory-promotion product on a
represented prime equals its frozen operational promotion exponent,
without assuming a nonzero V or canceling any mass. -/
theorem memory_original_prime_source_promotion_power
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (gp : PhysicalSourcePrime BP)
    (az : Fin (N+1) × Fin (N+1))
    (hl : life gp.1 gp.2 = some az)
    (hA : ∀ t ∈ A gp.1 gp.2, az.1.val ≤ t ∧ t ≤ az.2.val)
    (Vinv : ℂ) :
    (∏ t ∈ Finset.range N,
      if memorySchedulePromote (A gp.1 gp.2) (life gp.1 gp.2) t
        then Vinv else 1) =
    Vinv ^ ((Finset.range (N+1)).filter (fun t =>
      t ∈ A gp.1 gp.2 ∧ 0 < t ∧ az.1.val ≤ t-1 ∧
      t-1 < az.2.val ∧ t-1 ∉ A gp.1 gp.2)).card := by
  rw [hl]
  exact memory_source_promotion_V_product_clock_exact N
    (A gp.1 gp.2) az hA Vinv
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cRepresentedPrimeRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
set_option maxHeartbeats 750000

/-- CORE REPRESENTED-PRIME PHYSICAL FACTORIZATION.
For the original nonempty finite lifespan, the *entire genuine*
source G0 E0 ... GN coefficient equals exactly ONE original mu,
ONE V^{-1} per operational promotion, and the product of all
literal original four-factor lifespan rows. This counts original
mu/G/E witnesses, with no prime loss, no extra V, and no assumed
operational scalar equality or positivity. -/
theorem memory_source_represented_prime_true_row_factor
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ)
    (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP)
    (az : Fin (N+1) × Fin (N+1))
    (hl : life gp.1 gp.2 = some az)
    (hs : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2)) :
    memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
      q rho Vbig mu gp =
    (mu gp.1 gp.2 : ℂ) *
      (1/(Vbig gp.1 : ℂ)) ^
        ((Finset.range (N+1)).filter (fun t =>
          t ∈ A gp.1 gp.2 ∧ 0 < t ∧ az.1.val ≤ t-1 ∧
          t-1 < az.2.val ∧ t-1 ∉ A gp.1 gp.2)).card *
      (∏ t ∈ Finset.range (N+1),
        memoryOriginalLiteralPrimeRow BP bigMod (g:=gp.1) (p:=gp.2)
          (A gp.1 gp.2) N az
          (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
          q rho (Vbig gp.1) t) := by
  let Input : ℂ := if 0 ∈ A gp.1 gp.2 then (mu gp.1 gp.2 : ℂ) else 1
  let μ : ℂ := (mu gp.1 gp.2 : ℂ)
  let Vinv : ℂ := 1/(Vbig gp.1 : ℂ)
  let Row : ℕ → ℂ := fun t =>
    memoryOriginalPrimeClockRow BP bigMod A life offset t
      q rho N Vbig gp
  let Birth : ℕ → ℂ := fun t =>
    if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) t
      then μ else 1
  let Promo : ℕ → ℂ := fun t =>
    if memorySchedulePromote (A gp.1 gp.2) (life gp.1 gp.2) t
      then Vinv else 1
  let Fresh : ℕ → ℂ := fun t =>
    if memoryScheduleFresh (A gp.1 gp.2) (life gp.1 gp.2) t
      then μ else 1
  let EExtra : ℕ → ℂ := fun t =>
    memoryOriginalPrimeEExtra BP A life t Vbig mu gp
  have hsup : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (some az) := by simpa only [hl] using hs
  have hA (t : ℕ) (ht : t ∈ A gp.1 gp.2) :
      az.1.val ≤ t ∧ t ≤ az.2.val :=
    ⟨(hsup.2.1 t ht).1,(hsup.2.1 t ht).2.1⟩
  have hMu := memory_original_prime_source_mu_once BP A N life gp az hl
    (fun t ht => (hA t ht).1) μ
  have hProm := memory_original_prime_source_promotion_power BP
    A N life gp az hl hA Vinv
  have hChron := memory_original_primitive_prime_chronological_rows
    BP bigMod A N life offset q rho Vbig mu gp
  have hExtra (t : ℕ) : EExtra t = Promo t * Fresh t := rfl
  have hClock (t : ℕ) : Row t =
      memoryOriginalLiteralPrimeRow BP bigMod (g:=gp.1) (p:=gp.2)
        (A gp.1 gp.2) N az
        (fun j => (offset j : ZMod (bigMod gp.1 gp.2)))
        q rho (Vbig gp.1) t :=
    memory_source_supported_clock_row_is_literal BP bigMod
      A N life offset q rho Vbig gp az hl hs t
  change Input * (∏ t ∈ Finset.range (N+1), Birth t) *
    (∏ t ∈ Finset.range N, Fresh t) = μ at hMu
  change (∏ t ∈ Finset.range N, Promo t) = Vinv ^ _ at hProm
  change memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
    q rho Vbig mu gp =
      Input * (∏ t ∈ Finset.range (N+1), Row t * Birth t) *
      (∏ t ∈ Finset.range N, EExtra t) at hChron
  have hEProduct :
      (∏ t ∈ Finset.range N, EExtra t) =
      ∏ t ∈ Finset.range N, Promo t * Fresh t := by
    apply Finset.prod_congr rfl
    intro t ht
    exact hExtra t
  have hRowProduct :
      (∏ t ∈ Finset.range (N+1), Row t) =
      ∏ t ∈ Finset.range (N+1),
        memoryOriginalLiteralPrimeRow BP bigMod (g:=gp.1) (p:=gp.2)
          (A gp.1 gp.2) N az
          (fun j => (offset j : ZMod (bigMod gp.1 gp.2)))
          q rho (Vbig gp.1) t := by
    apply Finset.prod_congr rfl
    intro t ht
    exact hClock t
  calc
    _ = Input * (∏ t ∈ Finset.range (N+1), Row t * Birth t) *
        (∏ t ∈ Finset.range N, EExtra t) := hChron
    _ = Input * (∏ t ∈ Finset.range (N+1), Row t * Birth t) *
        (∏ t ∈ Finset.range N, Promo t * Fresh t) := by rw [hEProduct]
    _ = (∏ t ∈ Finset.range (N+1), Row t) * μ *
        (∏ t ∈ Finset.range N, Promo t) :=
          memory_finite_one_mu_reassembly N Input μ Row Birth Promo Fresh hMu
    _ = _ := by rw [hProm,hRowProduct]; dsimp only [μ,Vinv]; ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cRepresentedPrimeExact -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
set_option maxHeartbeats 600000
set_option maxRecDepth 2600

/-- Source-coefficient matching for a REAL original represented finite
lifespan, using the original physical mu-tilde and exact frozen
operational baseline 1/(V p b_p). No extra phi_p, Bernoulli
normalization or standalone zero-hit premise is supplied. -/
theorem memory_source_represented_prime_operational_exact
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ) (Vbig : BG → ℝ)
    (gp : PhysicalSourcePrime BP)
    (az : Fin (N+1) × Fin (N+1))
    (hl : life gp.1 gp.2 = some az)
    (hs : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2)) :
    memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
      q rho Vbig (physicalSourceMuTilde BP bigMod q N Vbig) gp =
    memoryFrozenPrimeOperationalScalar BP bigMod q rho N Vbig
      gp.1 gp.2
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2) := by
  have hrows := memory_source_represented_prime_true_row_factor BP bigMod
    A N life offset q rho Vbig
    (physicalSourceMuTilde BP bigMod q N Vbig) gp az hl hs
  rw [hrows,hl]
  unfold memoryFrozenPrimeOperationalScalar physicalSourceMuTilde
  dsimp only
  push_cast
  simp only [memoryOriginalLiteralPrimeRow]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cAllLifespansExact -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- COMPLETE one-prime source physical/frozen OPERATIONAL identity,
for BOTH genuine absent and represented source lifespans. The only
premise is the real original finite-lifespan schedule support. No
nonzero scalar, extra zero-hit, or algebraic normalization premise. -/
theorem memory_source_all_supported_primitive_prime_operational_exact
    (A : (g : BG) → BP g → Finset ℕ)
    (N : ℕ) (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) (q rho : ℝ) (Vbig : BG → ℝ)
    (gp : PhysicalSourcePrime BP)
    (hs : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2)) :
    memoryOriginalPrimitivePrimeScalar BP bigMod A N life offset
      q rho Vbig (physicalSourceMuTilde BP bigMod q N Vbig) gp =
    memoryFrozenPrimeOperationalScalar BP bigMod q rho N Vbig
      gp.1 gp.2
      (fun t => (offset t : ZMod (bigMod gp.1 gp.2)))
      (A gp.1 gp.2) (life gp.1 gp.2) := by
  cases hl : life gp.1 gp.2 with
  | none =>
    have hA : A gp.1 gp.2 = ∅ := by
      simpa only [hl,MemoryFrozenScheduleSupport] using hs
    simpa only [hl] using
      (memory_source_original_absent_prime_operational_exact BP
        bigMod A N life offset q rho Vbig
        (physicalSourceMuTilde BP bigMod q N Vbig) gp hl hA)
  | some az =>
    simpa only [hl] using
      (memory_source_represented_prime_operational_exact BP bigMod
        A N life offset q rho Vbig gp az hl hs)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cNonzeroFibreFrozenOperational -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- Complete ORIGINAL nonzero frozen root fibre = exactly one SMALL Haar
 state mass times literal residual E edges, and per-prime true operational
 physical schedule factors each with its own ORIGINAL baseline. The latter
 remain to be identified with the separately checked frozen prime terms. -/
theorem memory_source_original_nonzero_fibre_frozen_operational_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    (∏ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i) *
    (∏ gp : PhysicalSourcePrime BP,
      (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ) *
      memoryFrozenPrimeOperationalScalar BP bigMod q rho (2*R) Vbig gp.1 gp.2
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) := by
  have hprime : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hprime
  have hRoot := memory_source_original_nonzero_fibre_operational_prime_factor
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  rw [hRoot]
  congr 1
  apply Finset.prod_congr rfl
  intro gp hgp
  have hlocal := memory_source_all_supported_primitive_prime_operational_exact
    BP bigMod
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (2*R) (fun g p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    q rho Vbig gp (hs gp)
  rw [hlocal]
end Green64FullPhysicalE

end

end

