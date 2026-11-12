module

public import Green64.Library.Correlation.Part047
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.Part046
public import Green64.Library.Correlation.Part008
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part027
public import Green64.Library.Correlation.Part044
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Correlation / Part048

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryMarkedProjectedDirty -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal globally marked residual, with BOTH OLD projectors.
CLEAN is the original no-promotion/no-store witness restriction.
The full term is the original physicalOrientedBirthMarkedE. -/
def sourceOriginalMemoryMarkedProjectedDirty434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ) : ℂ :=
  let PF := fun Y t => @ite ℂ ((∑ g : BG,(Y.2 g).2.card) ≤ H) (Classical.propDecidable _) (F Y t) 0
  if (∑ g : BG,(X.2 g).2.card) ≤ H then
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st s PF -
      sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
          (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
        q rho Vs Vb mu Knu zeta theta o k st s PF) X else 0

def sourceOriginalMemoryMarkedEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) : ℝ :=
  ∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
    ∑ s ∈ (sourceOriginalMemoryBirthPool434 BP bigMod).powerset,
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) * ‖F X s‖^2

theorem source_original_memory_MARKED_E_DIRTY_split434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (s : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st s F -
    sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k st s F =
    sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k st s F +
    sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k st s F := by
  classical
  rw [← source_original_memory_MARKED_E_literal434]
  unfold sourceOriginalMemoryMarkedFilteredE434
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z <;>
  by_cases he : orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns s z <;>
  by_cases hp : ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty <;>
  by_cases hs : ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty <;>
  simp only [hl,he,hp,hs,not_true_eq_false,not_false_eq_true,true_and,and_true,
    false_and,and_false,ite_true,ite_false,add_zero,zero_add,sub_zero,sub_self]

theorem source_original_memory_MARKED_projected_DIRTY_split434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ) :
    sourceOriginalMemoryMarkedProjectedDirty434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k H F X s =
    sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k H F X s +
    sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k H F X s := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedDirty434 sourceOriginalMemoryMarkedProjectedE434
  dsimp only
  by_cases hx : (∑ g : BG,(X.2 g).2.card) ≤ H
  · simp only [if_pos hx]
    simp_rw [source_original_memory_MARKED_E_DIRTY_split434]
    exact source_original_memory_ORIGINAL_orbit_add434 SP smallMod BP bigMod J ell cap Vs mu _ _ X
  · simp only [if_neg hx,add_zero]

theorem source_original_memory_MARKED_projected_DIRTY_energy434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    let En := sourceOriginalMemoryMarkedEnergy434 SP smallMod BP bigMod J ell cap Vs Vb mu
    En (sourceOriginalMemoryMarkedProjectedDirty434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k H F) ≤
    2*En (sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k H F) +
    2*En (sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k H F) := by
  classical
  dsimp only
  unfold sourceOriginalMemoryMarkedEnergy434
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X hX
  apply Finset.sum_le_sum
  intro s hs
  rw [source_original_memory_MARKED_projected_DIRTY_split434]
  have hm := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  have hn (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
    nlinarith only [hh,sq_nonneg (‖a‖-‖b‖)]
  exact (mul_le_mul_of_nonneg_left (hn _ _) hm).trans_eq (by ring)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalProjectedRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


/-- Physical source G is exactly linear in its signed joint terminal test,
including all ghost witnesses and the numerical no-rebirth mask. -/
theorem source_original_ACTUAL_PHYSICAL_MARKED_G_sub434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N i V mu x seen
      (fun out st => F out st-A out st) =
    physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N i V mu x seen F -
    physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N i V mu x seen A := by
  unfold physicalGBirthMarkedRow
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> ring

theorem source_original_ACTUAL_ORBIT_sub434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F A : FullPhysicalState SP sm BP bm (J+ell) cap → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun st => F st-A st) y =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu F y -
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu A y := by
  unfold fullPhysicalOrbitAverage
  simp only [mul_sub,Finset.sum_sub_distrib,sub_div]

theorem source_original_ACTUAL_SYMMETRIC_G_sub434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen
      (fun out st => F out st-A out st) =
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F -
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen A := by
  unfold physicalMarkedSymmetricG
  rw [←source_original_ACTUAL_ORBIT_sub434]
  apply congrArg (fun t => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu t y)
  funext x
  exact source_original_ACTUAL_PHYSICAL_MARKED_G_sub434 SP sm BP bm J ell cap
    q rho N i V mu x seen F A

/-- A literal keep-filtered E is signed-linear before outer Fock averaging. -/
theorem source_original_ACTUAL_MARKED_FILTERED_E_sub434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen (fun out st => F out st-A out st) =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F -
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen A := by
  unfold sourceOriginalMemoryMarkedFilteredE434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> ring

/-- P(E_keep)P is signed-linear with BOTH TOTAL OLD endpoint projectors. -/
theorem source_original_ACTUAL_MARKED_PROJECTED_E_sub434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k H (fun out st => F out st-A out st) y seen =
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k H F y seen -
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns keep
      q rho Vs V mu K zeta theta o k H A y seen := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedE434
  by_cases hy : (∑ g : BG,(y.2 g).2.card) ≤ H
  · simp only [if_pos hy]
    rw [←source_original_ACTUAL_ORBIT_sub434]
    congr 1
    funext x
    unfold sourceOriginalMemoryMarkedFilteredE434
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hg : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
        keep x z ∧ orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
    · simp only [if_pos hg]
      by_cases ht : (∑ g : BG,
          ((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2.card) ≤ H
      · simp only [if_pos ht]
        ring
      · simp only [if_neg ht,mul_zero,sub_self]
    · simp only [if_neg hg,sub_self]
  · simp only [if_neg hy,sub_self]

/-- PEP from the original E equals the literal marked projector with
keep=True. No reachable-state hypothesis or manufactured symmetric row. -/
theorem source_original_ACTUAL_PEP_projected_true434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k H F y seen =
    if (∑ g : BG,(y.2 g).2.card) ≤ H then
      physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k y seen
        (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ H)
          (Classical.propDecidable _) (F out st) 0)
    else 0 := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedE434
  by_cases hy : (∑ g : BG,(y.2 g).2.card) ≤ H
  · simp only [if_pos hy]
    unfold physicalOrientedMarkedSymmetricE
    apply congrArg (fun t => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu t y)
    funext x
    simpa only using (source_original_memory_MARKED_E_literal434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen _)
  · simp only [if_neg hy]

/-- The local marked DIRTY operator is EXACTLY PEP-PCLEANP on the original
symmetric E, with the two OLD projector gates on the correct ends. -/
theorem source_original_ACTUAL_projected_TRUE_minus_CLEAN434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k H F y seen -
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      (fun _ z => sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns _ z)
      q rho Vs V mu K zeta theta o k H F y seen =
    sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H F y seen := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedDirty434 sourceOriginalMemoryMarkedProjectedE434
  by_cases hy : (∑ g : BG,(y.2 g).2.card) ≤ H
  · simp only [if_pos hy]
    rw [←source_original_ACTUAL_ORBIT_sub434]
    apply congrArg (fun t => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu t y)
    funext x
    let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
      fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ H)
        (Classical.propDecidable _) (F out st) 0
    change
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (fun _ _ => True) q rho Vs V mu K zeta theta o k x seen PF -
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k x seen PF =
      physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen PF -
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k x seen PF
    exact congrArg (fun z : ℂ => z -
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k x seen PF)
      (source_original_memory_MARKED_E_literal434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen PF)
  · simp only [if_neg hy,sub_self]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedSelectorComponents -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_memory_MARKED_SELECTOR_projected_components_L2434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hrho : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hprom : ∀ st,(∑ g : BG,(st.2 g).2.1.val) ≤ H →
      sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st ≤ R)
    (hfull : ∀ Y,sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k Y ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y))
    (htrans : ∀ X,sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k X ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X))
    (hstore : ∀ Y,(∑ g : BG,(Y.2 g).2.card) ≤ H →
      sourceOriginalMemoryOriginalFilteredDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
        (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
          (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
        q rho Vs Vb mu Knu zeta theta o k Y ≤
      R*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (f : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (seen : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ)
    (hseen : ∀ X,seen X ∈ (sourceOriginalMemoryBirthPool434 BP bigMod).powerset)
    (hf : ∀ Y,∀ t ∈ (sourceOriginalMemoryBirthPool434 BP bigMod).powerset,‖F Y t‖ ≤ ‖f Y‖) :
    let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
    let Hist := (sourceOriginalMemoryBirthPool434 BP bigMod).powerset
    let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
    let En := fun f : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ => ∑ X ∈ S,M X*‖f X‖^2
    En (fun X => sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k H F X (seen X)) ≤ R*C*En f ∧
    En (fun X => sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k H F X (seen X)) ≤ C*R*En f := by
  classical
  dsimp only
  let prom := fun (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) =>
    ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty
  let store := fun (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) =>
    (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty)
  let eligible := fun X : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
    (∑ g : BG,(X.2 g).2.card) ≤ H
  have hp := source_original_memory_MARKED_SELECTOR_compressed_L2_transfer434
    SP smallMod BP bigMod J ell m cap patterns prom q rho Vs Vb mu hVs hVb hmu
    Knu zeta theta o k (sourceOriginalMemoryBirthPool434 BP bigMod).powerset
    (source_original_memory_E_history_closed434 SP smallMod BP bigMod J ell m cap patterns)
    eligible eligible R C hR hC
    (by
      intro X hx
      apply source_original_memory_FILTERED_pair_row_of_row434
        SP smallMod BP bigMod J ell m cap patterns prom q rho Vs Vb mu hVs hVb hmu
        Knu zeta theta o k X R
      intro st he
      dsimp only [prom]
      rw [source_original_memory_PROMOTION_filtered_row434]
      apply hprom st
      rw [← source_original_memory_PAIR_OLD_projection434 SP smallMod BP bigMod J ell cap st,he]
      exact hx)
    (by
      intro Y hy
      apply le_trans _ (hfull Y)
      rw [← source_original_memory_FULL_pair_source_sum434]
      apply Finset.sum_le_sum
      intro X hX
      exact source_original_memory_FILTERED_density_pair_le_full434
        SP smallMod BP bigMod J ell m cap patterns prom q rho Vs Vb mu hVs hVb hmu
        Knu zeta theta o k X Y) F f seen hseen hf
  have hs := source_original_memory_MARKED_SELECTOR_compressed_L2_transfer434
    SP smallMod BP bigMod J ell m cap patterns store q rho Vs Vb mu hVs hVb hmu
    Knu zeta theta o k (sourceOriginalMemoryBirthPool434 BP bigMod).powerset
    (source_original_memory_E_history_closed434 SP smallMod BP bigMod J ell m cap patterns)
    eligible eligible C R hC hR
    (fun X _ => (source_original_memory_FILTERED_pair_row_of_transpose_column434
      SP smallMod BP bigMod J ell m cap patterns store q rho Vs Vb mu hVs hVb hmu hrho
      Knu zeta theta o k X).trans (htrans X))
    (by
      intro Y hy
      rw [source_original_memory_FILTERED_pair_source_sum434]
      exact hstore Y hy) F f seen hseen hf
  constructor
  · simpa only [sourceOriginalMemoryMarkedProjectedE434,prom,eligible] using hp
  · simpa only [sourceOriginalMemoryMarkedProjectedE434,store,eligible] using hs
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedSelectorEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalMemorySelectorEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℝ :=
  ∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) * ‖f X‖^2

theorem source_original_memory_MARKED_SELECTOR_projected_DIRTY_energy434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (seen : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ) :
    let En := sourceOriginalMemorySelectorEnergy434 SP smallMod BP bigMod J ell cap Vs Vb mu
    En (fun X => sourceOriginalMemoryMarkedProjectedDirty434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k H F X (seen X)) ≤
    2*En (fun X => sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k H F X (seen X)) +
    2*En (fun X => sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k H F X (seen X)) := by
  classical
  dsimp only
  unfold sourceOriginalMemorySelectorEnergy434
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X hX
  rw [source_original_memory_MARKED_projected_DIRTY_split434]
  have hm := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  have hn (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
    nlinarith only [hh,sq_nonneg (‖a‖-‖b‖)]
  exact (mul_le_mul_of_nonneg_left (hn _ _) hm).trans_eq (by ring)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalProjectedDirtyL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Applicable signed DIRTY estimate for the literal full E minus CLEAN,
with the ORIGINAL Fock compression and both explicit TOTAL OLD projectors.
This closes the unmarked projected E remainder, not the complete marked
G/history Memory chain or the OLD tail. No analytic saving premise remains. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_projected_DIRTY_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Bcolumn := 2*(B+1)+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → ℂ),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    (∑ X ∈ physicalFockOrbitSupport
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      (physicalOrbitMass
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        (J+ell) cap data.Vsmall mu X *
      sourceOriginalMemorySectorDensity434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell data.Vbig X) *
      ‖sourceOriginalMemoryCompressedProjectedDirty434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        q rho data.Vsmall data.Vbig mu
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q hA hB xi) zeta theta o k (Nat.ceil (L^2)) F X‖^2) ≤
    L^(-(2*B)) * (∑ y ∈ physicalFockOrbitSupport
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      (physicalOrbitMass
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        (J+ell) cap data.Vsmall mu y *
      sourceOriginalMemorySectorDensity434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell data.Vbig y)*‖F y‖^2) := by
  dsimp only
  let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
  let Bcolumn := 2*(B+1)+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hProm := source_original_memory_PHYSICAL_ORIGINAL_E_compressed_promotion_L2_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 (B+1) hq hq1 hr hr1 hc0
  have hStore := source_original_memory_PHYSICAL_ORIGINAL_E_compressed_store_only_L2_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 (B+1) hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hProm.1,?_⟩
  filter_upwards [hProm.2,hStore.2,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hprom hstore hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F
  classical
  let SP := fun g => {p : ℕ // p ∈ data.Ts g}
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Kn := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi
  let H := Nat.ceil (L^2)
  let PF := fun y : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+ell) =>
    if (∑ g : G,(y.2 g).2.card) ≤ H then F y else 0
  let S := physicalFockOrbitSupport SP (fun _ p => p.val) BP (fun _ p => p.val) (J+ell) cap
  let M := fun X => physicalOrbitMass SP (fun _ p => p.val) BP (fun _ p => p.val)
    (J+ell) cap data.Vsmall mu X *
    sourceOriginalMemorySectorDensity434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell data.Vbig X
  let En := fun f : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+ell) → ℂ =>
    ∑ X ∈ S,M X*‖f X‖^2
  let pop := fun X => fullPhysicalOrbitAverage SP (fun _ p => p.val) BP (fun _ p => p.val)
    (J+ell) cap data.Vsmall mu
    (fun st => if (∑ g : G,(st.2 g).2.1.val) ≤ H then
      sourceOriginalMemoryOriginalEPromotion434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m cap pats q rho data.Vsmall data.Vbig mu Kn zeta theta o k st PF else 0) X
  let sop := fun X => fullPhysicalOrbitAverage SP (fun _ p => p.val) BP (fun _ p => p.val)
    (J+ell) cap data.Vsmall mu
    (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap pats q rho data.Vsmall data.Vbig mu Kn zeta theta o k st PF) X
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hM (X) : 0 ≤ M X := source_original_memory_FULL_density_orbit_nonneg434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu X
  have hPF : En PF ≤ En F := by
    apply Finset.sum_le_sum
    intro X hX
    apply mul_le_mul_of_nonneg_left _ (hM X)
    dsimp only [PF]
    split_ifs <;> first | exact le_rfl | simpa only [norm_zero,zero_pow (by omega : 2≠0)] using sq_nonneg ‖F X‖
  have hp : En pop ≤ L^(-(2*(B+1)))*En PF := by
    exact hprom x Y Hprime data sep m hm hmJ cap hSmallUpper hBigLower hHarmonic
      hSmallGroupsLower blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB
      zeta theta o k ho hk0 hk PF
  have hs : En sop ≤ L^(-(2*(B+1)))*En F := by
    have hh := hstore x Y Hprime data sep m hm hmJ cap hSmallUpper hBigLower hHarmonic
      hSmallGroupsLower blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB
      zeta theta o k ho hk0 hk F
    convert hh using 1
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hPF (Real.rpow_nonneg hLp.le _))
  have hd := source_original_memory_PROJECTED_DIRTY_energy_components434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    q rho data.Vsmall data.Vbig mu hVs hVb hmu Kn zeta theta o k H F
  have hd' :
      En (sourceOriginalMemoryCompressedProjectedDirty434 SP (fun _ p => p.val)
        BP (fun _ p => p.val) J ell m cap pats q rho data.Vsmall data.Vbig mu Kn
        zeta theta o k H F) ≤ 2*En pop+2*En sop := by
    exact hd
  have hEn : 0 ≤ En F := Finset.sum_nonneg (fun X _ => mul_nonneg (hM X) (sq_nonneg _))
  have hpow : 4*L^(-(2*(B+1))) ≤ L^(-(2*B)) := by
    have hsq : (4:ℝ) ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-2)]
    calc
      _ ≤ L^2*L^(-(2*(B+1))) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_add hLp]
        congr 1
        norm_num
        ring
  apply hd'.trans
  calc
    _ ≤ 2*(L^(-(2*(B+1)))*En F)+2*(L^(-(2*(B+1)))*En F) :=
      add_le_add (mul_le_mul_of_nonneg_left hp' (by norm_num))
        (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = (4*L^(-(2*(B+1))))*En F := by ring
    _ ≤ L^(-(2*B))*En F := mul_le_mul_of_nonneg_right hpow hEn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalJointHistoryDIRTYL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Applicable SOURCE-ORIENTED marked DIRTY at ANY admissible source-history selector.
Uses the literal memorySourceGEChain adaptor memoryOrientationK, including
transposition of the complete joint RAW+comparison K on reverse edges.
Every source and target history is summed coherently in the physical density.
The global birth filter avoids any power-set cardinality cost.
No row, column, Gram or smallness assumption remains. The eventual threshold
precedes the moving carriers, histories and all phases. The original E is orbit averaged; the separate signed finite canonical
representation must be reconciled. G/CLEAN bounds remain separate. -/
theorem source_original_memory_PHYSICAL_SOURCE_ORIENTED_MARKED_DIRTY_JOINT_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Bcolumn := 2*(B+1)+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let En := sourceOriginalMemoryMarkedEnergy434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell cap data.Vsmall data.Vbig mu
    En (sourceOriginalMemoryMarkedProjectedDirty434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (memoryOrientationK (fun g => {p : ℕ // p ∈ data.Tb g}) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q hA hB xi) o) zeta theta o k (Nat.ceil (L^2)) F) ≤
    L^(-(2*B))*En F := by
  dsimp only
  let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
  let Bcolumn := 2*(B+1)+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hProm := source_original_memory_PHYSICAL_ORIGINAL_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Bcolumn hq hq1 hr hr1 hc0
  have hPromT := source_original_memory_PHYSICAL_TRANSPOSE_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Bcolumn hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hProm.1,?_⟩
  filter_upwards [hProm.2,hPromT.2,
    eventually_source_original_memory_PHYSICAL_ORIGINAL_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_memory_PHYSICAL_TRANSPOSE_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hprom hpromT hfull htrans hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F
  classical
  let SP := fun g => {p : ℕ // p ∈ data.Ts g}
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Kn := memoryOrientationK BP J ell m pats
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi) o
  let H := Nat.ceil (L^2)
  let En := sourceOriginalMemoryMarkedEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap data.Vsmall data.Vbig mu
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hh := source_original_memory_MARKED_projected_components_L2434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le Kn zeta theta o k H
    (L^Ccol) (L^(-Bcolumn)) (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _)
    (by
      intro st hOld
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hprom x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta o k ho hk0 hk)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hpromT x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta o k ho hk0 hk))
    (by
      intro y
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hfull x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k y)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (htrans x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k y))
    (by
      intro X
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (htrans x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta (-o) k X)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hfull x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta (-o) k X))
    (by
      intro y hy
      apply source_original_memory_STORE_ONLY_density_column_of_reverse_row434
        SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
        q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le Kn zeta theta o k y (L^(-Bcolumn))
      intro st he
      have hOld : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) := by
        rw [← source_original_memory_PAIR_OLD_projection434
          SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap st,he]
        exact hy
      have hoNeg : -o=1 ∨ -o= -1 := by rcases ho with h|h <;> simp [h]
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hpromT x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta (-o) k hoNeg hk0 hk)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hprom x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta (-o) k hoNeg hk0 hk)) F
  have hd := source_original_memory_MARKED_projected_DIRTY_energy434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    q rho data.Vsmall data.Vbig mu hVs hVb hmu Kn zeta theta o k H F
  have hEn : 0 ≤ En F := by
    dsimp only [En, sourceOriginalMemoryMarkedEnergy434]
    apply Finset.sum_nonneg
    intro X hX
    apply Finset.sum_nonneg
    intro seen hseen
    exact mul_nonneg (source_original_memory_FULL_density_orbit_nonneg434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap data.Vsmall data.Vbig mu hVs hVb hmu X) (sq_nonneg _)
  have hpow : 4*(L^(-Bcolumn)*L^Ccol) ≤ L^(-(2*B)) := by
    rw [← Real.rpow_add hLp,show -Bcolumn+Ccol= -(2*(B+1)) by dsimp only [Bcolumn];ring]
    have hsq : (4:ℝ) ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-2)]
    calc
      _ ≤ L^2*L^(-(2*(B+1))) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_add hLp]
        congr 1
        norm_num
        ring
  apply hd.trans
  calc
    _ ≤ 2*(L^(-Bcolumn)*L^Ccol*En F)+2*(L^Ccol*L^(-Bcolumn)*En F) :=
      add_le_add (mul_le_mul_of_nonneg_left hh.1 (by norm_num))
        (mul_le_mul_of_nonneg_left hh.2 (by norm_num))
    _ = (4*(L^(-Bcolumn)*L^Ccol))*En F := by ring
    _ ≤ L^(-(2*B))*En F := mul_le_mul_of_nonneg_right hpow hEn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalMarkedOrientedDirtyL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Applicable SOURCE-ORIENTED marked DIRTY at ANY admissible source-history selector.
Uses the literal memorySourceGEChain adaptor memoryOrientationK, including
transposition of the complete joint RAW+comparison K on reverse edges.
A physical envelope bounds target tests uniformly in history. This avoids the
counting-measure terminal-history cost and retains the exact global birth filter.
No row, column, Gram or smallness assumption remains. The eventual threshold
precedes the moving carriers, histories and all phases. Full G/Memory
propagation and OLD tails remain separate obligations. -/
theorem source_original_memory_PHYSICAL_SOURCE_ORIENTED_MARKED_DIRTY_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Bcolumn := 2*(B+1)+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (f : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → ℂ)
      (seen : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → Finset ℕ)
      (hseen : ∀ X,seen X ∈ (sourceOriginalMemoryBirthPool434
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)).powerset)
      (hf : ∀ Y,∀ t ∈ (sourceOriginalMemoryBirthPool434
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)).powerset,‖F Y t‖ ≤ ‖f Y‖),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let En := sourceOriginalMemorySelectorEnergy434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell cap data.Vsmall data.Vbig mu
    En (fun X => sourceOriginalMemoryMarkedProjectedDirty434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (memoryOrientationK (fun g => {p : ℕ // p ∈ data.Tb g}) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q hA hB xi) o) zeta theta o k (Nat.ceil (L^2)) F X (seen X)) ≤
    L^(-(2*B))*En f := by
  dsimp only
  let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
  let Bcolumn := 2*(B+1)+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hProm := source_original_memory_PHYSICAL_ORIGINAL_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Bcolumn hq hq1 hr hr1 hc0
  have hPromT := source_original_memory_PHYSICAL_TRANSPOSE_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Bcolumn hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hProm.1,?_⟩
  filter_upwards [hProm.2,hPromT.2,
    eventually_source_original_memory_PHYSICAL_ORIGINAL_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_memory_PHYSICAL_TRANSPOSE_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hprom hpromT hfull htrans hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F f seen hseen hf
  classical
  let SP := fun g => {p : ℕ // p ∈ data.Ts g}
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Kn := memoryOrientationK BP J ell m pats
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi) o
  let H := Nat.ceil (L^2)
  let En := sourceOriginalMemorySelectorEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap data.Vsmall data.Vbig mu
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hh := source_original_memory_MARKED_SELECTOR_projected_components_L2434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le Kn zeta theta o k H
    (L^Ccol) (L^(-Bcolumn)) (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _)
    (by
      intro st hOld
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hprom x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta o k ho hk0 hk)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hpromT x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta o k ho hk0 hk))
    (by
      intro y
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hfull x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k y)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (htrans x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k y))
    (by
      intro X
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (htrans x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta (-o) k X)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hfull x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
            blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta (-o) k X))
    (by
      intro y hy
      apply source_original_memory_STORE_ONLY_density_column_of_reverse_row434
        SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
        q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le Kn zeta theta o k y (L^(-Bcolumn))
      intro st he
      have hOld : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) := by
        rw [← source_original_memory_PAIR_OLD_projection434
          SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap st,he]
        exact hy
      have hoNeg : -o=1 ∨ -o= -1 := by rcases ho with h|h <;> simp [h]
      by_cases ho1 : o=1
      · simpa only [Kn,memoryOrientationK,if_pos ho1] using
          (hpromT x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta (-o) k hoNeg hk0 hk)
      · simpa only [Kn,memoryOrientationK,if_neg ho1] using
          (hprom x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
            hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
            hA hB hhA hhB zeta theta (-o) k hoNeg hk0 hk)) F f seen hseen hf
  have hd := source_original_memory_MARKED_SELECTOR_projected_DIRTY_energy434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    q rho data.Vsmall data.Vbig mu hVs hVb hmu Kn zeta theta o k H F seen
  have hEn : 0 ≤ En f := by
    apply Finset.sum_nonneg
    intro X hX
    exact mul_nonneg (source_original_memory_FULL_density_orbit_nonneg434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap data.Vsmall data.Vbig mu
      hVs hVb hmu X) (sq_nonneg _)
  have hpow : 4*(L^(-Bcolumn)*L^Ccol) ≤ L^(-(2*B)) := by
    rw [← Real.rpow_add hLp,show -Bcolumn+Ccol= -(2*(B+1)) by dsimp only [Bcolumn];ring]
    have hsq : (4:ℝ) ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-2)]
    calc
      _ ≤ L^2*L^(-(2*(B+1))) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_add hLp]
        congr 1
        norm_num
        ring
  apply hd.trans
  calc
    _ ≤ 2*(L^(-Bcolumn)*L^Ccol*En f)+2*(L^Ccol*L^(-Bcolumn)*En f) :=
      add_le_add (mul_le_mul_of_nonneg_left hh.1 (by norm_num))
        (mul_le_mul_of_nonneg_left hh.2 (by norm_num))
    _ = (4*(L^(-Bcolumn)*L^Ccol))*En f := by ring
    _ ≤ L^(-(2*B))*En f := mul_le_mul_of_nonneg_right hpow hEn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostBackground -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]

/-- A never-active prime's complete marked vacuum block. If it has
already appeared in the global seen set, every ghost-birth contribution
is removed. Otherwise its terminal observation keeps the inserted
NUMERICAL prime. The terminal function need not factor over primes. -/
def sourceOriginalPhysicalGhostBackgroundRow434
    (q : ℝ) (N : ℕ) (Vb : BG → ℝ) (g : BG) (p : BP g)
    (positions : ℕ → ZMod (modulus g p)) (seen : Finset ℕ)
    (F : Finset ℕ → ℂ) : ℂ :=
  (physicalSourceBaseline BP modulus q N g p:ℂ) *
    sourceOriginalGhostReturnLiteralChain434
      (sourceOriginalGhostSourceVisits434 q N positions)
      (Vb g*physicalSourceMuTilde BP modulus q N Vb g p)
      (sourceOriginalGhostReturnTerminal434
        (F seen) (if modulus g p ∈ seen then 0 else F (insert (modulus g p) seen)))
      .unborn

theorem source_original_PHYSICAL_GHOST_BACKGROUND_row_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (g : BG) (p : BP g) (hV : Vb g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP modulus q N g p)
    (positions : ℕ → ZMod (modulus g p))
    (U seen : Finset ℕ) (hpU : modulus g p ∈ U) (hs : seen ⊆ U)
    (F : Finset ℕ → ℂ) (M : ℝ) (hf : ∀ t, t ⊆ U → ‖F t‖ ≤ M) :
    ‖sourceOriginalPhysicalGhostBackgroundRow434 BP modulus q N Vb g p positions seen F‖ ≤ M := by
  have hA := hf seen hs
  have hM : 0 ≤ M := (norm_nonneg _).trans hA
  have hB : ‖if modulus g p ∈ seen then (0:ℂ) else F (insert (modulus g p) seen)‖ ≤ M := by
    split_ifs
    · simpa only [norm_zero] using hM
    · exact hf _ (Finset.insert_subset_iff.mpr ⟨hpU,hs⟩)
  have hcard : (modulus g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (modulus g p)
  have hlam : Vb g*physicalSourceMuTilde BP modulus q N Vb g p =
      1/((modulus g p:ℝ)*physicalSourceBaseline BP modulus q N g p) := by
    unfold physicalSourceMuTilde
    field_simp [hV,hcard,ne_of_gt hb]
  have hh := source_original_GHOST_RETURN_BASELINE_terminal_envelope434
    (sourceOriginalGhostSourceVisits434 q N positions)
    (source_original_GHOST_SOURCE_visits_unit434 q hq hq1 N positions)
    (by simpa only [ZMod.card,source_original_GHOST_SOURCE_visits_sum434,
      physicalSourceBaseline] using hb)
    (F seen) (if modulus g p ∈ seen then 0 else F (insert (modulus g p) seen)) M hA hB
  simpa only [sourceOriginalPhysicalGhostBackgroundRow434,hlam,ZMod.card,
    source_original_GHOST_SOURCE_visits_sum434,physicalSourceBaseline] using hh

def sourceOriginalPhysicalGhostBackgroundChain434
    (q : ℝ) (N : ℕ) (Vb : BG → ℝ)
    (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
    (primes : List (Sigma BP)) (F : Finset ℕ → ℂ) : Finset ℕ → ℂ :=
  match primes with
  | [] => F
  | x::xs => fun seen =>
      sourceOriginalPhysicalGhostBackgroundRow434 BP modulus q N Vb x.1 x.2
        (positions x.1 x.2) seen
        (sourceOriginalPhysicalGhostBackgroundChain434 q N Vb positions xs F)

/-- Joint-history envelope for the exact resummed background blocks.
The bound is independent of both visit count and number of background
primes, and allows an arbitrary shared terminal function of seen.
This theorem does NOT assert extraction of these blocks from mixed E/G. -/
theorem source_original_PHYSICAL_GHOST_BACKGROUND_chain_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (hV : ∀ g,Vb g ≠ 0)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
    (primes : List (Sigma BP)) (F : Finset ℕ → ℂ) (M : ℝ)
    (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ M)
    (seen : Finset ℕ) (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset) :
    ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q N Vb positions primes F seen‖ ≤ M := by
  induction primes generalizing seen with
  | nil => exact hf seen hs
  | cons x xs ih =>
    apply source_original_PHYSICAL_GHOST_BACKGROUND_row_envelope434
      BP modulus q hq hq1 N Vb x.1 x.2 (hV x.1) (hb x.1 x.2) (positions x.1 x.2)
      (sourceOriginalMemoryBirthPool434 BP modulus) seen
    · exact Finset.mem_biUnion.mpr ⟨x.1,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨x.2,Finset.mem_univ _,rfl⟩⟩
    · exact Finset.mem_powerset.mp hs
    · intro t ht
      exact ih t (Finset.mem_powerset.mpr ht)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostBackgroundUniform -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The source depth is N=2 ceil(L^0.52). The threshold comes only
from c>0, BEFORE all moving groups, prime carriers, positions,
background lists, seen sets, envelopes and terminal functions.
This is an applicable estimate for the resummed background block,
not an assertion that the whole mixed Memory chain equals it. -/
theorem eventually_source_original_PHYSICAL_GHOST_BACKGROUND_source_depth434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (Vb : BG → ℝ)
      (hV : ∀ g,0 < Vb g)
      (hprimeScale : ∀ g p,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
      (primes : List (Sigma BP)) (F : Finset ℕ → ℂ) (M : ℝ)
      (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ M)
      (seen : Finset ℕ)
      (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset),
      ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q
        (2*Nat.ceil (L^(0.52:ℝ))) Vb positions primes F seen‖ ≤ M := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro BG _ _ BP _ _ modulus _ q hq hq1 Vb hV hprimeScale positions primes F M hf seen hs
  apply source_original_PHYSICAL_GHOST_BACKGROUND_chain_envelope434
    BP modulus q hq hq1 _ Vb (fun g => ne_of_gt (hV g)) _ positions primes F M hf seen hs
  intro g p
  have hh := (source_original_B26_physical_baseline_half434 BP modulus q hq hq1
    (2*Nat.ceil (L^(0.52:ℝ))) g p (hL (modulus g p) (hprimeScale g p))).1
  linarith only [hh]

/-- In particular the exact birth-parity terminal observation is kept
as an observable; its modulus-one envelope costs no number of histories. -/
theorem eventually_source_original_PHYSICAL_GHOST_BACKGROUND_birth_parity434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (Vb : BG → ℝ)
      (hV : ∀ g,0 < Vb g)
      (hprimeScale : ∀ g p,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
      (primes : List (Sigma BP)) (seen : Finset ℕ)
      (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset),
      ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q
        (2*Nat.ceil (L^(0.52:ℝ))) Vb positions primes
        (fun t => (-1:ℂ)^t.card) seen‖ ≤ 1 := by
  filter_upwards [eventually_source_original_PHYSICAL_GHOST_BACKGROUND_source_depth434 c hc] with L hL
  intro BG _ _ BP _ _ modulus _ q hq hq1 Vb hV hprimeScale positions primes seen hs
  apply hL BP modulus q hq hq1 Vb hV hprimeScale positions primes
    (fun t => (-1:ℂ)^t.card) 1 _ seen hs
  intro t ht
  simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## OriginalSmallHaarGatedConditionalL2 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 9000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]

/-- Literal original SMALL Haar physical target kernel, with exact
J+ell permutation pair, signed D-dependent integer step, and
all original source/target shared slots. The extra keep can be any
nonseparable predicate on the genuine target SMALL state; it does
not replace SMALL states with independent prime draws. -/
noncomputable def green64_original_SMALL_target_weight434
    (J ell : ℕ) (q : ℝ) (Vs : SG → ℝ)
    (step : ℤ) (sigma tau : GroupPermFamily (G := SG) (J+ell))
    (x : GroupState SP sm (J+ell))
    (keep : GroupState SP sm (J+ell) → Prop)
    (y : GroupState SP sm (J+ell)) : ℝ :=
  if keep y then
    ‖groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
      step (fun _ _ => (1:ℂ)) sigma tau x y‖
  else 0

/-- The original literal D-step SMALL Haar target law, under an
arbitrary extra joint-dependent target mask, has a weighted L2 bound
with precisely the already-proved SOURCE SMALL row constant C.
Crucially C depends on ell, q and original Vs, NOT on J, number
of SMALL targets, signed step or a Fourier cell xi. The arbitrary
complex target test remains INSIDE the weighted energy. -/
theorem green64_original_SMALL_target_gated_L2_no_card434
    (J ell : ℕ) (q : ℝ) (Vs : SG → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hVs : ∀ g, 0 < Vs g)
    (step : ℤ) (sigma tau : GroupPermFamily (G := SG) (J+ell))
    (x : GroupState SP sm (J+ell))
    (keep : GroupState SP sm (J+ell) → Prop)
    (F : GroupState SP sm (J+ell) → ℂ) :
    let C : ℝ := ∏ g : SG, memorySmallRowConstant q (Vs g) ell
    let w := green64_original_SMALL_target_weight434 SP sm J ell q Vs step sigma tau x keep
    (∑ y, w y * ‖F y‖)^2 ≤ C * (∑ y, w y * ‖F y‖^2) := by
  classical
  let W := GroupState SP sm (J+ell)
  let C : ℝ := ∏ g : SG, memorySmallRowConstant q (Vs g) ell
  let w : W → ℝ := green64_original_SMALL_target_weight434
    SP sm J ell q Vs step sigma tau x keep
  change (∑ y : W, w y * ‖F y‖)^2 ≤
    C * (∑ y : W, w y * ‖F y‖^2)
  have hw (y : W) : 0 ≤ w y := by
    dsimp only [w,green64_original_SMALL_target_weight434]
    split_ifs
    · exact norm_nonneg _
    · exact le_refl _
  have hRow : (∑ y : W,
      ‖groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
         step (fun _ _ => (1:ℂ)) sigma tau x y‖) ≤ C := by
    simpa only [C,norm_one,one_mul] using
      source_original_memory_SOURCE_SMALL_group_kernel_row434
        SP sm J ell q Vs hq hq1 hVs step (fun _ _ => (1:ℂ)) sigma tau x
  have hTotal : (∑ y : W, w y) ≤ C := by
    calc
      _ ≤ ∑ y : W,
        ‖groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
          step (fun _ _ => (1:ℂ)) sigma tau x y‖ := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases h : keep y
          · simp [w,green64_original_SMALL_target_weight434,h]
          · simpa [w,green64_original_SMALL_target_weight434,h] using
              (norm_nonneg (groupPermutedKernel SP sm (J+ell) q Vs
                (sourceSmallShared J ell) step (fun _ _ => (1:ℂ)) sigma tau x y))
      _ ≤ C := hRow
  have hEnergy : 0 ≤ (∑ y : W, w y * ‖F y‖^2) :=
    Finset.sum_nonneg (fun y hy => mul_nonneg (hw y) (sq_nonneg _))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset W)
    (fun y => Real.sqrt (w y)) (fun y => Real.sqrt (w y) * ‖F y‖)
  have hLeft :
      (∑ y : W, Real.sqrt (w y) * (Real.sqrt (w y) * ‖F y‖)) =
      ∑ y : W, w y * ‖F y‖ := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [← mul_assoc,Real.mul_self_sqrt (hw y)]
  have hMass : (∑ y : W, (Real.sqrt (w y))^2) = ∑ y : W, w y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact Real.sq_sqrt (hw y)
  have hEnergyId : (∑ y : W, (Real.sqrt (w y) * ‖F y‖)^2) =
      ∑ y : W, w y * ‖F y‖^2 := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [mul_pow,Real.sq_sqrt (hw y)]
  rw [hLeft,hMass,hEnergyId] at hCS
  calc
    _ ≤ (∑ y : W, w y) * (∑ y : W, w y * ‖F y‖^2) := hCS
    _ ≤ C * (∑ y : W, w y * ‖F y‖^2) :=
      mul_le_mul_of_nonneg_right hTotal hEnergy
end Green64Analytic.CorrelationSquare

end

end

