module

public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Correlation / PhysicalGhostWitnessCollapse

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGhostWitnessCollapse -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalFockFromList434 {U : Type} {B : ℕ}
    (l : List U) (h : l.length ≤ B) : FockState U B :=
  ⟨⟨l.length, Nat.lt_succ_of_le h⟩, l.get⟩

theorem source_original_fock_to_from_list434 {U : Type} {B : ℕ}
    (l : List U) (h : l.length ≤ B) :
    fockToList (sourceOriginalFockFromList434 l h) = l := by
  simp [fockToList, sourceOriginalFockFromList434]

theorem source_original_fock_to_list_injective434 {U : Type} {B : ℕ} :
    Function.Injective (@fockToList U B) := by
  intro x y he
  rcases x with ⟨j,f⟩
  rcases y with ⟨k,g⟩
  have hj : j=k := by
    apply Fin.ext
    simpa only [fockToList,List.length_ofFn] using congrArg List.length he
  subst k
  have hf : f=g := List.ofFn_injective he
  subst g
  rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

def sourceOriginalPhysicalGhostWitnessFits434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x) : Prop :=
  ∀ g, (afterGhost (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2).length ≤ cap g

def sourceOriginalPhysicalGhostWitnessTarget434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c) :
    FullPhysicalState SP sm BP bm M cap :=
  (x.1,fun g => ((x.2 g).1,
    sourceOriginalFockFromList434
      (afterGhost (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2) (hc g)))

def sourceOriginalPhysicalGhostWitnessCoefficient434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x) : ℂ :=
  ∏ g, sourceGhostTerm (fockToList ((x.2 g).2))
    (fun z : Atom (BP g) (bm g) => z.2=0) (c g).1.1 (c g).2.2
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))
    (sourceBirthNu (fun p => (mu g p:ℂ)))

/-- The original joint G witness has exactly one ordered output whenever
its actual OLD/fresh list fits the original Fock cutoff. -/
theorem source_original_PHYSICAL_G_witness_target434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c) :
    physicalGBranchTerm SP sm BP bm M cap q rho N i Vb mu x y c =
    if y=sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c hc then
      sourceOriginalPhysicalGhostWitnessCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c
    else 0 := by
  classical
  by_cases hy : y=sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c hc
  · subst y
    simp [physicalGBranchTerm,sourceOriginalPhysicalGhostWitnessTarget434,
      ghostWitnessTerm,source_original_fock_to_from_list434,
      sourceOriginalPhysicalGhostWitnessCoefficient434]
  · rw [if_neg hy]
    by_contra hn
    obtain ⟨hxy,hout⟩ := physical_nonzero_ghost_witness_is_operational
      SP sm BP bm M cap q rho N i Vb mu x y c hn
    apply hy
    apply Prod.ext
    · exact hxy.1.symm
    · funext g
      apply Prod.ext
      · exact (hxy.2 g).symm
      · apply source_original_fock_to_list_injective434
        simpa only [sourceOriginalPhysicalGhostWitnessTarget434,
          source_original_fock_to_from_list434] using (hout g).symm

theorem source_original_PHYSICAL_G_witness_nofit_zero434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hc : ¬sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c) :
    physicalGBranchTerm SP sm BP bm M cap q rho N i Vb mu x y c = 0 := by
  by_contra hn
  obtain ⟨_,hout⟩ := physical_nonzero_ghost_witness_is_operational
    SP sm BP bm M cap q rho N i Vb mu x y c hn
  apply hc
  intro g
  rw [hout g,fockToList_length]
  exact Nat.le_of_lt_succ ((y.2 g).2).1.isLt

/-- Exact collapse of the target Fock sum, including its true cutoff.
No distinctness or quotient of repeated atoms is assumed. -/
theorem source_original_PHYSICAL_G_witness_output_sum434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (F : FullPhysicalOutput SP sm BP bm M → ℂ) :
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      physicalGBranchTerm SP sm BP bm M cap q rho N i Vb mu x y c *
        F (physicalFockProjection SP sm BP bm M cap y)) =
    if hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c then
      sourceOriginalPhysicalGhostWitnessCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c *
        F (physicalFockProjection SP sm BP bm M cap
          (sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c hc))
    else 0 := by
  classical
  split_ifs with hc
  · simp_rw [source_original_PHYSICAL_G_witness_target434 SP sm BP bm M cap
      q rho N i Vb mu x _ c hc]
    simp
  · simp_rw [source_original_PHYSICAL_G_witness_nofit_zero434 SP sm BP bm M cap
      q rho N i Vb mu x _ c hc]
    simp

/-- All original OLD and fresh witnesses remain. The only removed index
is the deterministic ordered target, and the numerical global birth gate
is still applied before summation. -/
def sourceOriginalPhysicalMarkedGhostCollapsed434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ c : FullGhostWitness SP sm BP bm M cap x,
    if physicalGhostBatchEligible SP sm BP bm M cap x seen c then
      if hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c then
        sourceOriginalPhysicalGhostWitnessCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c *
          F (physicalFockProjection SP sm BP bm M cap
            (sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c hc))
            (seen ∪ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset)
      else 0
    else 0

theorem source_original_PHYSICAL_MARKED_G_target_collapse434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i Vb mu x seen F =
      sourceOriginalPhysicalMarkedGhostCollapsed434 SP sm BP bm M cap
        q rho N i Vb mu x seen F := by
  classical
  unfold physicalGBirthMarkedRow sourceOriginalPhysicalMarkedGhostCollapsed434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases he : physicalGhostBatchEligible SP sm BP bm M cap x seen c
  · simp only [if_pos he]
    exact source_original_PHYSICAL_G_witness_output_sum434 SP sm BP bm M cap
      q rho N i Vb mu x c
      (fun y => F y (seen ∪ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset))
  · simp [he]

/-- Exact insertion into the source symmetric G. The original harmonic
and 1/j! orbit average is literally unchanged on the right-hand side. -/
theorem source_original_PHYSICAL_SYMMETRIC_G_target_collapse434
    (J ell : ℕ) (q rho : ℝ) (N i : ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs Vb mu y seen F =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => sourceOriginalPhysicalMarkedGhostCollapsed434 SP sm BP bm
        (J+ell) cap q rho N i Vb mu x seen F) y := by
  unfold physicalMarkedSymmetricG
  congr 1
  funext x
  exact source_original_PHYSICAL_MARKED_G_target_collapse434 SP sm BP bm
    (J+ell) cap q rho N i Vb mu x seen F
end Green64Analytic.CorrelationSquare

end

end

