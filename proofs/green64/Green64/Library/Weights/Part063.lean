module

public import Green64.Library.Weights.ActualMultigroupReturnG
public import Green64.Library.Correlation.Part030
public import Green64.Library.Correlation.Part031

@[expose] public section

/-!
# Weights / Part063

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalReachableMultigroupReturnG -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))

/-- Reachability supplies all return-state encodings simultaneously.
The encodings are chosen BEFORE q, V, mu and the arbitrary continuation. -/
theorem source_original_REACHABLE_MULTIGROUP_G_return_matrix434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (hi : ∀ g,Function.Injective (bm g)) (shift : ℤ) :
    ∃ s : (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g),
      (∀ g p,p ∉ background g → s g p=.retired) ∧
      (∀ g,sourceOriginalPrimeProductPending434 (bm g) shift (s g) =
        ((y.2 g).2).filter (fun z => z.1 ∈ background g)) ∧
      (∀ g,(seen \ (background g).image (bm g)) ∪
        (sourceOriginalPrimeProductSeen434 (bm g) (s g) ∩ background g).image (bm g)=seen) ∧
      ∀ (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
        (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ),
        sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm M background y
          q 1 N i V mu seen F =
        sourceOriginalMultigroupBackgroundReturnG434 SP sm BP bm M background y
          shift s q N i V mu seen F := by
  have h := fun g => source_original_REACHABLE_background_encoding434
    SP sm BP bm M y seen hy g (background g) shift
  choose s hs hp hseen using h
  refine ⟨s,hs,hp,hseen,?_⟩
  intro q N i V mu F
  rw [source_original_PHYSICAL_G_separate_operators434]
  exact source_original_ACTUAL_MULTIGROUP_G_return_matrix434
    SP sm BP bm M background y seen hi shift s hs hp hseen q N i V mu F

/-- The literal original physical marked G has the all-group signed
return-matrix formula. No assumed reduced-state representability, norm
bound, independence of F, or birth-gate weakening occurs. -/
theorem source_original_PHYSICAL_MARKED_G_background_return_matrix434
    (cap : BG → ℕ) (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g) (shift : ℤ) :
    ∃ s : (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g),
      (∀ g p,p ∉ background g → s g p=.retired) ∧
      (∀ g,sourceOriginalPrimeProductPending434 (bm g) shift (s g) =
        (((physicalFockProjection SP sm BP bm M cap x).2 g).2).filter
          (fun z => z.1 ∈ background g)) ∧
      (∀ g,(seen \ (background g).image (bm g)) ∪
        (sourceOriginalPrimeProductSeen434 (bm g) (s g) ∩ background g).image (bm g)=seen) ∧
      ∀ (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
        (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ),
        physicalGBirthMarkedRow SP sm BP bm M cap q 1 N i V mu x seen F =
        sourceOriginalMultigroupBackgroundReturnG434 SP sm BP bm M background
          (physicalFockProjection SP sm BP bm M cap x) shift s q N i V mu seen F := by
  have hlocal : ∀ g,Function.Injective (bm g) := by
    intro g p r h
    have he : (⟨g,p⟩ : Sigma BP)=⟨g,r⟩ := hi h
    exact eq_of_heq (Sigma.mk.inj he).2
  obtain ⟨s,hs,hp,hseen,hr⟩ := source_original_REACHABLE_MULTIGROUP_G_return_matrix434
    SP sm BP bm M background (physicalFockProjection SP sm BP bm M cap x)
    seen hx hlocal shift
  refine ⟨s,hs,hp,hseen,?_⟩
  intro q N i V mu F
  rw [source_original_PHYSICAL_MARKED_G_background_split434
    SP sm BP bm M background cap hi q 1 N i V mu x seen hx hcap F,
    source_original_PHYSICAL_G_background_seen_row434 SP sm BP bm M background _ hi]
  exact hr q N i V mu F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualMultigroupBirthGauge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- Global numerical injectivity makes the actual all-group numerical
birth count equal the sum of the labelled group counts. -/
theorem source_original_NUMERIC_BACKGROUND_card434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (born : (g : BG) → Finset (BP g)) :
    (sourceOriginalNumericBackground434 BP bm born).card = ∑ g,(born g).card := by
  have he : sourceOriginalNumericBackground434 BP bm born =
      (Finset.univ.sigma born).image (fun x : Sigma BP => bm x.1 x.2) := by
    ext n
    constructor
    · intro hn
      obtain ⟨g,hg,himg⟩ := Finset.mem_biUnion.mp hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp himg
      exact Finset.mem_image.mpr ⟨⟨g,p⟩,Finset.mem_sigma.mpr ⟨Finset.mem_univ g,hp⟩,rfl⟩
    · intro hn
      obtain ⟨⟨g,p⟩,hp,rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ g,
        Finset.mem_image_of_mem (bm g) (Finset.mem_sigma.mp hp).2⟩
  rw [he,Finset.card_image_of_injective _ hi,Finset.card_sigma]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- One true G witness increments background numerical seen by exactly
its fresh background births. Active births cannot change this counter. -/
theorem source_original_ACTUAL_G_background_birth_count434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y)
    (ha : ∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen ∩ B) :
    ((seen ∪ (sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1) ∪
      sourceOriginalNumericBackground434 BP bm (fun g => (b g).2.1))) ∩ B).card =
      (seen ∩ B).card + ∑ g,(a g).2.1.card := by
  have hd : Disjoint (seen ∩ B)
      (sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hb
    obtain ⟨g,hg,himg⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp himg
    exact ha g p hp hn
  rw [source_original_PHYSICAL_G_updated_background_seen434
    SP sm BP bm M background y hi seen a b,Finset.card_union_of_disjoint hd,
    source_original_NUMERIC_BACKGROUND_card434 BP bm hi]

/-- The actual all-group background coefficient gets one factor u per
birth; retention and deletion weights, including rho, are untouched. -/
theorem source_original_ACTUAL_BACKGROUND_coefficient_birth_tilt434
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y) :
    sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y
      q rho N i V (fun g p => u*mu g p) a =
    (u:ℂ)^(∑ g,(a g).2.1.card) *
      sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y
        q rho N i V mu a := by
  unfold sourceOriginalGhostBackgroundCoefficient434
    sourceOriginalGroupPrimeBirthWeight434 sourceOriginalRestrictedPrimeBirthLift434
  simp only [Complex.ofReal_mul,Finset.prod_mul_distrib,Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (a g).2.1.card) (u:ℂ)]
  ring

/-- Only the background G birth weights are tilted. The active G and
the entire original joint observable keep their original coefficients. -/
def sourceOriginalActualBackgroundBirthTiltG434
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    if ((∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen ∩ B) ∧
        (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)) then
      (sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y
        q rho N i V (fun g p => u*mu g p) ab.1 *
       sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y
        q rho N i V mu ab.2) *
      F (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y ab.1 ab.2)
        (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1)) ∪
          ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))
    else 0

/-- Exact numerical birth-counter conjugation for the FULL G row.
This is an identity for arbitrary real u, not a norm estimate or a
per-visit cost. The original no-rebirth gates are essential. -/
theorem source_original_ACTUAL_G_background_birth_gauge434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    (u:ℂ)^(seen ∩ B).card *
      sourceOriginalActualBackgroundBirthTiltG434 BP bm SP sm M background y
        q rho u N i V mu seen F =
    sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm M background y q rho N i V mu seen
      (fun out st => (u:ℂ)^(st ∩ B).card * F out st) := by
  unfold sourceOriginalActualBackgroundBirthTiltG434 sourceOriginalGhostBackgroundSeenRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hg : (∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen ∩ B) ∧
      (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)
  · rw [if_pos hg,if_pos hg]
    dsimp only
    have hu :
        (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1)) ∪
          ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1))) =
        seen ∪ (sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1) ∪
          sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)) := by
      ext n
      simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    rw [source_original_ACTUAL_BACKGROUND_coefficient_birth_tilt434 BP bm SP sm M background y,
      hu,source_original_ACTUAL_G_background_birth_count434 BP bm SP sm M background y
        hi seen ab.1 ab.2 hg.1,pow_add]
    ring
  · rw [if_neg hg,if_neg hg,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBackgroundBirthGauge -/

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
variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- Literal branching mixed chain, tilting ONLY background G births.
All E and active G coefficients remain the original ones. -/
def sourceOriginalBirthTiltedBackgroundChain434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,start,_,F => fun y seen =>
      sourceOriginalActualBackgroundBirthTiltG434 BP bm SP sm (J+ell) background y
        q 1 u N start V mu seen F
  | n+1,(r,h),start,sk,F => fun y seen =>
      sourceOriginalActualBackgroundBirthTiltG434 BP bm SP sm (J+ell) background y
        q 1 u N start V mu seen (fun yg sg =>
          let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
            (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
          sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k z (sg \ B) r
            (fun out s =>
              sourceOriginalBirthTiltedBackgroundChain434 q u Vs V mu K zeta theta k N n h
                (start+1) (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r) F
                (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
                  (sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns sk r
                    (physicalAlternatingSign start) k) out) (s ∪ (sg ∩ B))))

/-- Exact transport of the total background-birth mark through the
complete mixed G/E chain of an actual avoiding frame history. No
prescribed external-seen schedule is substituted for the branching chain. -/
theorem source_original_MEMORY_history_background_birth_gauge434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    (u:ℂ)^(seen ∩ B).card *
      sourceOriginalBirthTiltedBackgroundChain434 SP sm BP bm J ell m cap patterns background
        q u Vs V mu K zeta theta k N n h start sk F y seen =
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk
      (fun out st => (u:ℂ)^(st ∩ B).card * F out st) y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      exact source_original_ACTUAL_G_background_birth_gauge434
        BP bm SP sm (J+ell) background y hi q 1 u N start V mu seen F
  | succ n ih =>
      rcases h with ⟨r,h⟩
      rw [sourceOriginalBirthTiltedBackgroundChain434,
        sourceOriginalSeenSeparatedBackgroundChain434]
      dsimp only
      rw [source_original_ACTUAL_G_background_birth_gauge434
        BP bm SP sm (J+ell) background y hi]
      apply congrArg (sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm (J+ell)
        background y q 1 N start V mu seen)
      funext yg sg
      let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
        (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
      let H := fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) =>
        sourceOriginalBirthTiltedBackgroundChain434 SP sm BP bm J ell m cap patterns background
          q u Vs V mu K zeta theta k N n h (start+1)
          (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r) F
          (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
            (sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns sk r
              (physicalAlternatingSign start) k) out) (st ∪ (sg ∩ B))
      have hc : ((sg \ B) ∪ (sg ∩ B)) ∩ B = sg ∩ B := by
        ext p
        simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
        tauto
      have he := source_original_SOURCE_E_frame_background_counter_row434
        SP sm BP bm J ell m cap patterns hi background
        q 1 u Vs V mu
        (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
        zeta theta z (sg \ B) (sg ∩ B) r (physicalAlternatingSign start) k havoid.1 H
      rw [hc] at he
      rw [he]
      unfold sourceOriginalSourceEFrameFibreRow434
      apply Finset.sum_congr rfl
      intro f hf
      dsimp only [H]
      congr 1
      exact ih h havoid.2 (start+1) _ _ _

/-- Empty initial background seen removes the initial gauge factor.
The terminal mark is still present and is not identified with an
arithmetic parity observable. -/
theorem source_original_MEMORY_history_background_birth_terminal434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hzero : seen ∩ B=∅) :
    sourceOriginalBirthTiltedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk F y seen =
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk
      (fun out st => (u:ℂ)^(st ∩ B).card * F out st) y seen := by
  have hh := source_original_MEMORY_history_background_birth_gauge434
    SP sm BP bm J ell m cap patterns background hi q u Vs V mu K zeta theta k N
    F n h havoid start sk y seen
  simpa only [hzero,Finset.card_empty,pow_zero,one_mul] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBackgroundBirthRoot -/

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

def sourceOriginalBirthTiltedBackgroundMemoryRoot434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalBirthTiltedBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q u Vs V mu K zeta theta k N N h 0
            (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
            (fun out _ => physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

def sourceOriginalBackgroundBirthMarkedMemoryRoot434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q Vs V mu K zeta theta k N N h 0
            (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
            (fun out st =>
              (u:ℂ)^(st ∩ sourceOriginalNumericBackground434 BP bm
                (fun g => Finset.univ \
                  sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)).card *
                physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- The genuine history-selected background birth generating root is
the original branching chain with its numerical terminal birth mark.
The actual baseline, orbit mass, initial distinctness, phases, both
integer outputs and endpoint data all stay inside the same sums. -/
theorem source_original_MEMORY_background_birth_root_gauge434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    sourceOriginalBirthTiltedBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R =
    sourceOriginalBackgroundBirthMarkedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  unfold sourceOriginalBirthTiltedBackgroundMemoryRoot434
    sourceOriginalBackgroundBirthMarkedMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · rw [hv,star_zero,mul_zero,zero_mul,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      have hzero := Finset.disjoint_iff_inter_eq_empty.mp
        (source_original_MEMORY_history_background_initial_empty434
          SP sm BP bm J ell m patterns hi y hv (2*R) h).2
      exact source_original_MEMORY_history_background_birth_terminal434
        SP sm BP bm J ell m cap patterns
        (fun g => Finset.univ \
          sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y (2*R) h g)
        hi q u Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R)
        (fun out _ => physicalVacuum SP sm BP bm J ell out)
        (2*R) h
        (source_original_FULL_ACTIVE_HISTORY_complement_avoids434
          SP sm BP bm J ell m patterns y (2*R) h)
        0 (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
        y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset hzero
    · simp only [if_neg hn]

/-- At u=1 the new generating root is literally the original source
root, for the original source domain and any admissible nonzero rho.
No analytic smallness or arithmetic parity identification is asserted. -/
theorem source_original_MEMORY_background_birth_root_one434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    sourceOriginalBirthTiltedBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q 1 Vs V K zeta theta k R =
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R := by
  rw [source_original_MEMORY_background_birth_root_gauge434
    SP sm BP bm J ell m cap patterns hd.big_injective,
    source_original_MEMORY_root_seen_separated_source_domain434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R hd]
  unfold sourceOriginalBackgroundBirthMarkedMemoryRoot434
    sourceOriginalSeenSeparatedBackgroundMemoryRoot434
  simp only [Complex.ofReal_one,one_pow,one_mul]
end Green64Analytic.CorrelationSquare

end

end

