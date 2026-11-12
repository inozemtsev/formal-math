module

public import Green64.Library.Weights.SourceEBackgroundOperator
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.PhysicalGhostBackgroundSplit
public import Green64.Library.Weights.Part029
public import Green64.Library.Correlation.PhysicalEBackgroundBirthGate

@[expose] public section

/-!
# Correlation / Part030

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryFixedFrames -/

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

theorem source_original_G_unseen_terminal_sum434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    {I : Type} [Fintype I]
    (F : I → FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N i V mu y seen
      (fun out s => ∑ t,F t out s) =
    ∑ t,sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (F t) := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
  · simp only [if_pos h,Finset.mul_sum]
  · simp only [if_neg h,Finset.sum_const_zero]

theorem source_original_E_fibre_terminal_sum434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    {I : Type} [Fintype I]
    (F : I → FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r (fun out s => ∑ t,F t out s) =
    ∑ t,sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r (F t) := by
  unfold sourceOriginalSourceEFrameFibreRow434
  dsimp only
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- A full sequence of original E frames. Its carrier is independent
of every intervening OLD state, seen set and G choice. -/
def SourceOriginalSourceFrameHistory434 : ℕ → Type
  | 0 => PUnit
  | n+1 => SourceOriginalSourceEFrame434 SP sm BP J ell m patterns ×
      SourceOriginalSourceFrameHistory434 n

noncomputable instance (n : ℕ) :
    Fintype (SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) := by
  induction n with
  | zero => change Fintype PUnit;infer_instance
  | succ n ih =>
      letI := ih
      change Fintype (SourceOriginalSourceEFrame434 SP sm BP J ell m patterns ×
        SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
      infer_instance

def sourceOriginalFixedFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen F
  | n+1,(r,h),start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
            (sourceOriginalFixedFrameGEChain434 q rho Vs V mu K zeta theta k N n h (start+1) F))

/-- Exact temporal expansion of the original canonical G/E chain over
whole E-frame histories. Finite linearity moves only the frame sum;
all G choices, OLD outputs, global births and joint coefficients stay. -/
theorem source_original_MEMORY_prime_chain_fixed_frames434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalPrimeBirthGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N n start F y seen =
    ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
      sourceOriginalFixedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N n h start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      letI : Unique (SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns 0) :=
        inferInstanceAs (Unique PUnit)
      rw [Fintype.sum_unique]
      rfl
  | succ n ih =>
      change _ = ∑ h : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns ×
        SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
        sourceOriginalFixedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N (n+1) h start F y seen
      rw [Fintype.sum_prod_type]
      rw [sourceOriginalPrimeBirthGEChain434]
      simp only [sourceOriginalFixedFrameGEChain434]
      have ihf :
          sourceOriginalPrimeBirthGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N n (start+1) F =
          fun out s => ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
            sourceOriginalFixedFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N n h (start+1) F out s := by
        funext out s
        exact ih (start+1) out s
      rw [ihf]
      simp_rw [source_original_SOURCE_MARKED_E_fibre_frames434,
        source_original_E_fibre_terminal_sum434]
      rw [source_original_G_unseen_terminal_sum434]
      apply Finset.sum_congr rfl
      intro r hr
      rw [source_original_G_unseen_terminal_sum434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFixedFrameRoot -/

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


def sourceOriginalFixedFrameMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalFixedFrameGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N N h 0
            (fun out _ => physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- The whole original root is a finite sum over complete original
E-frame histories, inside its literal outer Fock/vacuum measure. -/
theorem source_original_MEMORY_root_fixed_frames434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalFixedFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  rw [source_original_MEMORY_root_prime_birth_exact434 SP sm BP bm J ell m cap patterns
    hi hcap q rho Vs V K zeta theta k R hVs hmu]
  unfold sourceOriginalPrimeBirthMemoryRoot434 sourceOriginalFixedFrameMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    rw [source_original_MEMORY_prime_chain_fixed_frames434]
  · simp only [if_neg hn]

/-- Applicable source-domain identity at rho=1, with no new
reachability, bounded-continuation or analytic smallness premise. -/
theorem source_original_MEMORY_root_fixed_frames_rho_one434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalFixedFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q 1 Vs V K zeta theta k R := by
  rw [source_original_memory_SOURCE_ROOT_rho_invariant434
    SP sm BP bm J ell m cap patterns q rho (ne_of_gt hd.rho_pos) Vs V K zeta theta k R]
  exact source_original_MEMORY_root_fixed_frames434 SP sm BP bm J ell m cap patterns
    hd.big_injective hd.cap_saturated q 1 Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFrameHistoryPool -/

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


def sourceOriginalFrameTargetPool434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (g : BG) : Finset (BP g) :=
  Finset.univ.image (r.2.2.1.2.2.1 g).1

def sourceOriginalFrameHistoryPool434 :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
      (g : BG) → Finset (BP g)
  | 0,_,_ => ∅
  | n+1,(r,h),g => sourceOriginalFrameTargetPool434 SP sm BP J ell m patterns r g ∪
      sourceOriginalFrameHistoryPool434 n h g

def sourceOriginalFrameHistoryAvoids434
    (background : (g : BG) → Finset (BP g)) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n → Prop
  | 0,_ => True
  | n+1,(r,h) => (∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g) ∧
      sourceOriginalFrameHistoryAvoids434 background n h

theorem source_original_FRAME_HISTORY_pool_card434
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) (g : BG) :
    (sourceOriginalFrameHistoryPool434 SP sm BP J ell m patterns n h g).card ≤ n*(J+ell) := by
  induction n with
  | zero => simp [sourceOriginalFrameHistoryPool434]
  | succ n ih =>
      rcases h with ⟨r,h⟩
      have ht : (sourceOriginalFrameTargetPool434 SP sm BP J ell m patterns r g).card ≤ J+ell := by
        exact (Finset.card_image_le).trans (by simp)
      exact (Finset.card_union_le _ _).trans
        (by simpa only [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add ht (ih h))

theorem source_original_FRAME_HISTORY_pool_avoids434
    (background : (g : BG) → Finset (BP g))
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (hd : ∀ g,Disjoint (background g) (sourceOriginalFrameHistoryPool434 SP sm BP J ell m patterns n h g)) :
    sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rcases h with ⟨r,h⟩
      refine ⟨?_,ih h ?_⟩
      · intro g j hj
        exact Finset.disjoint_left.mp (hd g) hj (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
      · intro g
        exact (hd g).mono_right (Finset.subset_union_right)

def sourceOriginalFullActiveHistoryPool434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) (g : BG) :
    Finset (BP g) :=
  (Finset.univ.image (y.2 g).1) ∪
    sourceOriginalFrameHistoryPool434 SP sm BP J ell m patterns n h g

theorem source_original_FULL_ACTIVE_HISTORY_pool_card434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) (g : BG) :
    (sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y n h g).card ≤
      (n+1)*(J+ell) := by
  have hi : (Finset.univ.image (y.2 g).1).card ≤ J+ell :=
    (Finset.card_image_le).trans (by simp)
  exact (Finset.card_union_le _ _).trans
    (by simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using
      Nat.add_le_add hi (source_original_FRAME_HISTORY_pool_card434 SP sm BP J ell m patterns n h g))

theorem source_original_FULL_ACTIVE_HISTORY_complement_avoids434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) :
    sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns
      (fun g => Finset.univ \ sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y n h g)
      n h := by
  apply source_original_FRAME_HISTORY_pool_avoids434
  intro g
  apply Finset.disjoint_left.mpr
  intro p hp hh
  exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_right _ hh)

theorem source_original_FULL_ACTIVE_HISTORY_initial_avoids434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) :
    sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell
      (fun g => Finset.univ \ sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y n h g) y := by
  intro g j hj
  exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEBackgroundReachable -/

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

theorem source_original_G_unseen_reachable_congr434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (F G : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (hFG : ∀ out s,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out s →
      F out s=G out s) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen G := by
  rw [←source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434
    SP sm BP bm cap J ell hi q rho N i Vs V mu hVs hmu y seen hy hcap,
    ←source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434
    SP sm BP bm cap J ell hi q rho N i Vs V mu hVs hmu y seen hy hcap]
  exact source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
    q rho N i Vs V mu y seen hy F G hFG

variable (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
variable (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)

local notation "X" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
local notation "Y" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
  (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background y)
local notation "E" => sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm
  (J+ell) cap hcap background y seen hy


include hcap hy in
theorem source_original_SOURCE_E_background_frame_reachable434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r)
    (hf : sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns Y seen o k r f) :
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background y
        (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
          r.2.2.1.1 r.2.2.2.1 o k)
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns Y o k
          (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f)))
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f)).toFinset) := by
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap X) seen := by
    rw [source_original_REACHABLE_canonical_projection434 SP sm BP bm (J+ell) cap hcap y seen hy]
    exact hy
  have hf' := (source_original_SOURCE_E_background_frame_admissible434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k f).mp hf
  have hh := source_original_SOURCE_ORIENTED_E_reachable434 SP sm BP bm cap J ell m patterns
    X seen o k
    (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
      (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r f)) hx hf'.1 hf'.2
  rw [source_original_SOURCE_E_background_frame_output434,
    source_original_SOURCE_E_background_frame_births434] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryTemporalBackground -/

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

/-- The original time order with G split into its actual two prime
pools and E performed on the retained OLD state. Each E frame's
translated background is reattached inside the joint continuation. -/
def sourceOriginalFixedFrameBackgroundChain434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,start,F => fun y seen =>
      sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen F
  | n+1,(r,h),start,F => fun y seen =>
      sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen (fun yg sg =>
          let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg
          let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
            (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
          sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k z sg r
            (fun out s =>
              sourceOriginalFixedFrameBackgroundChain434 q Vs V mu K zeta theta k N n h
                (start+1) F
                (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
                  (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 x
                    r.2.2.1.1 r.2.2.2.1 (physicalAlternatingSign start) k) out) s))

/-- Exact temporal transfer through every original G/E step on a
fixed complete E-frame history. This is a chain identity, not a
background norm bound or an assumed bound for the continuation. -/
theorem source_original_MEMORY_fixed_history_background_transfer434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    sourceOriginalFixedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta k N n h start F y seen =
    sourceOriginalFixedFrameBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_PHYSICAL_G_background_split_row434
        SP sm BP bm (J+ell) background y q 1 N start V mu seen F
  | succ n ih =>
      rcases h with ⟨r,h⟩
      rw [sourceOriginalFixedFrameGEChain434,sourceOriginalFixedFrameBackgroundChain434]
      dsimp only
      rw [←source_original_PHYSICAL_G_background_split_row434]
      apply source_original_G_unseen_reachable_congr434 SP sm BP bm J ell cap hi hcap
        q 1 N start Vs V mu hVs hmu y seen hy
      intro yg sg hg
      rw [source_original_SOURCE_E_background_frame_row434 SP sm BP bm J ell m cap patterns
        hcap background yg sg hg q Vs V mu
        (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
        zeta theta r (physicalAlternatingSign start) k havoid.1]
      unfold sourceOriginalSourceEFrameFibreRow434
      apply Finset.sum_congr rfl
      intro f hf
      dsimp only
      congr 1
      exact ih h havoid.2 (start+1) _ _
        (source_original_SOURCE_E_background_frame_reachable434
          SP sm BP bm J ell m cap patterns hcap background yg sg hg r
          (physicalAlternatingSign start) k f.1 f.2)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryTemporalBackgroundRoot -/

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

/-- Every complete original E-frame history chooses its own background:
the complement of its initial and future BIG active prime labels.
The whole original vacuum and Fock measure is retained. -/
def sourceOriginalTemporalBackgroundMemoryRoot434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalFixedFrameBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q Vs V mu K zeta theta k N N h 0
            (fun out _ => physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Exact full-source temporal background transfer under the original
source-domain hypotheses only. No smallness of the joint continuation
or history sum is assumed. The background is chosen inside each
literal complete-history summand. -/
theorem source_original_MEMORY_root_temporal_background_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalTemporalBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q Vs V K zeta theta k R := by
  rw [source_original_MEMORY_root_fixed_frames_rho_one434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R hd]
  unfold sourceOriginalFixedFrameMemoryRoot434 sourceOriginalTemporalBackgroundMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y = 0
  · simp [hv]
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    exact source_original_MEMORY_fixed_history_background_transfer434
      SP sm BP bm J ell m cap patterns
      (fun g => Finset.univ \
        sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y (2*R) h g)
      hd.big_injective hd.cap_saturated q Vs V
      (physicalSourceMuTilde BP bm q (2*R) V) hd.Vsmall_pos
      (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
        hd.Vbig_pos hd.big_above_visits)
      K zeta theta k (2*R)
      (fun out _ => physicalVacuum SP sm BP bm J ell out)
      (2*R) h
      (source_original_FULL_ACTIVE_HISTORY_complement_avoids434
        SP sm BP bm J ell m patterns y (2*R) h)
      0 y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      (source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn)
  · simp only [if_neg hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryHistoryOldTail -/

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
variable (M : ℕ)

/-- A reachable source state has at most one pending atom per prime
of any chosen pool, including primes with different residues. -/
theorem source_original_REACHABLE_pending_pool_card434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (g : BG) (pool : Finset (BP g)) :
    ((y.2 g).2.filter (fun a => a.1 ∈ pool)).card ≤ pool.card := by
  let s := (y.2 g).2.filter (fun a => a.1 ∈ pool)
  have hl : s.map (fun z => bm g z.1) ≤
      sourceOriginalPhysicalInventory434 SP sm BP bm M y := by
    apply le_trans (Multiset.map_le_map (Multiset.filter_le _ _))
    apply le_trans (b := sourceOriginalBigInventory434 (bm g) M
      (y.2 g).1 (y.2 g).2) le_add_self
    have hh := Finset.sum_le_sum_of_subset
      (f := fun h : BG => sourceOriginalBigInventory434 (bm h) M
        (y.2 h).1 (y.2 h).2)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ g))
    simpa only [Finset.sum_singleton,sourceOriginalPhysicalInventory434] using hh
  have hn : (s.toList.map (fun z => bm g z.1)).Nodup := by
    change (↑(s.toList.map (fun z => bm g z.1)) : Multiset ℕ).Nodup
    rw [←Multiset.map_coe,Multiset.coe_toList]
    exact Multiset.nodup_of_le hl hy.1
  have hp : (s.toList.map (fun z => z.1)).Nodup := by
    apply List.Nodup.of_map (bm g)
    simpa only [List.map_map,Function.comp_def] using hn
  have hs : (s.toList.map (fun z => z.1)).toFinset ⊆ pool := by
    intro p h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have ha' : a ∈ s := by simpa only [Multiset.mem_toList] using ha
    exact (Multiset.mem_filter.mp ha').2
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hp] at hc
  simpa only [List.length_map,Multiset.length_toList] using hc

/-- Exact partition followed only by the reachable prime-pool bound. -/
theorem source_original_REACHABLE_pending_pool_partition434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (pool : (g : BG) → Finset (BP g)) :
    (∑ g,(y.2 g).2.card) ≤
      (∑ g,((y.2 g).2.filter (fun a => a.1 ∉ pool g)).card) + ∑ g,(pool g).card := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g hg
  have hc := source_original_REACHABLE_pending_pool_card434 SP sm BP bm M y seen hy g (pool g)
  have he := congrArg Multiset.card
    (Multiset.filter_add_not (fun a : Atom (BP g) (bm g) => a.1 ∈ pool g) (y.2 g).2)
  rw [Multiset.card_add] at he
  omega

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The non-background OLD population at any reachable state is bounded
by the initial and future active labels of the fixed whole history. -/
theorem source_original_MEMORY_history_OLD_background_bound434
    (initial y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) :
    (∑ g,(y.2 g).2.card) ≤
      (∑ g,((y.2 g).2.filter (fun a =>
        a.1 ∉ sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h g)).card) +
      Fintype.card BG * ((n+1)*(J+ell)) := by
  have hp := source_original_REACHABLE_pending_pool_partition434 SP sm BP bm (J+ell)
    y seen hy (sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h)
  apply hp.trans
  apply Nat.add_le_add_left
  calc
    (∑ g,(sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h g).card)
      ≤ ∑ _g : BG,(n+1)*(J+ell) := by
        apply Finset.sum_le_sum
        intro g hg
        exact source_original_FULL_ACTIVE_HISTORY_pool_card434 SP sm BP bm J ell m patterns initial n h g
    _ = Fintype.card BG * ((n+1)*(J+ell)) := by simp

/-- A large actual OLD population forces a large background population
with an explicit finite active-history allowance. This is an event
inclusion, not a tail-probability or operator-norm estimate. -/
theorem source_original_MEMORY_history_OLD_tail_implies_background434
    (initial y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (H : ℕ)
    (ht : H + Fintype.card BG * ((n+1)*(J+ell)) < ∑ g,(y.2 g).2.card) :
    H < ∑ g,((y.2 g).2.filter (fun a =>
      a.1 ∉ sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h g)).card := by
  have hb := source_original_MEMORY_history_OLD_background_bound434 SP sm BP bm J ell m patterns
    initial y seen hy n h
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEFrameSeenSplit -/

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

def sourceOriginalNumericBackground434
    (background : (g : BG) → Finset (BP g)) : Finset ℕ :=
  Finset.univ.biUnion (fun g => (background g).image (bm g))

theorem source_original_NUMERIC_BACKGROUND_mem434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (background : (g : BG) → Finset (BP g)) (g : BG) (p : BP g) :
    bm g p ∈ sourceOriginalNumericBackground434 BP bm background ↔ p ∈ background g := by
  constructor
  · intro h
    obtain ⟨g',hg',hp'⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p',hp',he⟩ := Finset.mem_image.mp hp'
    have hs : (⟨g',p'⟩ : Sigma BP) = ⟨g,p⟩ := hi he
    exact Eq.mp (congrArg (fun x : Sigma BP => x.2 ∈ background x.1) hs) hp'
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background
include hi

/-- The actual frame admissibility predicate depends only on the
non-background part of seen when every target label avoids background.
Global numerical injectivity handles interactions across all groups. -/
theorem source_original_SOURCE_E_frame_background_seen434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) :
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f ↔
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x (seen \ B) o k r f := by
  let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f
  have ht : ∀ g j,bm g ((z.2.2.1.bigChoice g).1 j) ∉ B := by
    intro g j hj
    exact htarget g j ((source_original_NUMERIC_BACKGROUND_mem434 BP bm hi background g _).mp hj)
  have he := source_original_SOURCE_E_background_seen_gate434 SP sm BP bm J ell m cap patterns
    x z B (seen \ B) (seen ∩ B) ht Finset.inter_subset_right
  have hs : (seen \ B) ∪ (seen ∩ B) = seen := by
    ext p
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hs] at he
  unfold sourceOriginalSourceEFrameAdmissible434
  exact and_congr_right (fun _ => he)

/-- The background part of seen is absent from the actual E gate but
is reinserted in the arbitrary joint terminal observation. The full
original coefficient, phases and outputs are unchanged. -/
theorem source_original_SOURCE_E_frame_background_seen_row434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r F =
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x (seen \ B) r
      (fun out s => F out (s ∪ (seen ∩ B))) := by
  let e : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f} ≃
      {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x (seen \ B) o k r f} :=
    { toFun := fun f => ⟨f.1,(source_original_SOURCE_E_frame_background_seen434
        SP sm BP bm J ell m cap patterns hi background x seen r o k htarget f.1).mp f.2⟩
      invFun := fun f => ⟨f.1,(source_original_SOURCE_E_frame_background_seen434
        SP sm BP bm J ell m cap patterns hi background x seen r o k htarget f.1).mpr f.2⟩
      left_inv := by intro f;rfl
      right_inv := by intro f;rfl }
  unfold sourceOriginalSourceEFrameFibreRow434
  apply Fintype.sum_equiv e
  intro f
  dsimp only [e]
  have hu (births : Finset ℕ) :
      ((seen \ B) ∪ births) ∪ (seen ∩ B) = seen ∪ births := by
    ext p
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hu]
  all_goals rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryHistorySchedule -/

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

/-- The actual SMALL state and BIG active labels, with pending emptied. -/
def sourceOriginalPhysicalActiveSkeleton434
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    FullPhysicalOutput SP sm BP bm (J+ell) :=
  (y.1,fun g => ((y.2 g).1,0))

/-- The next active skeleton is literally the target data of the frame. -/
def sourceOriginalFrameTargetSkeleton434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) :
    FullPhysicalOutput SP sm BP bm (J+ell) :=
  (r.2.2.1.2.2.2,fun g => ((r.2.2.1.2.2.1 g).1,0))

def sourceOriginalActiveFrameStep434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ) : ℤ :=
  sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y)
    r.2.2.1.1 r.2.2.2.1 o k

theorem source_original_ACTIVE_FRAME_step_skeleton434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ) :
    sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns y r o k =
    sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns
      (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y) r o k := rfl

theorem source_original_SOURCE_E_frame_target_skeleton434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) :
    sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f)) =
    sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r := rfl

/-- A deterministic list of ALL literal E shifts, computed from the
initial active skeleton and the complete frame history. -/
def sourceOriginalFrameHistorySteps434 (k : ℤ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    ℕ → FullPhysicalOutput SP sm BP bm (J+ell) → List ℤ
  | 0,_,_,_ => []
  | n+1,(r,h),start,y =>
      sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns y r
        (physicalAlternatingSign start) k ::
      sourceOriginalFrameHistorySteps434 k n h (start+1)
        (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r)

theorem source_original_FRAME_HISTORY_steps_length434
    (k : ℤ) (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    (sourceOriginalFrameHistorySteps434 SP sm BP bm J ell m cap patterns k n h start y).length = n := by
  induction n generalizing start y with
  | zero => rfl
  | succ n ih =>
      rcases h with ⟨r,h⟩
      simp only [sourceOriginalFrameHistorySteps434,List.length_cons,ih]

variable (background : (g : BG) → Finset (BP g))

/-- The same actual temporal chain, with each background translation
computed from the fixed active skeleton, independent of every G choice. -/
def sourceOriginalScheduledBackgroundChain434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,start,_,F => fun y seen =>
      sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen F
  | n+1,(r,h),start,sk,F => fun y seen =>
      sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen (fun yg sg =>
          let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
            (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
          sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k z sg r
            (fun out s =>
              sourceOriginalScheduledBackgroundChain434 q Vs V mu K zeta theta k N n h
                (start+1) (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r) F
                (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
                  (sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns sk r
                    (physicalAlternatingSign start) k) out) s))

/-- Actual temporal identity; neither independence of shifts from
background paths nor any norm estimate is assumed. -/
theorem source_original_MEMORY_background_schedule434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalFixedFrameBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start F y seen =
    sourceOriginalScheduledBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start
      (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y) F y seen := by
  induction n generalizing start y seen with
  | zero => rfl
  | succ n ih =>
      rcases h with ⟨r,h⟩
      rw [sourceOriginalFixedFrameBackgroundChain434,sourceOriginalScheduledBackgroundChain434]
      dsimp only
      unfold sourceOriginalPhysicalGhostBackgroundSplitRow434
      apply Finset.sum_congr rfl
      intro ab hab
      split_ifs
      · congr 1
        unfold sourceOriginalSourceEFrameFibreRow434
        apply Finset.sum_congr rfl
        intro f hf
        dsimp only
        congr 1
        rw [ih]
        rfl
      · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryScheduledBackgroundRoot -/

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

def sourceOriginalScheduledBackgroundMemoryRoot434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalScheduledBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q Vs V mu K zeta theta k N N h 0
            (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
            (fun out _ => physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- The actual full root has a predetermined background shift schedule
inside each complete-history summand, with no new analytic premise. -/
theorem source_original_MEMORY_root_scheduled_background_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalScheduledBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q Vs V K zeta theta k R := by
  rw [source_original_MEMORY_root_temporal_background_source_domain434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R hd]
  unfold sourceOriginalTemporalBackgroundMemoryRoot434 sourceOriginalScheduledBackgroundMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    exact source_original_MEMORY_background_schedule434 SP sm BP bm J ell m cap patterns
      _ q Vs V _ K zeta theta k (2*R) _ (2*R) h 0 y _
  · simp only [if_neg hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostSeenSplit -/

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
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)
local notation "B" => sourceOriginalNumericBackground434 BP bm background

def sourceOriginalGhostBackgroundSeenRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    if ((∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen ∩ B) ∧
        (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)) then
      (sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu ab.1 *
        sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2) *
      F (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y ab.1 ab.2)
        (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1)) ∪
          ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))
    else 0

variable (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
include hi

theorem source_original_PHYSICAL_G_background_birth_mem434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (g : BG) (p : BP g) (hp : p ∈ (a g).2.1) :
    bm g p ∈ B := by
  apply (source_original_NUMERIC_BACKGROUND_mem434 BP bm hi background g p).mpr
  exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp)).2

theorem source_original_PHYSICAL_G_active_birth_not_mem434
    (a : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y)
    (g : BG) (p : BP g) (hp : p ∈ (a g).2.1) :
    bm g p ∉ B := by
  intro h
  exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp)).2
    ((source_original_NUMERIC_BACKGROUND_mem434 BP bm hi background g p).mp h)

theorem source_original_PHYSICAL_G_separate_seen_gates434
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    ((∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen) ∧
      (∀ g,∀ p ∈ (b g).2.1,bm g p ∉ seen)) ↔
    ((∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen ∩ B) ∧
      (∀ g,∀ p ∈ (b g).2.1,bm g p ∉ seen \ B)) := by
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨fun g p hp hn => ha g p hp (Finset.mem_inter.mp hn).1,
      fun g p hp hn => hb g p hp (Finset.mem_sdiff.mp hn).1⟩
  · rintro ⟨ha,hb⟩
    refine ⟨?_,?_⟩
    · intro g p hp hs
      exact ha g p hp (Finset.mem_inter.mpr ⟨hs,
        source_original_PHYSICAL_G_background_birth_mem434 SP sm BP bm M background y hi a g p hp⟩)
    · intro g p hp hs
      exact hb g p hp (Finset.mem_sdiff.mpr ⟨hs,
        source_original_PHYSICAL_G_active_birth_not_mem434 SP sm BP bm M background y hi b g p hp⟩)

theorem source_original_PHYSICAL_G_updated_background_seen434
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    (seen ∪ (sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1) ∪
      sourceOriginalNumericBackground434 BP bm (fun g => (b g).2.1))) ∩ B =
    (seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1) := by
  have ha : ∀ n ∈ sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1),n ∈ B := by
    intro n hn
    obtain ⟨g,hg,himg⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp himg
    exact source_original_PHYSICAL_G_background_birth_mem434 SP sm BP bm M background y hi a g p hp
  have hb : ∀ n ∈ sourceOriginalNumericBackground434 BP bm (fun g => (b g).2.1),n ∉ B := by
    intro n hn
    obtain ⟨g,hg,himg⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp himg
    exact source_original_PHYSICAL_G_active_birth_not_mem434 SP sm BP bm M background y hi b g p hp
  ext n
  have haa := ha n
  have hbb := hb n
  simp only [Finset.mem_inter,Finset.mem_union]
  tauto

/-- Both actual G gates use their respective numeric seen components,
and the updated full seen is reconstructed in the joint continuation. -/
theorem source_original_PHYSICAL_G_background_seen_row434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm M background y
      q rho N i V mu seen F =
    sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm M background y
      q rho N i V mu seen F := by
  unfold sourceOriginalPhysicalGhostBackgroundSplitRow434 sourceOriginalGhostBackgroundSeenRow434
  apply Finset.sum_congr rfl
  intro ab hab
  have he := source_original_PHYSICAL_G_separate_seen_gates434 SP sm BP bm M background y hi seen ab.1 ab.2
  by_cases h : (∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen ∩ B) ∧
      (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)
  · rw [if_pos h,if_pos (he.mpr h)]
    congr 2
    ext n
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,sourceOriginalNumericBackground434]
    tauto
  · rw [if_neg h,if_neg (fun h' => h (he.mp h'))]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemorySeparatedSeen -/

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

/-- Actual scheduled chain with separate numeric seen gates. E reads
only non-background seen; background seen is reattached to the joint
continuation. The full physical state remains in that continuation. -/
def sourceOriginalSeenSeparatedBackgroundChain434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,start,_,F => fun y seen =>
      sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen F
  | n+1,(r,h),start,sk,F => fun y seen =>
      sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm (J+ell) background y
        q 1 N start V mu seen (fun yg sg =>
          let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
            (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
          sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k z (sg \ B) r
            (fun out s =>
              sourceOriginalSeenSeparatedBackgroundChain434 q Vs V mu K zeta theta k N n h
                (start+1) (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r) F
                (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
                  (sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns sk r
                    (physicalAlternatingSign start) k) out) (s ∪ (sg ∩ B))))

theorem source_original_MEMORY_scheduled_background_seen434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalScheduledBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk F y seen =
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk F y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      exact source_original_PHYSICAL_G_background_seen_row434 SP sm BP bm (J+ell)
        background y hi q 1 N start V mu seen F
  | succ n ih =>
      rcases h with ⟨r,h⟩
      rw [sourceOriginalScheduledBackgroundChain434,sourceOriginalSeenSeparatedBackgroundChain434]
      dsimp only
      rw [source_original_PHYSICAL_G_background_seen_row434 SP sm BP bm (J+ell)
        background y hi]
      unfold sourceOriginalGhostBackgroundSeenRow434
      apply Finset.sum_congr rfl
      intro ab hab
      split_ifs
      · congr 1
        dsimp only
        rw [source_original_SOURCE_E_frame_background_seen_row434
          SP sm BP bm J ell m cap patterns hi background
          q 1 Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
          zeta theta _ _ r (physicalAlternatingSign start) k havoid.1]
        unfold sourceOriginalSourceEFrameFibreRow434
        apply Finset.sum_congr rfl
        intro f hf
        dsimp only
        congr 1
        exact ih h havoid.2 (start+1) _ _ _
      · rfl

def sourceOriginalSeenSeparatedBackgroundMemoryRoot434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
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
            (fun out _ => physicalVacuum SP sm BP bm J ell out)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full-root integration of the actual separated G/E seen gates.
The original MemorySourceDomain discharges the only structural
assumption, global numerical prime injectivity. -/
theorem source_original_MEMORY_root_seen_separated_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalSeenSeparatedBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q Vs V K zeta theta k R := by
  rw [source_original_MEMORY_root_scheduled_background_source_domain434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R hd]
  unfold sourceOriginalScheduledBackgroundMemoryRoot434 sourceOriginalSeenSeparatedBackgroundMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    exact source_original_MEMORY_scheduled_background_seen434 SP sm BP bm J ell m cap patterns
      _ hd.big_injective q Vs V _ K zeta theta k (2*R) _ (2*R) h
      (source_original_FULL_ACTIVE_HISTORY_complement_avoids434 SP sm BP bm J ell m patterns y (2*R) h)
      0 _ y _
  · simp only [if_neg hn]

theorem source_original_MEMORY_background_initial_seen_disjoint434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hact : sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell background y) :
    Disjoint (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset B := by
  apply Finset.disjoint_left.mpr
  intro n hn hnB
  have hnl := List.mem_toFinset.mp hn
  obtain ⟨g,hg,hgj⟩ := List.mem_flatMap.mp hnl
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hgj
  subst n
  exact hact g j ((source_original_NUMERIC_BACKGROUND_mem434 BP bm hi background g _).mp hnB)

/-- Every nonzero outer-vacuum summand starts with empty pending
memory and no seen label in its actual history-selected background. -/
theorem source_original_MEMORY_history_background_initial_empty434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hv : physicalVacuum SP sm BP bm J ell y ≠ 0)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n) :
    (∀ g,(y.2 g).2=0) ∧
    Disjoint (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      (sourceOriginalNumericBackground434 BP bm
        (fun g => Finset.univ \
          sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y n h g)) := by
  refine ⟨?_,?_⟩
  · by_contra hh
    exact hv (by simp [physicalVacuum,hh])
  · exact source_original_MEMORY_background_initial_seen_disjoint434 SP sm BP bm J ell
      _ hi y (source_original_FULL_ACTIVE_HISTORY_initial_avoids434 SP sm BP bm J ell m patterns y n h)
end Green64Analytic.CorrelationSquare

end

end

