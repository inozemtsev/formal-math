module

public import Green64.Library.Weights.B26FullKernelTranspose
public import Green64.Library.Weights.Part083

@[expose] public section

/-!
# Correlation / B26CanonicalPhysicalBridge

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26CanonicalPhysicalBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem perm_aux_reorder
    {U A B : Type} [Fintype U] [Fintype A] [Fintype B]
    (f : U → A × B → ℂ) :
    (∑ st : A × B, ∑ u : U, f u st) =
      ∑ r : U × B × A, f r.1 (r.2.2,r.2.1) := by
  let e : (U × B × A) ≃ ((A × B) × U) :=
    { toFun := fun r => ((r.2.2,r.2.1),r.1)
      invFun := fun r => (r.2,r.1.2,r.1.1)
      left_inv := by rintro ⟨u,b,a⟩; rfl
      right_inv := by rintro ⟨⟨a,b⟩,u⟩; rfl }
  have he := e.sum_comp (fun r => f r.2 r.1)
  simpa only [Fintype.sum_prod_type,e,Equiv.coe_fn_mk] using he.symm

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
variable (data : SourceComparisonData434 SG G cfg x L Y Hp)
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (cap : G → ℕ) (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
local notation "BP" => (fun g => {p : ℕ // p ∈ data.Tb g})
local notation "State" => FullPhysicalState SP sm BP (fun _ => Subtype.val) (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP (fun _ => Subtype.val) (J+ell)
local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "mu" => physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
local notation "family" => sourceOriginalTwoBlockProbePatterns434 blockA blockB m
local notation "nu" => (fun v : family => (Subtype.val v))
local notation "patterns" => (fun v : family => sourceOriginalProbeMemoryPattern434 J m hmJ (Subtype.val v))
local notation "K" => (fun v : family =>
  sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig J ell m hmJ (Subtype.val v) Q h h xi)

/-- The canonical B26 mean is exactly the original coherent comparison
family, including its auxiliary law and all four normalized endpoint
means. This is an identity on arbitrary joint complex continuations. -/
theorem source_original_B26_CANONICAL_mean_original434
    (sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → BP g)
    (f : Small → A → Finset ℕ →
      SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime → ℂ)
    (xs : Small) (a : A) (S : Finset ℕ)
    (r : SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime) :
    sourceOriginalB26NodupPhysicalCleanMean434 data SP sm sizes prime cap hsizes q N
      blockA blockB J ell m hmJ Q h xi zeta theta o k false false f xs a S r =
    ∑ v ∈ family, sourceOriginalMarkedPhysicalCleanMean434 SP sm BP (fun _ => Subtype.val)
      J ell m hmJ v cap sizes hsizes prime o k q data.Vsmall data.Vbig mu
      (fun t => sourceOriginalMarkedCleanJointK434 SP sm BP (fun _ => Subtype.val)
        J ell m hmJ v t.1 t.2.1.1 t.2.1.2
        (sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig J ell m hmJ v Q h h xi)
        zeta theta o k) f xs a S r := by
  unfold sourceOriginalB26NodupPhysicalCleanMean434 sourceOriginalB26NodupPhysicalCleanFamily434
  simp only [sourceOriginalB26NumericSharedSign434, Bool.false_eq_true, ↓reduceIte,
    one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  unfold sourceOriginalMarkedPhysicalCleanMean434 sourceOriginalMarkedPhysicalFrameMass434
  simp only [←mul_assoc]
  rw [perm_aux_reorder]
  apply Finset.sum_congr rfl
  intro t ht
  push_cast
  ring

/-- Exact equality on the entire original ordered Fock-sector carrier,
before taking norms and without altering numerical birth-list Nodup. -/
theorem source_original_B26_CANONICAL_ordered_original434
    (f : State → Finset ℕ → ℂ) (a : State) (S : Finset ℕ) :
    sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k false false f a S =
    sourceOriginalMarkedCleanOrderedFamily434 SP sm BP (fun _ => Subtype.val)
      J ell m hmJ cap nu mu data.Vbig K q data.Vsmall zeta theta o k f a S := by
  unfold sourceOriginalB26NodupFullOrderedClean434 sourceOriginalMarkedCleanOrderedFamily434
  simp only [sourceOriginalMarkedFullOrderedClean434, sourceOriginalMarkedCleanFamilySectorK434]
  rw [source_original_B26_CANONICAL_mean_original434]
  symm
  exact Finset.sum_coe_sort family (fun v =>
    sourceOriginalMarkedFullOrderedClean434 SP sm BP (fun _ => Subtype.val)
      J ell m hmJ v cap o k q data.Vsmall data.Vbig mu
      (fun _d r => sourceOriginalMarkedCleanJointK434 SP sm BP (fun _ => Subtype.val)
        J ell m hmJ v r.1 r.2.1.1 r.2.1.2
        (sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig J ell m hmJ v Q h h xi)
        zeta theta o k) f a S)

/-- The original physical CLEAN comparison channel, with its real
source divisor, ban, OLD translations and common seen update, is
literally the canonical B26 packet on the actual reachable support. -/
theorem source_original_B26_CANONICAL_physical_original434
    (F : Out → Finset ℕ → ℂ) (a : State) (S : Finset ℕ)
    (hseen : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell)
      (fun g => (a.2 g).1)).image (fun p : Sigma BP => p.2.val) ⊆ S) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
      q 1 data.Vsmall data.Vbig mu K zeta theta o k a S F =
    sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k false false
      (fun b T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap b) T)
      a S := by
  rw [source_original_MARKED_CLEAN_full_ordered_literal434 SP sm BP (fun _ => Subtype.val)
    J ell m hmJ cap nu mu data.Vbig K q data.Vsmall zeta theta o k F a S hseen]
  exact (source_original_B26_CANONICAL_ordered_original434 data SP sm cap q N blockA blockB
    J ell m hmJ Q h xi zeta theta o k _ a S).symm

end Green64Analytic.CorrelationSquare

end

end

