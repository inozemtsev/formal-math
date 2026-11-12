module

public import Green64.Library.Weights.Part082

@[expose] public section

/-!
# Weights / MarkedCleanMeanLiteral

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedCleanMeanLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 900000

private theorem sum_endpoint_order
    {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    (∑ a,∑ b,∑ c,∑ d,f a b c d) = ∑ c,∑ d,∑ a,∑ b,f a b c d := by
  let e : (C × D × A × B) ≃ (A × B × C × D) :=
    { toFun := fun p => (p.2.2.1,p.2.2.2,p.1,p.2.1)
      invFun := fun p => (p.2.2.1,p.2.2.2,p.1,p.2.1)
      left_inv := by rintro ⟨c,d,a,b⟩;rfl
      right_inv := by rintro ⟨a,b,c,d⟩;rfl }
  have h := e.sum_comp (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2)
  simpa only [Fintype.sum_prod_type,e,Equiv.coe_fn_mk] using h.symm

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J)
variable (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))
local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Exact identification of the literal original CLEAN sum with the
verified physical Hilbert channels, for ALL actual patterns coherently.
The SAME arbitrary future is used before every auxiliary/endpoint sum. -/
theorem source_original_MARKED_CLEAN_family_mean_literal434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ)
    (hseen : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) a).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t) S F =
    ∑ i : I,sourceOriginalMarkedPhysicalCleanMean434 SP sm BP bm J ell m hmJ (nu i)
      cap sizes hsizes prime o k q Vs Vb mu
      (fun r => sourceOriginalMarkedCleanJointK434 SP sm BP bm J ell m hmJ (nu i)
        r.1 r.2.1.1 r.2.1.2 (K i) zeta theta o k)
      (fun ys b T u => sourceOriginalB26TargetPullback434 SP sm BP bm
        J ell cap sizes hsizes prime (fun Y => F Y T) ys b u) xs a S t := by
  rw [source_original_MARKED_CLEAN_full_literal_row434]
  unfold sourceOriginalMarkedPhysicalCleanMean434
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro aux haux
  apply Finset.sum_congr rfl
  intro sigma hsigma
  apply Finset.sum_congr rfl
  intro tau htau
  rw [sum_endpoint_order]
  apply Finset.sum_congr rfl
  intro ss hss
  apply Finset.sum_congr rfl
  intro tt htt
  exact (source_original_MARKED_CLEAN_frame_channel434 SP sm BP bm J ell m hmJ
    cap sizes hsizes prime nu i mu Vb K q Vs zeta theta o k F xs a t S hseen
    (aux,(sigma,tau),(ss,tt))).symm

/-- The literal joint coefficient expressed on the entire ORIGINAL
ordered sector carrier; no new analytic or bounded-mask input appears. -/
def sourceOriginalMarkedCleanFamilySectorK434
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (i : I) :
    SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ (nu i) cap :=
  fun _d r => sourceOriginalMarkedCleanJointK434 SP sm BP bm J ell m hmJ (nu i)
    r.1 r.2.1.1 r.2.1.2 (K i) zeta theta o k

/-- ALL actual ordered sectors use the same explicit per-pattern cap. -/
theorem source_original_MARKED_CLEAN_family_sector_K_cap434
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (C : I → ℝ) (hC : ∀ i,0 ≤ C i)
    (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (i : I) (d : SourceOriginalMarkedSectorIndex434 BP cap)
    (r : SourceBigAux BP J m (patterns i) ×
      (BigGroupPerm (BG := BG) (J+ell) × BigGroupPerm (BG := BG) (J+ell)) ×
      (GroupPermFamily (G := SG) (J+ell) × GroupPermFamily (G := SG) (J+ell)))
    (e : SourceOriginalB26SharedTuple434 SP J ell)
    (y : memoryFrozenResidueGroup SP sm BP bm (fun g => (d.1 g).val) d.2)
    (a : A) (S : Finset ℕ) (b : A) :
    ‖sourceOriginalMarkedCleanFamilySectorK434 SP sm BP bm J ell m hmJ cap nu
      K zeta theta o k i d r e y a S b‖ ≤ C i := by
  exact source_original_MARKED_CLEAN_joint_K_cap434 SP sm BP bm J ell m hmJ (nu i)
    r.1 r.2.1.1 r.2.1.2 (K i) zeta theta o k (C i) (hC i) (hK i) e y a S b

end Green64Analytic.CorrelationSquare

end

end

