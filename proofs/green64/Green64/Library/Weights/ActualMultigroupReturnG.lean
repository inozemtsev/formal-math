module

public import Green64.Library.Weights.Part060
public import Green64.Library.Weights.Part061
public import Green64.Library.Weights.ReachableBackgroundRow

@[expose] public section

/-!
# Weights / ActualMultigroupReturnG

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualMultigroupReturnG -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem background_seen_union
    {I : Type} [Fintype I] [DecidableEq I]
    (B b : I → Finset ℕ) (hb : ∀ i,b i ⊆ B i) (seen : Finset ℕ) :
    (Finset.univ.biUnion (fun i => (seen ∪ b i) ∩ B i)) =
      (seen ∩ Finset.univ.biUnion B) ∪ Finset.univ.biUnion b := by
  ext n
  simp only [Finset.mem_biUnion,Finset.mem_inter,Finset.mem_union,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,(hs|hn),hi⟩
    · exact Or.inl ⟨hs,i,hi⟩
    · exact Or.inr ⟨i,hn⟩
  · rintro (⟨hs,i,hi⟩|⟨i,hi⟩)
    · exact ⟨i,Or.inl hs,hi⟩
    · exact ⟨i,Or.inr hi,hb i hi⟩

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))

def sourceOriginalBackgroundPendingAttach434
    (pending : (g : BG) → Multiset (Atom (BP g) (bm g)))
    (out : FullPhysicalOutput SP sm BP bm M) : FullPhysicalOutput SP sm BP bm M :=
  (out.1,fun g => ((out.2 g).1,pending g + (out.2 g).2))

/-- Exact signed return row for ALL background groups, with the original
active G operator and arbitrary joint physical continuation still inside.
The numerical seen set is reconstructed from the local output projections. -/
def sourceOriginalMultigroupBackgroundReturnG434
    (y : FullPhysicalOutput SP sm BP bm M)
    (shift : ℤ) (s : (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g))
    (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ t : (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g),
    (∏ g,∏ p,sourceOriginalPrimeReturnKernel434 (bm g) p shift
      (sourceVisitEta q N i) (V g) (mu g) (s g p) (t g p)) *
    sourceOriginalActiveGhostSeenRow434 SP sm BP bm M background
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)
      q 1 N i V mu (seen \ sourceOriginalNumericBackground434 BP bm background)
      (fun out activeSeen =>
        F (sourceOriginalBackgroundPendingAttach434 SP sm BP bm M
          (fun g => sourceOriginalPrimeProductPending434 (bm g) shift (t g)) out)
          ((Finset.univ.biUnion (fun g =>
            (((seen \ (background g).image (bm g)) ∪
              (sourceOriginalPrimeProductSeen434 (bm g) (t g) ∩ background g).image (bm g)) ∩
                (background g).image (bm g)))) ∪ activeSeen))

/-- No product factorization is imposed on F or on the active G row.
Every group has its own original V and mu. -/
theorem source_original_ACTUAL_MULTIGROUP_G_return_matrix434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hi : ∀ g,Function.Injective (bm g))
    (shift : ℤ) (s : (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g))
    (hs : ∀ g p,p ∉ background g → s g p=.retired)
    (hp : ∀ g,sourceOriginalPrimeProductPending434 (bm g) shift (s g) =
      ((y.2 g).2).filter (fun z => z.1 ∈ background g))
    (hseen : ∀ g,(seen \ (background g).image (bm g)) ∪
      (sourceOriginalPrimeProductSeen434 (bm g) (s g) ∩ background g).image (bm g)=seen)
    (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalBackgroundSeparatedGhostOperator434 SP sm BP bm M background y
      q 1 N i V mu seen F =
    sourceOriginalMultigroupBackgroundReturnG434 SP sm BP bm M background y
      shift s q N i V mu seen F := by
  let A : BG → Type := fun g => SourceOriginalRestrictedPrimeBirthChoice434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
    (Finset.univ.filter (fun p => p ∈ background g))
  let T : BG → Type := fun g => SourceOriginalPrimeReturnProductState434 (bm g)
  let X : BG → Type := fun g => Multiset (Atom (BP g) (bm g)) × Finset ℕ
  let phi : (g : BG) → A g → X g := fun g a =>
    (sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) a.1.1 a.2.1,
      seen ∪ a.2.1.image (bm g))
  let psi : (g : BG) → T g → X g := fun g t =>
    (sourceOriginalPrimeProductPending434 (bm g) shift t,
      (seen \ (background g).image (bm g)) ∪
        (sourceOriginalPrimeProductSeen434 (bm g) t ∩ background g).image (bm g))
  let w : (g : BG) → A g → ℂ := fun g a =>
    if ∀ p ∈ a.2.1,bm g p ∉ seen then
      sourceOriginalGroupPrimeBirthWeight434 (bm g)
        (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
        (-((sourceVisitEta q N i:ℝ):ℂ)/(1:ℂ))
        (((sourceVisitQ q N i:ℝ):ℂ)/(1:ℂ)^2)
        (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(1:ℂ))
        (fun p => (mu g p:ℂ)) (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ a)
    else 0
  let v : (g : BG) → T g → ℂ := fun g t =>
    ∏ p,sourceOriginalPrimeReturnKernel434 (bm g) p shift
      (sourceVisitEta q N i) (V g) (mu g) (s g p) (t p)
  let H : ((g : BG) → X g) → ℂ := fun z =>
    sourceOriginalActiveGhostSeenRow434 SP sm BP bm M background
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)
      q 1 N i V mu (seen \ sourceOriginalNumericBackground434 BP bm background)
      (fun out activeSeen =>
        F (sourceOriginalBackgroundPendingAttach434 SP sm BP bm M (fun g => (z g).1) out)
          ((Finset.univ.biUnion (fun g => (z g).2 ∩ (background g).image (bm g))) ∪ activeSeen))
  have hrow : ∀ g (f : X g → ℂ),
      (∑ a : A g,w g a * f (phi g a)) = ∑ t : T g,v g t * f (psi g t) := by
    intro g f
    have hext : ∀ p ∈ background g,bm g p ∉ seen \ (background g).image (bm g) := by
      intro p hp' hn
      exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_image_of_mem (bm g) hp')
    have hr := source_original_NUMERIC_BACKGROUND_POOL_G_return_matrix434
      (bm g) (background g) shift (s g) (hs g) (hi g)
      (seen \ (background g).image (bm g)) hext
      (sourceVisitEta q N i) (V g) (mu g) (fun out st => f (out,st))
    rw [hp g,hseen g] at hr
    exact (source_original_ACTUAL_BACKGROUND_group_G434
      (bm g) (background g) (y.2 g).2 q N i (V g) (mu g) seen
      (fun out st => f (out,st))).trans hr
  have ht := source_original_FINITE_joint_row_congr434 A T X phi psi w v hrow H
  have hl :
      sourceOriginalBackgroundSeparatedGhostOperator434 SP sm BP bm M background y
        q 1 N i V mu seen F =
      ∑ a : (g : BG) → A g,(∏ g,w g (a g))*H (fun g => phi g (a g)) := by
    unfold sourceOriginalBackgroundSeparatedGhostOperator434
    apply Finset.sum_congr rfl
    intro a ha
    have hb : ∀ g,(a g).2.1 ⊆ background g := by
      intro g p hp'
      exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp')).2
    have hnum : ∀ g,(a g).2.1.image (bm g) ⊆ (background g).image (bm g) := by
      intro g
      exact Finset.image_mono (bm g) (hb g)
    have hg : (∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen ∩
        sourceOriginalNumericBackground434 BP bm background) ↔
        (∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen) := by
      constructor
      · intro h g p hp' hn
        apply h g p hp'
        exact Finset.mem_inter.mpr ⟨hn,Finset.mem_biUnion.mpr
          ⟨g,Finset.mem_univ g,Finset.mem_image_of_mem (bm g) (hb g hp')⟩⟩
      · intro h g p hp' hn
        exact h g p hp' (Finset.mem_inter.mp hn).1
    have hw : (∏ g,w g (a g)) =
        if ∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen then
          sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q 1 N i V mu a
        else 0 := by
      dsimp only [w]
      rw [source_original_FINITE_product_gate434]
      rfl
    rw [hw]
    by_cases h : ∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen
    · rw [if_pos h,if_pos (hg.mpr h)]
      have hu := background_seen_union
        (fun g => (background g).image (bm g)) (fun g => (a g).2.1.image (bm g)) hnum seen
      dsimp only [H,phi]
      rw [hu]
      rfl
    · rw [if_neg h,if_neg (fun hh => h (hg.mp hh)),zero_mul]
  exact hl.trans ht
end Green64Analytic.CorrelationSquare

end

end

