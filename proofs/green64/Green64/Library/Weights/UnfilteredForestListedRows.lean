module

public import Green64.Library.Weights.Part028

@[expose] public section

/-!
# Weights / UnfilteredForestListedRows

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredForestListedRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A single original numerical birth batch, retaining its local LIST
Nodup filter. This identity is valid even for a repeated prior register. -/
theorem source_original_forest_LIST_GATE434 (H B : List ℕ) (c : ℂ)
    (F : Finset ℕ → ℂ) :
    (if B.Nodup then c*(if (H++B).Nodup then F (H++B).toFinset else 0) else 0) =
    if H.Nodup then
      (if B.Nodup ∧ Disjoint H.toFinset B.toFinset then c*F (H.toFinset ∪ B.toFinset) else 0)
    else 0 := by
  by_cases hH : H.Nodup <;> by_cases hB : B.Nodup <;>
    by_cases hd : Disjoint H.toFinset B.toFinset <;>
    simp [physical_list_nodup_append_iff_disjoint,hH,hB,hd,List.toFinset_append]

private theorem ite_instance434 {A : Type*} (p : Prop) (d₁ d₂ : Decidable p) (a b : A) :
    @ite A p d₁ a b = @ite A p d₂ a b := by
  have h : d₁=d₂ := Subsingleton.elim _ _
  rw [h]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap

/-- Original symmetric G with only the seen-disjointness gate erased.
The complete chronological numeric list is a scalar register, with no
history Hilbert measure; actual ordered representatives are still averaged. -/
def sourceOriginalForestListedG434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List ℕ)
    (F : Output → List ℕ → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => ∑ y : State,∑ z : FullGhostWitness SP sm BP bm (J+ell) cap x,
      if (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup then
        physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
          F (physicalFockProjection SP sm BP bm (J+ell) cap y)
            (H++physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z)
      else 0) X

/-- Original oriented symmetric E with its actual fresh target LIST and
all original choices, auxiliary labels, permutations and full joint K. -/
def sourceOriginalForestListedE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List ℕ)
    (F : Output → List ℕ → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
      if (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z *
          F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
            (H++orientedEFreshBirths SP sm BP bm J ell m cap patterns z)
      else 0) X

theorem source_original_forest_LISTED_G_EXACT434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List ℕ)
    (F : Output → Finset ℕ → ℂ) (X : Output) :
    sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N i Vs V mu H
      (fun Y H' => if H'.Nodup then F Y H'.toFinset else 0) X =
    if H.Nodup then physicalMarkedSymmetricG SP sm BP bm J ell cap
      q rho N i Vs V mu X H.toFinset F else 0 := by
  unfold sourceOriginalForestListedG434 physicalMarkedSymmetricG physicalGBirthMarkedRow
  simp_rw [source_original_forest_LIST_GATE434]
  by_cases hH : H.Nodup
  · simp only [if_pos hH,physicalGhostBatchEligible]
    congr 1
    funext x
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    exact ite_instance434 _ _ _ _ _
  · simp [hH,fullPhysicalOrbitAverage]

theorem source_original_forest_LISTED_E_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List ℕ)
    (F : Output → Finset ℕ → ℂ) (X : Output) :
    sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H
      (fun Y H' => if H'.Nodup then F Y H'.toFinset else 0) X =
    if H.Nodup then physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k X H.toFinset F else 0 := by
  unfold sourceOriginalForestListedE434 physicalOrientedMarkedSymmetricE physicalOrientedBirthMarkedE
  simp_rw [source_original_forest_LIST_GATE434]
  by_cases hH : H.Nodup
  · simp only [if_pos hH,orientedEFreshBatchEligible]
    congr 1
    funext x
    apply Finset.sum_congr rfl
    intro z hz
    exact ite_instance434 _ _ _ _ _
  · simp [hH,fullPhysicalOrbitAverage]
end Green64Analytic.CorrelationSquare

end

end

