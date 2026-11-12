module

public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Correlation / PhysicalEBackgroundBirthGate

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalEBackgroundBirthGate -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
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

/-- The genuine E birth list uses only target active labels, after the
original target permutation. A never-active numerical background cannot
enter this batch, even through auxiliary-D or OLD/store data. -/
theorem source_original_SOURCE_E_background_births_disjoint434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (background : Finset ℕ)
    (htarget : ∀ g j,bm g ((z.2.2.1.bigChoice g).1 j) ∉ background) :
    Disjoint background (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset := by
  apply Finset.disjoint_left.mpr
  intro p hp hb
  have hb' : p ∈ orientedEFreshBirths SP sm BP bm J ell m cap patterns z :=
    List.mem_toFinset.mp hb
  unfold orientedEFreshBirths at hb'
  obtain ⟨g,hg,hb'⟩ := List.mem_flatMap.mp hb'
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hb'
  exact htarget g (z.2.2.1.tauBig g j) (by rw [he];exact hp)

/-- Background seen labels pass the actual E eligibility test without
being forgotten. This removes their influence on this one gate only;
the complete terminal observation below still receives them. -/
theorem source_original_SOURCE_E_background_seen_gate434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (background seenActive seenBackground : Finset ℕ)
    (htarget : ∀ g j,bm g ((z.2.2.1.bigChoice g).1 j) ∉ background)
    (hseen : seenBackground ⊆ background) :
    orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns
      (seenActive ∪ seenBackground) z ↔
    orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seenActive z := by
  have hd := source_original_SOURCE_E_background_births_disjoint434
    SP sm BP bm J ell m cap patterns x z background htarget
  have hd' : Disjoint seenBackground
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset :=
    hd.mono_left hseen
  simp only [orientedEFreshBatchEligible,Finset.disjoint_union_left,hd',and_true]

/-- Exact signed source-oriented E witness, including the complete joint
K, original Fourier/Mellin phases and endpoint data. The background seen
set is carried through to F; no parity observation is discarded. -/
theorem source_original_SOURCE_ORIENTED_E_background_seen_witness434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (background seenActive seenBackground : Finset ℕ)
    (htarget : ∀ g j,bm g ((z.2.2.1.bigChoice g).1 j) ∉ background)
    (hseen : seenBackground ⊆ background)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (if orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns
        (seenActive ∪ seenBackground) z then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu K zeta theta o k x z *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        ((seenActive ∪ seenBackground) ∪
          (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0) =
    if orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seenActive z then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu K zeta theta o k x z *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        ((seenActive ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) ∪
          seenBackground)
    else 0 := by
  rw [source_original_SOURCE_E_background_seen_gate434 SP sm BP bm J ell m cap patterns
    x z background seenActive seenBackground htarget hseen]
  have hu : ((seenActive ∪ seenBackground) ∪
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) =
      ((seenActive ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) ∪
        seenBackground) := by
    ext p
    simp only [Finset.mem_union]
    tauto
  rw [hu]
end Green64Analytic.CorrelationSquare

end

end

