module

public import Green64.Library.Correlation.Part046
public import Green64.Library.Weights.Part018
public import Green64.Library.Correlation.Part006
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.Part045

@[expose] public section

/-!
# Correlation / Part047

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryStoreOnlyPairReversal -/

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

/-- Any literal branch restriction, with the unchanged original
coefficient, physical density and two actual Fock endpoints. -/
def sourceOriginalMemoryOriginalFilteredDensityPair434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y) ∧ keep st z
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

theorem source_original_memory_FILTERED_density_pair_nonneg434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    0 ≤ sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
      patterns keep q rho Vs Vb mu Knu zeta theta o k X Y := by
  apply Finset.sum_nonneg
  intro st hst
  apply mul_nonneg
  · exact source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st
  · apply Finset.sum_nonneg
    intro z hz
    split_ifs <;> first | exact norm_nonneg _ | exact le_rfl

theorem source_original_memory_PAIR_OLD_projection434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    (∑ g : BG,((physicalFockProjection SP smallMod BP bigMod (J+ell) cap st).2 g).2.card) =
      ∑ g : BG,(st.2 g).2.1.val := by
  simp only [physicalFockProjection,Green64Fock.fockMultiset,Multiset.coe_card,List.length_ofFn]

/-- The store-only absolute pair kernel is supported on strict TOTAL
OLD increase. This bounds a literal branch restriction, without
asserting that the full original coefficient is invariant under reversal. -/
theorem source_original_memory_STORE_ONLY_density_pair_OLD_upper434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k X Y ≤
    if (∑ g : BG,(X.2 g).2.card) < ∑ g : BG,(Y.2 g).2.card then
      sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k X Y else 0 := by
  classical
  by_cases hh : (∑ g : BG,(X.2 g).2.card) < ∑ g : BG,(Y.2 g).2.card
  · rw [if_pos hh]
    apply Finset.sum_le_sum
    intro st hst
    apply mul_le_mul_of_nonneg_left _
      (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
        J ell cap Vs Vb mu hVs hVb hmu st)
    apply Finset.sum_le_sum
    intro z hz
    dsimp only
    split_ifs with hp hp'
    · exact le_rfl
    · exact False.elim (hp' hp.1)
    · exact norm_nonneg _
    · exact le_rfl
  · rw [if_neg hh]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro st hst
    suffices he : (∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y) ∧
        ((¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
          (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0)=0 by
      convert (congrArg (fun a : ℝ =>
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st * a) he).trans
          (mul_zero _) using 1
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> rfl
    apply Finset.sum_eq_zero
    intro z hz
    apply if_neg
    rintro ⟨⟨hx,hl,hy⟩,hnp,hs⟩
    have hold := source_original_memory_ORIGINAL_store_only_OLD_strict434 SP smallMod BP bigMod
      J ell m cap patterns st o k z hnp hs
    rw [hy] at hold
    have hinput := source_original_memory_PAIR_OLD_projection434 SP smallMod BP bigMod J ell cap st
    rw [hx] at hinput
    exact hh (by simpa only [hinput] using hold)

/-- Every actual branch between a decreasing TOTAL OLD endpoint pair
belongs to promotion. All multiplicities remain in the original carrier. -/
theorem source_original_memory_OLD_decrease_density_pair_is_promotion434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (hh : (∑ g : BG,(Y.2 g).2.card) < ∑ g : BG,(X.2 g).2.card) :
    sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k X Y =
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k X Y := by
  classical
  apply Finset.sum_congr rfl
  intro st hst
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only
  by_cases hp : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
      sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
  · have hinput := source_original_memory_PAIR_OLD_projection434 SP smallMod BP bigMod J ell cap st
    rw [hp.1] at hinput
    have hprom := source_original_memory_ORIGINAL_OLD_decrease_has_promotion434 SP smallMod BP bigMod
      J ell m cap patterns st o k z (by simpa only [hp.2.2,hinput] using hh)
    rw [if_pos hp,if_pos ⟨hp,hprom⟩]
  · rw [if_neg hp,if_neg (fun h => hp h.1)]

/-- Actual store-only is dominated by reversed actual promotion in the
weighted physical orbit-pair kernel. The result has no analytic saving
premise and permits arbitrary joint K; reversal transposes that K.
A uniform promotion bound must still be applied with the correct
source/target OLD projections. -/
theorem source_original_memory_STORE_ONLY_density_pair_le_reverse_promotion434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k X Y ≤
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k Y X := by
  classical
  apply (source_original_memory_STORE_ONLY_density_pair_OLD_upper434 SP smallMod BP bigMod
    J ell m cap patterns q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X Y).trans
  split_ifs with hh
  · rw [source_original_memory_ORIGINAL_density_pair_reverse434 SP smallMod BP bigMod
      J ell m cap patterns q rho Vs Vb mu hmu hVb hr Knu zeta theta o k X Y]
    rw [source_original_memory_OLD_decrease_density_pair_is_promotion434 SP smallMod BP bigMod
      J ell m cap patterns q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s)
        zeta theta (-o) k Y X hh]
  · exact source_original_memory_FILTERED_density_pair_nonneg434 SP smallMod BP bigMod
      J ell m cap patterns _ q rho Vs Vb mu hVs hVb hmu _ zeta theta (-o) k Y X
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryStoreOnlyColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 30000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalMemoryOriginalFilteredDensityColumn434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if (sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y) ∧ keep st z
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

def sourceOriginalMemoryOriginalFilteredRow434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℝ :=
  ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

theorem source_original_memory_FILTERED_pair_source_sum434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k X Y) =
    sourceOriginalMemoryOriginalFilteredDensityColumn434 SP smallMod BP bigMod J ell m cap
      patterns keep q rho Vs Vb mu Knu zeta theta o k Y := by
  classical
  unfold sourceOriginalMemoryOriginalFilteredDensityPair434
    sourceOriginalMemoryOriginalFilteredDensityColumn434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro st hst
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  have hm : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st ∈
      physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap :=
    Finset.mem_image.mpr ⟨st,Finset.mem_univ _,rfl⟩
  rw [Finset.sum_eq_single (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st)]
  · simp only [eq_self_iff_true,true_and]
  · intro X hX hne
    apply if_neg
    intro h
    exact hne h.1.1.symm
  · exact fun hnot => False.elim (hnot hm)

theorem source_original_memory_FILTERED_pair_target_sum434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k X Y) =
    ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X then
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
          sourceOriginalMemoryOriginalFilteredRow434 SP smallMod BP bigMod J ell m cap patterns
            keep q rho Vs Vb mu Knu zeta theta o k st else 0 := by
  classical
  unfold sourceOriginalMemoryOriginalFilteredDensityPair434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro st hst
  rw [← Finset.mul_sum,Finset.sum_comm]
  by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X
  · rw [if_pos hx]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
    · have hm := source_original_memory_ORIGINAL_legal_output_mem434 SP smallMod BP bigMod
        J ell m cap patterns st o k z hl
      rw [Finset.sum_eq_single
        (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)]
      · simp only [hx,hl,eq_self_iff_true,true_and]
      · intro Y hY hne
        apply if_neg
        intro h
        exact hne h.1.2.2.symm
      · exact fun hnot => False.elim (hnot hm)
    · simp only [hl,false_and,and_false,ite_false,Finset.sum_const_zero]
  · simp only [hx,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem source_original_memory_PROMOTION_filtered_row434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemoryOriginalFilteredRow434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k st =
    sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st := by
  classical
  unfold sourceOriginalMemoryOriginalFilteredRow434 sourceOriginalMemoryOriginalEPromotionRow434
  apply Finset.sum_congr rfl
  intro z hz
  congr <;> exact Subsingleton.elim _ _

/-- Exact physical weighted-column reduction of actual store-only to
the transposed original promotion rows on the TARGET orbit. It keeps
all OLD cutoffs and original branch witnesses. -/
theorem source_original_memory_STORE_ONLY_density_column_reverse434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalFilteredDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k Y ≤
    ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=Y then
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
          sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
            q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k st else 0 := by
  classical
  rw [← source_original_memory_FILTERED_pair_source_sum434]
  calc
    _ ≤ ∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
          q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k Y X :=
      Finset.sum_le_sum (fun X _ =>
        source_original_memory_STORE_ONLY_density_pair_le_reverse_promotion434 SP smallMod BP bigMod
          J ell m cap patterns q rho Vs Vb mu hVs hVb hmu hr Knu zeta theta o k X Y)
    _ = _ := by
      rw [source_original_memory_FILTERED_pair_target_sum434]
      simp_rw [source_original_memory_PROMOTION_filtered_row434]

/-- The target-orbit row bound is charged with its TRUE density mass.
There is no sector count, maximal density ratio or free rho damping. -/
theorem source_original_memory_STORE_ONLY_density_column_of_reverse_row434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (R : ℝ)
    (hrow : ∀ st,physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=Y →
      sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k st ≤ R) :
    sourceOriginalMemoryOriginalFilteredDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k Y ≤
    R*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y) := by
  classical
  have hm :
      (∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=Y then
          sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st else 0) =
      physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y := by
    have hh := source_original_memory_sector_density_orbit_mass434 SP smallMod BP bigMod J ell cap Vs Vb mu Y
    simp only [Finset.sum_filter] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro st hst
    by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=Y
    · simp only [hx,ite_true,sourceOriginalMemoryFullDensityMass434]
    · simp only [hx,ite_false]
  apply (source_original_memory_STORE_ONLY_density_column_reverse434 SP smallMod BP bigMod
    J ell m cap patterns q rho Vs Vb mu hVs hVb hmu hr Knu zeta theta o k Y).trans
  rw [← hm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro st hst
  by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=Y
  · rw [if_pos hx,if_pos hx]
    exact (mul_le_mul_of_nonneg_left (hrow st hx)
      (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
        J ell cap Vs Vb mu hVs hVb hmu st)).trans_eq (mul_comm _ _)
  · rw [if_neg hx,if_neg hx,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFilteredOrbitKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
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

def sourceOriginalMemoryOriginalFilteredE434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℂ :=
  ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
    then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z) else 0

theorem source_original_memory_STORE_ONLY_filtered_E434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    sourceOriginalMemoryOriginalFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k st F =
    sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F := by
  classical
  unfold sourceOriginalMemoryOriginalFilteredE434 sourceOriginalMemoryOriginalEStoreOnly434
    sourceOrientedPhysicalChoices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
  · simp only [hl,true_and,ite_true]
  · simp only [hl,false_and,ite_false]

theorem source_original_memory_FULL_density_orbit_nonneg434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    0 ≤ physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X := by
  rw [source_original_memory_FULL_density_orbit_product434]
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g _ =>
      (stateMass_positive (smallMod g) (J+ell) (Vs g) (hVs g)).le)
  · apply Finset.prod_nonneg
    intro g hg
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact mul_nonneg
        (bigStateMass_positive (bigMod g) (J+ell) (cap g) (mu g) (hmu g) x).le
        (pow_nonneg (hVb g).le _)
    · exact le_rfl

/-- Exact output-fibre formula with an arbitrary joint physical test
after the input endpoint is fixed. Original branch multiplicities are
preserved in the finite pair kernel. -/
theorem source_original_memory_FILTERED_pair_target_weighted434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (u : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℝ) :
    (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k X Y * u Y) =
    ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
      ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ *
          u (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
        else 0 := by
  classical
  have he (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) :
      (if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ *
          u (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
        else 0) =
      ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        (if (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y) ∧ keep st z
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ else 0)*u Y := by
    by_cases h : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
    · have hm := source_original_memory_ORIGINAL_legal_output_mem434 SP smallMod BP bigMod
        J ell m cap patterns st o k z h.2.1
      simp only [h.1,h.2.1,h.2.2,true_and,and_true,ite_true,ite_mul,zero_mul]
      rw [Finset.sum_eq_single
        (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)]
      · simp
      · intro Y hY hne
        exact if_neg (Ne.symm hne)
      · exact fun hnot => False.elim (hnot hm)
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro Y hY
      rw [if_neg (fun hh => h ⟨hh.1.1,hh.1.2.1,hh.2⟩),zero_mul]
  simp_rw [he]
  unfold sourceOriginalMemoryOriginalFilteredDensityPair434
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2;ext st
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro st hst
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro Y hY
  ring

/-- The true original Fock compression is dominated by its physical
absolute pair kernel. This is the explicit bridge from signed E to
the pair estimates; no pointwise history estimate is asserted. -/
theorem source_original_memory_FILTERED_compressed_pair_norm434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
    ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryOriginalFilteredE434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k st F) X‖ ≤
    ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k X Y * ‖F Y‖ := by
  classical
  let M := physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
  let N := ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X then
      (sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st:ℂ) *
      sourceOriginalMemoryOriginalFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st F else 0
  have hM : 0 ≤ M := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  have ha :
      fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryOriginalFilteredE434 SP smallMod BP bigMod J ell m cap
          patterns keep q rho Vs Vb mu Knu zeta theta o k st F) X = N/(M:ℂ) := by
    rw [← source_original_memory_sector_density_orbit_average434 SP smallMod BP bigMod
      J ell cap Vs Vb hVb mu]
    unfold sourceOriginalMemoryDensityOrbitAverage434
    simp only [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro st hst
    by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X
    · simp only [hx,ite_true,sourceOriginalMemoryFullDensityMass434]
    · simp only [hx,ite_false]
  have ht : ‖N‖ ≤ ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k X Y * ‖F Y‖ := by
    rw [source_original_memory_FILTERED_pair_target_weighted434]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro st hst
    have hw := source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st
    by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X
    · rw [if_pos hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z hz
      by_cases hh : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧ keep st z
      · simp only [hx,hh.1,hh.2,true_and,ite_true,norm_mul,le_refl]
      · simp only [hx,true_and,hh,ite_false,norm_zero,le_refl]
    · simp only [hx,false_and,ite_false,norm_zero,Finset.sum_const_zero,mul_zero,le_refl]
  rw [ha,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
  change M*(‖N‖/M) ≤ _
  by_cases hz : M=0
  · rw [hz,zero_mul]
    exact (norm_nonneg N).trans ht
  · calc
      _ = ‖N‖ := by field_simp
      _ ≤ _ := ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedDensityPair -/

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

/-- Literal original absolute pair kernel with the actual GLOBAL birth
list and both seen endpoints; witnesses remain separate inside each sum. -/
def sourceOriginalMemoryMarkedDensityPair434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (t : Finset ℕ) : ℝ :=
  sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
    (fun st z => keep st z ∧ sourceOriginalBirthHistoryGate434
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) s t)
    q rho Vs Vb mu Knu zeta theta o k X Y

theorem source_original_memory_MARKED_pair_nonneg434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (t : Finset ℕ) :
    0 ≤ sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X s Y t := by
  exact source_original_memory_FILTERED_density_pair_nonneg434 SP smallMod BP bigMod
    J ell m cap patterns _ q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X Y

theorem source_original_memory_MARKED_pair_history_row434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ))
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ) :
    (∑ t ∈ H,sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X s Y t) ≤
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X Y := by
  classical
  unfold sourceOriginalMemoryMarkedDensityPair434 sourceOriginalMemoryOriginalFilteredDensityPair434
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro st hst
  rw [← Finset.mul_sum,Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _
    (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st)
  apply Finset.sum_le_sum
  intro z hz
  by_cases hb : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
      sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
  · by_cases hk : keep st z
    · simp only [hb,hk,true_and,ite_true]
      exact source_original_birth_history_row434 H
        (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) s _ (norm_nonneg _)
    · simp only [hk,and_false,false_and,ite_false,Finset.sum_const_zero,le_refl]
  · simp only [hb,false_and,ite_false,Finset.sum_const_zero,le_refl]

theorem source_original_memory_MARKED_pair_history_column434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ))
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (t : Finset ℕ) :
    (∑ s ∈ H,sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X s Y t) ≤
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X Y := by
  classical
  unfold sourceOriginalMemoryMarkedDensityPair434 sourceOriginalMemoryOriginalFilteredDensityPair434
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro st hst
  rw [← Finset.mul_sum,Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _
    (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st)
  apply Finset.sum_le_sum
  intro z hz
  by_cases hb : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
      sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
  · by_cases hk : keep st z
    · simp only [hb,hk,true_and,ite_true]
      exact source_original_birth_history_column434 H
        (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) t _ (norm_nonneg _)
    · simp only [hk,and_false,false_and,ite_false,Finset.sum_const_zero,le_refl]
  · simp only [hb,false_and,ite_false,Finset.sum_const_zero,le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedOrbitKernel -/

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

/-- Original marked E with a witness predicate. The actual fresh birth
list and global test are retained before any endpoint compression. -/
def sourceOriginalMemoryMarkedFilteredE434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (s : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) : ℂ :=
  ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        keep st z ∧ orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns s z
    then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
        (s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset)
    else 0

theorem source_original_memory_MARKED_E_literal434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (s : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ _ => True) q rho Vs Vb mu Knu zeta theta o k st s F =
    physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st s F := by
  classical
  unfold sourceOriginalMemoryMarkedFilteredE434 physicalOrientedBirthMarkedE
    sourceOrientedPhysicalChoices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
  · simp only [hl,true_and,ite_true]
  · simp only [hl,false_and,ite_false]

theorem source_original_memory_MARKED_E_history_expansion434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ)) (s : Finset ℕ)
    (hclosed : ∀ (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st),
      s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈ H)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k st s F =
    ∑ t ∈ H,sourceOriginalMemoryOriginalFilteredE434 SP smallMod BP bigMod J ell m cap patterns
      (fun st z => keep st z ∧ sourceOriginalBirthHistoryGate434
        (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) s t)
      q rho Vs Vb mu Knu zeta theta o k st (fun Y => F Y t) := by
  classical
  unfold sourceOriginalMemoryMarkedFilteredE434 sourceOriginalMemoryOriginalFilteredE434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_eq_single
    (s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset)]
  · simp only [sourceOriginalBirthHistoryGate434,orientedEFreshBatchEligible,
      eq_self_iff_true,and_true,and_assoc]
    congr 1 <;> exact Subsingleton.elim _ _
  · intro t ht hne
    apply if_neg
    intro hh
    exact hne hh.2.2.2.2.symm
  · exact fun hn => False.elim (hn (hclosed st z))

theorem source_original_memory_ORIGINAL_orbit_sum434
    {β : Type} (H : Finset β)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : β → FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => ∑ t ∈ H,f t st) X =
    ∑ t ∈ H,fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu (f t) X := by
  unfold fullPhysicalOrbitAverage
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]

/-- Actual signed marked E, after the ORIGINAL orbit average, is
dominated by its literal history-resolved absolute pair kernel. -/
theorem source_original_memory_MARKED_compressed_pair_norm434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ)) (s : Finset ℕ)
    (hclosed : ∀ (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st),
      s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈ H)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
    ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap
        patterns keep q rho Vs Vb mu Knu zeta theta o k st s F) X‖ ≤
    ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      ∑ t ∈ H,sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X s Y t * ‖F Y t‖ := by
  classical
  simp_rw [source_original_memory_MARKED_E_history_expansion434 SP smallMod BP bigMod
    J ell m cap patterns keep q rho Vs Vb mu Knu zeta theta o k H s hclosed]
  rw [source_original_memory_ORIGINAL_orbit_sum434]
  have hm := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
  rw [Finset.mul_sum,Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  exact source_original_memory_FILTERED_compressed_pair_norm434 SP smallMod BP bigMod
    J ell m cap patterns _ q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X (fun Y => F Y t)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFrameCleanDirty -/

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

/-- Exact original E frame row restricted by a predicate on the
LITERAL oriented choice, including its admissible OLD injection. -/
def sourceOriginalSourceEFrameFilteredRow434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℂ :=
  ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
    if h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
        sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f then
      let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
        (Classical.choose h)
      if keep x z then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
          (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
      else 0
    else 0

def sourceOriginalCleanChoice434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) : Prop :=
  (¬ ∃ g : BG, ((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
  (¬ ∃ g : BG, ((z.2.2.1.bigChoice g).2).1.Nonempty)

def sourceOriginalSourceEFrameCleanRow434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℂ :=
  sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta o k x seen F

def sourceOriginalSourceEFrameDirtyRow434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℂ :=
  sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta o k x seen F

/-- CLEAN and DIRTY partition the TRUE original E-frame carrier,
not a surrogate kernel. No sign, absolute norm or source hypothesis. -/
theorem source_original_FRAME_E_clean_dirty_split434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F +
    sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  classical
  unfold sourceOriginalSourceEFrameRow434 sourceOriginalSourceEFrameCleanRow434
    sourceOriginalSourceEFrameDirtyRow434 sourceOriginalSourceEFrameFilteredRow434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    by_cases hc : sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r (Classical.choose h))
    · simp [hc]
    · simp [hc]
  · simp [h]

/-- Exact signed linearity of the genuine filtered E row. -/
theorem source_original_FRAME_FILTERED_E_sub434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F G : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen (fun out st => F out st - G out st) =
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F -
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen G := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    by_cases hc : keep x (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
      (Classical.choose h))
    · simp [hc]; ring
    · simp [hc]
  · simp [h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalThetaDephasing -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem originalReturnPhase_zero434 (o k : ℤ) (D : ℕ) :
    originalReturnPhase 0 o k D = 1 := by
  simp [originalReturnPhase]

/-- The literal phase of the source physical E coefficient factors off
without replacing the complex RAW/comparison K or changing orientation. -/
theorem originalEdgeScalar_theta_dephase434
    (K : ℂ) (zeta theta : ℝ) (D : ℕ) (o k : ℤ) :
    originalEdgeScalar K zeta theta D o k =
      originalEdgeScalar K zeta 0 D o k *
        originalReturnPhase theta o k D := by
  simp only [originalEdgeScalar, originalReturnPhase_zero434, mul_one]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The TRUE physical source oriented E summand is a single Fourier
frequency. Its amplitude at theta=0 keeps the exact joint K, small
Haar and BIG branch factors. No positivity is used. -/
theorem source_oriented_PHYSICAL_coefficient_theta_dephase434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x z =
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta 0 o k x z *
    originalReturnPhase theta o k
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1) := by
  unfold sourceOrientedPhysicalCoefficient
  dsimp only
  rw [originalEdgeScalar_theta_dephase434]
  unfold Green64SmallHaar.groupPermutedKernel
  split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalMemoryMarkedCompressedL2 -/

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

/-- Conditional finite transfer for the literal history-marked E.
Only the already physical positive row/column estimates will be inserted
by applications; history counts never enter the constant. -/
theorem source_original_memory_MARKED_compressed_L2_transfer434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ))
    (hclosed : ∀ s ∈ H,∀ (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st),
      s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈ H)
    (src dst : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Prop)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hr : ∀ X,src X →
      (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X))
    (hc : ∀ Y,dst Y →
      (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
      D*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,∑ s ∈ H,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
      ‖(if src X then fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k st s
          (fun Y t => if dst Y then F Y t else 0)) X else 0)‖^2) ≤
    C*D*(∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,∑ t ∈ H,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y)*‖F Y t‖^2) := by
  classical
  let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
  let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
  let A := sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
    patterns keep q rho Vs Vb mu Knu zeta theta o k
  let B := sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap
    patterns keep q rho Vs Vb mu Knu zeta theta o k
  let At := fun X Y => if src X ∧ dst Y then A X Y else 0
  let Bt := fun X s Y t => if src X ∧ dst Y then B X s Y t else 0
  let T := fun X s => if src X then
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st s
        (fun Y t => if dst Y then F Y t else 0)) X else 0
  have hM (X) : 0 ≤ M X := source_original_memory_FULL_density_orbit_nonneg434
    SP smallMod BP bigMod J ell cap Vs Vb mu hVs hVb hmu X
  have hA (X Y) : 0 ≤ A X Y := source_original_memory_FILTERED_density_pair_nonneg434
    SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X Y
  have hB (X s Y t) : 0 ≤ B X s Y t := source_original_memory_MARKED_pair_nonneg434
    SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X s Y t
  have hAt (X Y) : 0 ≤ At X Y := by
    dsimp only [At];split_ifs <;> first | exact hA X Y | exact le_rfl
  have hBt (X s Y t) : 0 ≤ Bt X s Y t := by
    dsimp only [Bt];split_ifs <;> first | exact hB X s Y t | exact le_rfl
  have hbr (X s Y) : (∑ t ∈ H,Bt X s Y t) ≤ At X Y := by
    by_cases h : src X ∧ dst Y
    · simp only [At,Bt,if_pos h]
      exact source_original_memory_MARKED_pair_history_row434 SP smallMod BP bigMod
        J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k H X Y s
    · simp only [At,Bt,if_neg h,Finset.sum_const_zero,le_refl]
  have hbc (X Y t) : (∑ s ∈ H,Bt X s Y t) ≤ At X Y := by
    by_cases h : src X ∧ dst Y
    · simp only [At,Bt,if_pos h]
      exact source_original_memory_MARKED_pair_history_column434 SP smallMod BP bigMod
        J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k H X Y t
    · simp only [At,Bt,if_neg h,Finset.sum_const_zero,le_refl]
  have hr' (X) (_hX : X ∈ S) : (∑ Y ∈ S,At X Y) ≤ C*M X := by
    by_cases hx : src X
    · apply le_trans _ (hr X hx)
      apply Finset.sum_le_sum
      intro Y hY
      dsimp only [At]
      split_ifs <;> first | exact le_rfl | exact hA X Y
    · simp only [At,hx,false_and,ite_false,Finset.sum_const_zero]
      exact mul_nonneg hC (hM X)
  have hc' (Y) (_hY : Y ∈ S) : (∑ X ∈ S,At X Y) ≤ D*M Y := by
    by_cases hy : dst Y
    · apply le_trans _ (hc Y hy)
      apply Finset.sum_le_sum
      intro X hX
      dsimp only [At]
      split_ifs <;> first | exact le_rfl | exact hA X Y
    · simp only [At,hy,and_false,ite_false,Finset.sum_const_zero]
      exact mul_nonneg hD (hM Y)
  have ht (X) (_hX : X ∈ S) (s) (hs : s ∈ H) :
      M X*‖T X s‖ ≤ ∑ Y ∈ S,∑ t ∈ H,Bt X s Y t*‖F Y t‖ := by
    by_cases hx : src X
    · simp only [T,if_pos hx]
      have hh := source_original_memory_MARKED_compressed_pair_norm434
        SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu
        Knu zeta theta o k H s (hclosed s hs) X (fun Y t => if dst Y then F Y t else 0)
      apply hh.trans_eq
      apply Finset.sum_congr rfl
      intro Y hY
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hy : dst Y
      · simp only [Bt,B,hx,hy,true_and,ite_true]
      · simp only [Bt,B,hy,and_false,ite_false,norm_zero,mul_zero,zero_mul]
    · simp only [T,Bt,hx,false_and,ite_false,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero,le_refl]
  exact source_original_birth_history_density_energy434 S H M hM At hAt Bt hBt
    hbr hbc C D hC hr' hc' F T ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBirthPool -/

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

/-- Ambient set consists of numerical prime VALUES across all BIG groups. -/
def sourceOriginalMemoryBirthPool434 : Finset ℕ :=
  Finset.univ.biUnion (fun g : BG => Finset.univ.image (bigMod g))

theorem source_original_memory_E_births_subset_pool434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) :
    (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ⊆
      sourceOriginalMemoryBirthPool434 BP bigMod := by
  classical
  intro p hp
  simp only [orientedEFreshBirths,List.mem_toFinset,List.mem_flatMap,List.mem_map,
    Finset.mem_toList] at hp
  rcases hp with ⟨g,hg,j,hj,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨(z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g j),Finset.mem_univ _,rfl⟩⟩

theorem source_original_memory_E_history_closed434
    (s : Finset ℕ) (hs : s ∈ (sourceOriginalMemoryBirthPool434 BP bigMod).powerset)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) :
    s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈
      (sourceOriginalMemoryBirthPool434 BP bigMod).powerset := by
  apply Finset.mem_powerset.mpr
  exact Finset.union_subset (Finset.mem_powerset.mp hs)
    (source_original_memory_E_births_subset_pool434 SP smallMod BP bigMod J ell m cap patterns st z)

theorem source_original_memory_G_births_subset_pool434
    (M : ℕ) (st : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap st) :
    (physicalGhostFreshBirths SP smallMod BP bigMod M cap st c).toFinset ⊆
      sourceOriginalMemoryBirthPool434 BP bigMod := by
  classical
  intro p hp
  simp only [physicalGhostFreshBirths,List.mem_toFinset,List.mem_flatMap,List.mem_map,
    Finset.mem_toList] at hp
  rcases hp with ⟨g,hg,z,hz,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨z.1,Finset.mem_univ _,rfl⟩⟩

theorem source_original_memory_G_history_closed434
    (M : ℕ) (s : Finset ℕ) (hs : s ∈ (sourceOriginalMemoryBirthPool434 BP bigMod).powerset)
    (st : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap st) :
    s ∪ (physicalGhostFreshBirths SP smallMod BP bigMod M cap st c).toFinset ∈
      (sourceOriginalMemoryBirthPool434 BP bigMod).powerset := by
  apply Finset.mem_powerset.mpr
  exact Finset.union_subset (Finset.mem_powerset.mp hs)
    (source_original_memory_G_births_subset_pool434 SP smallMod BP bigMod cap M st c)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedHistoryEnvelope -/

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

/-- A physical envelope uniform in history dominates the marked row
without counting histories. This is the bridge needed for terminal
observables (including birth parity) with bounded history dependence. -/
theorem source_original_memory_MARKED_compressed_history_envelope434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ)) (s : Finset ℕ)
    (hclosed : ∀ (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st),
      s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈ H)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (f : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (hf : ∀ Y,∀ t ∈ H,‖F Y t‖ ≤ ‖f Y‖) :
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
    ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st s F) X‖ ≤
    ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X Y * ‖f Y‖ := by
  apply (source_original_memory_MARKED_compressed_pair_norm434 SP smallMod BP bigMod
    J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k H s hclosed X F).trans
  apply Finset.sum_le_sum
  intro Y hY
  calc
    _ ≤ ∑ t ∈ H,sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X s Y t * ‖f Y‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hf Y t ht)
        (source_original_memory_MARKED_pair_nonneg434 SP smallMod BP bigMod
          J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X s Y t)
    _ = (∑ t ∈ H,sourceOriginalMemoryMarkedDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X s Y t) * ‖f Y‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (source_original_memory_MARKED_pair_history_row434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k H X Y s) (norm_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedSelectorL2 -/

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

/-- Literal marked E evaluated at any admissible source-history selector.
A physical envelope uniform in the target history gives physical L2 control
without the counting norm of the terminal history observable. -/
theorem source_original_memory_MARKED_SELECTOR_compressed_L2_transfer434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (H : Finset (Finset ℕ))
    (hclosed : ∀ s ∈ H,∀ (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st),
      s ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset ∈ H)
    (src dst : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Prop)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hr : ∀ X,src X →
      (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X))
    (hc : ∀ Y,dst Y →
      (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
      D*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (f : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (seen : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ)
    (hseen : ∀ X,seen X ∈ H)
    (hf : ∀ Y,∀ t ∈ H,‖F Y t‖ ≤ ‖f Y‖) :
    (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
      ‖(if src X then fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
          keep q rho Vs Vb mu Knu zeta theta o k st (seen X)
          (fun Y t => if dst Y then F Y t else 0)) X else 0)‖^2) ≤
    C*D*(∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y)*‖f Y‖^2) := by
  classical
  let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
  let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
  let A := sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
    patterns keep q rho Vs Vb mu Knu zeta theta o k
  let At := fun X Y => if src X ∧ dst Y then A X Y else 0
  let T := fun X => if src X then
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st (seen X)
        (fun Y t => if dst Y then F Y t else 0)) X else 0
  have hM (X) : 0 ≤ M X := source_original_memory_FULL_density_orbit_nonneg434
    SP smallMod BP bigMod J ell cap Vs Vb mu hVs hVb hmu X
  have hA (X Y) : 0 ≤ A X Y := source_original_memory_FILTERED_density_pair_nonneg434
    SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X Y
  have hAt (X Y) : 0 ≤ At X Y := by
    dsimp only [At];split_ifs <;> first | exact hA X Y | exact le_rfl
  have hr' (X) (_hX : X ∈ S) : (∑ Y ∈ S,At X Y) ≤ C*M X := by
    by_cases hx : src X
    · apply le_trans _ (hr X hx)
      apply Finset.sum_le_sum
      intro Y hY
      dsimp only [At]
      split_ifs <;> first | exact le_rfl | exact hA X Y
    · simp only [At,hx,false_and,ite_false,Finset.sum_const_zero]
      exact mul_nonneg hC (hM X)
  have hc' (Y) (_hY : Y ∈ S) : (∑ X ∈ S,At X Y) ≤ D*M Y := by
    by_cases hy : dst Y
    · apply le_trans _ (hc Y hy)
      apply Finset.sum_le_sum
      intro X hX
      dsimp only [At]
      split_ifs <;> first | exact le_rfl | exact hA X Y
    · simp only [At,hy,and_false,ite_false,Finset.sum_const_zero]
      exact mul_nonneg hD (hM Y)
  have ht (X) (_hX : X ∈ S) :
      M X*‖T X‖ ≤ ∑ Y ∈ S,At X Y*‖f Y‖ := by
    by_cases hx : src X
    · simp only [T,if_pos hx]
      have hh := source_original_memory_MARKED_compressed_history_envelope434
        SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu
        Knu zeta theta o k H (seen X) (hclosed (seen X) (hseen X)) X
        (fun Y t => if dst Y then F Y t else 0)
        (fun Y => if dst Y then f Y else 0)
        (by
          intro Y t ht
          by_cases hy : dst Y
          · simp only [if_pos hy];exact hf Y t ht
          · simp only [if_neg hy,le_refl])
      apply hh.trans_eq
      apply Finset.sum_congr rfl
      intro Y hY
      by_cases hy : dst Y
      · simp only [At,A,hx,hy,true_and,ite_true]
      · simp only [At,A,hy,and_false,ite_false,norm_zero,mul_zero,zero_mul]
    · simp only [T,At,hx,false_and,ite_false,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero,le_refl]
  exact source_original_finite_density_kernel_energy434 S M hM At hAt C D hC hr' hc' f T ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalStoreOnlyColumn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- Applicable logarithmically small weighted column of the literal
store-only original E. The OLD restriction is on the TARGET orbit.
The original RAW+canonical joint K is retained; its transposed promotion
row is proved separately from the same physical hypotheses and budget.
No smallness, row, column, Gram or operator assumption remains. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_store_only_column_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
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
      (y : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell))
      (hOldTarget : (∑ g : G,(y.2 g).2.card) ≤ Nat.ceil (L^2)),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalFilteredDensityColumn434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      (fun _ z => (¬ ∃ g : G,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : G,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho data.Vsmall data.Vbig mu
      (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q hA hB xi) zeta theta o k y ≤
    L^(-B) * (physicalOrbitMass
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      (J+ell) cap data.Vsmall mu y *
      sourceOriginalMemorySectorDensity434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell data.Vbig y) := by
  dsimp only
  let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
  have hRow := source_original_memory_PHYSICAL_TRANSPOSE_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 B hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hRow.1,?_⟩
  filter_upwards [hRow.2,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hrow hVisit
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk y hOldTarget
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  apply source_original_memory_STORE_ONLY_density_column_of_reverse_row434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell m cap
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta o k y (L^(-B))
  intro st hx
  have hOld : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) := by
    have hp := source_original_memory_PAIR_OLD_projection434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      BP (fun _ p => p.val) J ell cap st
    rw [hx] at hp
    exact hp ▸ hOldTarget
  exact hrow x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower hHarmonic
    hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB
    zeta theta (-o) k (by omega) hk0 hk
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryStoreOnlyCompressedL2 -/

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

theorem source_original_memory_FILTERED_density_pair_le_full434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      keep q rho Vs Vb mu Knu zeta theta o k X Y ≤
    sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k X Y := by
  apply Finset.sum_le_sum
  intro st hst
  apply mul_le_mul_of_nonneg_left _
    (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st)
  apply Finset.sum_le_sum
  intro z hz
  split_ifs <;> first | exact le_rfl | exact norm_nonneg _ | tauto

theorem source_original_memory_FULL_pair_source_sum434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k X Y) =
    sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k Y := by
  have hh := source_original_memory_FILTERED_pair_source_sum434 SP smallMod BP bigMod
    J ell m cap patterns (fun _ _ => True) q rho Vs Vb mu Knu zeta theta o k Y
  simpa only [sourceOriginalMemoryOriginalFilteredDensityPair434,
    sourceOriginalMemoryOriginalDensityPair434,sourceOriginalMemoryOriginalFilteredDensityColumn434,
    sourceOriginalMemoryOriginalDensityColumn434,and_true] using hh

/-- Complete weighted orbit-row bound obtained from the proved exact
original reversal. The actual transposed complete column is the only
analytic input to this finite transfer. -/
theorem source_original_memory_FILTERED_pair_row_of_transpose_column434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
    sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k X := by
  calc
    _ ≤ ∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k X Y :=
      Finset.sum_le_sum (fun Y _ => source_original_memory_FILTERED_density_pair_le_full434
        SP smallMod BP bigMod J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu
          Knu zeta theta o k X Y)
    _ = _ := by
      simp_rw [source_original_memory_ORIGINAL_density_pair_reverse434 SP smallMod BP bigMod
        J ell m cap patterns q rho Vs Vb mu hmu hVb hr Knu zeta theta o k X]
      exact source_original_memory_FULL_pair_source_sum434 SP smallMod BP bigMod
        J ell m cap patterns q rho Vs Vb mu _ zeta theta (-o) k X

/-- Signed STORE-ONLY on the actual Fock orbit compression, with an
explicit target projector. Both premises are discharged by the physical
theorem; no uncompressed per-history estimate is used. -/
theorem source_original_memory_STORE_ONLY_compressed_L2_transfer434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (eligible : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Prop)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfull : ∀ X,sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k X ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X))
    (hstore : ∀ Y,eligible Y →
      sourceOriginalMemoryOriginalFilteredDensityColumn434 SP smallMod BP bigMod J ell m cap patterns
        (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
          (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
        q rho Vs Vb mu Knu zeta theta o k Y ≤
      D*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    (∑ X ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) *
      ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (fun Y => if eligible Y then F Y else 0)) X‖^2) ≤
    C*D*(∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb Y)*‖F Y‖^2) := by
  classical
  let keep := fun (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) =>
    (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty)
  let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
  let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
  let A := sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap
    patterns keep q rho Vs Vb mu Knu zeta theta o k
  let At := fun X Y => if eligible Y then A X Y else 0
  let T := fun X => fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
    (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st (fun Y => if eligible Y then F Y else 0)) X
  have hM (X) : 0 ≤ M X := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  have hA (X Y) : 0 ≤ A X Y := source_original_memory_FILTERED_density_pair_nonneg434 SP smallMod BP bigMod
    J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X Y
  have hAt (X Y) : 0 ≤ At X Y := by
    dsimp only [At]
    split_ifs <;> first | exact hA X Y | exact le_rfl
  have hrow (X) (hX : X ∈ S) : (∑ Y ∈ S,At X Y) ≤ C*M X := by
    calc
      _ ≤ ∑ Y ∈ S,A X Y := Finset.sum_le_sum (fun Y _ => by
        dsimp only [At]
        split_ifs <;> first | exact le_rfl | exact hA X Y)
      _ ≤ _ := (source_original_memory_FILTERED_pair_row_of_transpose_column434 SP smallMod BP bigMod
        J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu hr Knu zeta theta o k X).trans (hfull X)
  have hcol (Y) (hY : Y ∈ S) : (∑ X ∈ S,At X Y) ≤ D*M Y := by
    by_cases he : eligible Y
    · simp only [At,if_pos he]
      rw [source_original_memory_FILTERED_pair_source_sum434]
      exact hstore Y he
    · simp only [At,if_neg he,Finset.sum_const_zero]
      exact mul_nonneg hD (hM Y)
  have ht (X) (hX : X ∈ S) : M X*‖T X‖ ≤ ∑ Y ∈ S,At X Y*‖F Y‖ := by
    have hh := source_original_memory_FILTERED_compressed_pair_norm434 SP smallMod BP bigMod
      J ell m cap patterns keep q rho Vs Vb mu hVs hVb hmu Knu zeta theta o k X
        (fun Y => if eligible Y then F Y else 0)
    dsimp only [keep] at hh
    simp_rw [source_original_memory_STORE_ONLY_filtered_E434] at hh
    apply hh.trans_eq
    apply Finset.sum_congr rfl
    intro Y hY
    by_cases he : eligible Y
    · simp only [At,he,ite_true,A,keep]
    · simp only [At,he,ite_false,norm_zero,mul_zero,zero_mul]
  exact source_original_finite_density_kernel_energy434 S M hM At hAt C D hC hrow hcol F T ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalCompressedStoreOnlyL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Applicable L2 saving for the LITERAL signed store-only operator
under its original Fock orbit compression. The target TOTAL OLD
projector is explicit. No hypothetical kernel, column, row, Gram or
smallness input remains. J is chosen after fixed conductor and retention
losses, and the eventual threshold precedes every moving physical datum. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_compressed_store_only_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Bcolumn := 2*B+Ccol
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
      ‖fullPhysicalOrbitAverage
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        (J+ell) cap data.Vsmall mu
        (fun st => sourceOriginalMemoryOriginalEStoreOnly434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st
          (fun y => if (∑ g : G,(y.2 g).2.card) ≤ Nat.ceil (L^2) then F y else 0)) X‖^2) ≤
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
  let Bcolumn := 2*B+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Bcolumn+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hStore := source_original_memory_PHYSICAL_ORIGINAL_E_store_only_column_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Bcolumn hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hStore.1,?_⟩
  filter_upwards [hStore.2,
    eventually_source_original_memory_PHYSICAL_TRANSPOSE_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hstore hfull hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
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
  have hh := source_original_memory_STORE_ONLY_compressed_L2_transfer434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell m cap
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho data.Vsmall data.Vbig mu hVs hVb hmu hr.le
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi)
    zeta theta o k (fun y => (∑ g : G,(y.2 g).2.card) ≤ Nat.ceil (L^2))
    (L^Ccol) (L^(-Bcolumn)) (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _)
    (fun X => hfull x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
      blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta (-o) k X)
    (fun y hy => hstore x Y Hprime data sep m hm hmJ cap hSmallUpper hBigLower hHarmonic
      hSmallGroupsLower blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB
      zeta theta o k ho hk0 hk y hy) F
  rw [← Real.rpow_add hLp,show Ccol+ -Bcolumn= -(2*B) by dsimp only [Bcolumn];ring] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro X hX
  congr 4
  funext st
  congr 1
  funext y
  by_cases hy : (∑ g : G,(y.2 g).2.card) ≤ Nat.ceil (L^2)
  · simp only [hy,ite_true]
  · simp only [hy,ite_false]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryProjectedDirtyEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_memory_ORIGINAL_orbit_add434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F G : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu (fun st => F st+G st) X =
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F X +
      fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu G X := by
  unfold fullPhysicalOrbitAverage
  simp only [mul_add,Finset.sum_add_distrib,add_div]

/-- TOTAL OLD is an actual Fock-orbit observable, so its projector
commutes exactly with the original physical conditional expectation. -/
theorem source_original_memory_ORIGINAL_orbit_OLD_project434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (H : ℕ)
    (F : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => if (∑ g : BG,(st.2 g).2.1.val) ≤ H then F st else 0) X =
    if (∑ g : BG,(X.2 g).2.card) ≤ H then
      fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F X else 0 := by
  classical
  have he (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X) :
      (∑ g : BG,(st.2 g).2.1.val) = ∑ g : BG,(X.2 g).2.card := by
    rw [← source_original_memory_PAIR_OLD_projection434 SP smallMod BP bigMod J ell cap st,hx]
  unfold fullPhysicalOrbitAverage
  by_cases hx : (∑ g : BG,(X.2 g).2.card) ≤ H
  · rw [if_pos hx]
    congr 1
    apply Finset.sum_congr rfl
    intro st hst
    dsimp only
    rw [he st (Finset.mem_filter.mp hst).2,if_pos hx]
  · rw [if_neg hx]
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro st hst
    dsimp only
    rw [he st (Finset.mem_filter.mp hst).2,if_neg hx,mul_zero]

/-- Literal signed (full original E minus original CLEAN), compressed
with the ORIGINAL orbit average and explicit TOTAL OLD projectors on
both ends. No definition of E, CLEAN, K or the vacuum root is changed. -/
def sourceOriginalMemoryCompressedProjectedDirty434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℂ :=
  let PF := fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0
  fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
    (fun st => if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
      fullSourceOrientedPhysicalE SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st PF -
      sourceOriginalMemoryOriginalEClean434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st PF else 0) X

theorem source_original_memory_PROJECTED_DIRTY_split434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    let PF := fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0
    sourceOriginalMemoryCompressedProjectedDirty434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k H F X =
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
        sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st PF else 0) X +
    if (∑ g : BG,(X.2 g).2.card) ≤ H then
      fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st PF) X else 0 := by
  classical
  dsimp only
  unfold sourceOriginalMemoryCompressedProjectedDirty434
  have he (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      (if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
        fullSourceOrientedPhysicalE SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0) -
        sourceOriginalMemoryOriginalEClean434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0)
      else 0) =
      (if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
        sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0)
      else 0) +
      (if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
        sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0)
      else 0) := by
    by_cases hs : (∑ g : BG,(st.2 g).2.1.val) ≤ H
    · simp only [if_pos hs]
      rw [source_original_memory_ORIGINAL_E_CLEAN_DIRTY_split434]
      ring
    · simp only [if_neg hs,add_zero]
  simp_rw [he]
  rw [source_original_memory_ORIGINAL_orbit_add434]
  simp_rw [source_original_memory_ORIGINAL_orbit_OLD_project434]

/-- Complete signed DIRTY energy is controlled by its two disjoint
actual components, with the exact factor two in the square inequality.
This is before inserting their already physical logarithmic bounds. -/
theorem source_original_memory_PROJECTED_DIRTY_energy_components434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    let PF := fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0
    let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
    let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
    (∑ X ∈ S,M X*‖sourceOriginalMemoryCompressedProjectedDirty434 SP smallMod BP bigMod
      J ell m cap patterns q rho Vs Vb mu Knu zeta theta o k H F X‖^2) ≤
    2*(∑ X ∈ S,M X*‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
        sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st PF else 0) X‖^2) +
    2*(∑ X ∈ S,M X*‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st PF) X‖^2) := by
  classical
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X hX
  have hm := source_original_memory_FULL_density_orbit_nonneg434 SP smallMod BP bigMod
    J ell cap Vs Vb mu hVs hVb hmu X
  rw [source_original_memory_PROJECTED_DIRTY_split434]
  have hn (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
    nlinarith only [hs,sq_nonneg (‖a‖-‖b‖)]
  by_cases hx : (∑ g : BG,(X.2 g).2.card) ≤ H
  · rw [if_pos hx]
    exact (mul_le_mul_of_nonneg_left (hn _ _) hm).trans_eq (by ring)
  · rw [if_neg hx,add_zero]
    nlinarith only [mul_nonneg hm (sq_nonneg
      ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st
          (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0)) X‖),
      mul_nonneg hm (sq_nonneg
      ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
        (fun st => if (∑ g : BG,(st.2 g).2.1.val) ≤ H then
          sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
            q rho Vs Vb mu Knu zeta theta o k st
            (fun Y => if (∑ g : BG,(Y.2 g).2.card) ≤ H then F Y else 0) else 0) X‖)]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryMarkedProjectedComponents -/

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

/-- The actual filtered orbit-row inherits a bound on its physical
source fibre with its TRUE orbit density. -/
theorem source_original_memory_FILTERED_pair_row_of_row434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (R : ℝ)
    (hrow : ∀ st,physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X →
      sourceOriginalMemoryOriginalFilteredRow434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st ≤ R) :
    (∑ Y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k X Y) ≤
    R*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X) := by
  classical
  rw [source_original_memory_FILTERED_pair_target_sum434]
  have hm :
      (∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X then
          sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st else 0) =
      physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X := by
    have hh := source_original_memory_sector_density_orbit_mass434 SP smallMod BP bigMod J ell cap Vs Vb mu X
    simp only [Finset.sum_filter] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro st hst
    by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X
    · simp only [hx,ite_true,sourceOriginalMemoryFullDensityMass434]
    · simp only [hx,ite_false]
  rw [← hm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro st hst
  by_cases hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X
  · rw [if_pos hx,if_pos hx]
    exact (mul_le_mul_of_nonneg_left (hrow st hx)
      (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
        J ell cap Vs Vb mu hVs hVb hmu st)).trans_eq (mul_comm _ _)
  · rw [if_neg hx,if_neg hx,mul_zero]

/-- Both original TOTAL OLD projectors, the original orbit average,
and the unchanged witness-level global birth marker. -/
def sourceOriginalMemoryMarkedProjectedE434
    (keep : (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) →
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (X : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (s : Finset ℕ) : ℂ :=
  if (∑ g : BG,(X.2 g).2.card) ≤ H then
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP smallMod BP bigMod J ell m cap patterns
        keep q rho Vs Vb mu Knu zeta theta o k st s
        (fun Y t => @ite ℂ ((∑ g : BG,(Y.2 g).2.card) ≤ H) (Classical.propDecidable _) (F Y t) 0)) X else 0

theorem source_original_memory_MARKED_projected_components_L2434
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
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    let S := physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap
    let Hist := (sourceOriginalMemoryBirthPool434 BP bigMod).powerset
    let M := fun X => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu X *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb X
    let En := fun f => ∑ X ∈ S,∑ s ∈ Hist,M X*‖f X s‖^2
    En (sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      q rho Vs Vb mu Knu zeta theta o k H F) ≤ R*C*En F ∧
    En (sourceOriginalMemoryMarkedProjectedE434 SP smallMod BP bigMod J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      q rho Vs Vb mu Knu zeta theta o k H F) ≤ C*R*En F := by
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
  have hp := source_original_memory_MARKED_compressed_L2_transfer434
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
        Knu zeta theta o k X Y) F
  have hs := source_original_memory_MARKED_compressed_L2_transfer434
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
      exact hstore Y hy) F
  constructor
  · simpa only [sourceOriginalMemoryMarkedProjectedE434,prom,eligible] using hp
  · simpa only [sourceOriginalMemoryMarkedProjectedE434,store,eligible] using hs
end Green64Analytic.CorrelationSquare

end

end

