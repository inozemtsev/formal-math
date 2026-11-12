module

public import Green64.Library.Weights.Part042
public import Green64.Library.Correlation.Part001
public import Mathlib.Logic.Equiv.Prod
public import Green64.Library.Weights.Part038
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Green64.Library.Weights.Part023
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Weights / Part043

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceSharedFamilyEquiv -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 8500000

/-- The literal product-of-finite-list supports, not an independent copy
with changed coefficients or a count-only surrogate. -/
noncomputable def sourceFiniteListFamilyEquiv434
    {G : Type} [Fintype G] [DecidableEq G] {A : G → Type}
    [∀ g, DecidableEq (A g)] (F : ∀ g, Finset (A g)) :
    (↑(Fintype.piFinset F)) ≃ (∀ g, ↑(F g)) where
  toFun a g := ⟨a.val g,(Fintype.mem_piFinset.mp a.property) g⟩
  invFun b := ⟨fun g => (b g).val,Fintype.mem_piFinset.mpr (fun g => (b g).property)⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by funext g; rfl

/-- Full original physical marked tuples at the global shared position. -/
noncomputable def sourceGlobalSharedCompletions434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (shared : ∀ g, E g → ℕ) (w : ℕ) : Finset (G → Fin M → ℕ) :=
  Fintype.piFinset (fun g =>
    (orderedBigMarks (P g) M ((∏ p ∈ Finset.univ.biUnion
      (fun h => sourceSharedPrimeSet434 (E h) (shared h)),p)*w)).filter
        (fun a => ∀ i : E g, a i=shared g i))

theorem source_global_shared_completions_eq434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (shared : ∀ g, E g → ℕ) (w : ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hs : ∀ g i, shared g i ∈ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) :
    sourceGlobalSharedCompletions434 P M E shared w =
      Fintype.piFinset (fun g => sourceSharedCompletions434 (P g) M (E g) (shared g) w) := by
  classical
  have hRP : ∀ g, sourceSharedPrimeSet434 (E g) (shared g) ⊆ P g := by
    intro g p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hs g i
  unfold sourceGlobalSharedCompletions434 sourceSharedCompletions434
  congr 1
  funext g
  rw [source_group_marks_global_shared434 P _ hP hRP hDisj g M w]

/-- Exact finite-family reindex for arbitrary coupled source tests. -/
theorem source_global_shared_family_sum434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (shared : ∀ g, E g → ℕ) (t : G → ℕ)
    (e : ∀ g, Fin (t g) ≃ {i : Fin M // i ∉ E g}) (w : ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hs : ∀ g i, shared g i ∈ P g)
    (hInj : ∀ g, Function.Injective (shared g))
    (hAvoid : ∀ g i, ¬shared g i ∣ w)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h)
    (K : (G → Fin M → ℕ) → ℂ) :
    (∑ a ∈ sourceGlobalSharedCompletions434 P M E shared w,K a) =
      ∑ b ∈ bigMarkLists P t w,K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g)) := by
  classical
  rw [source_global_shared_completions_eq434 P M E shared w hP hs hDisj]
  let F := fun g => sourceSharedCompletions434 (P g) M (E g) (shared g) w
  let B := fun g => orderedBigMarks (P g) (t g) w
  let eqv := (sourceFiniteListFamilyEquiv434 F).trans
    ((Equiv.piCongrRight (fun g => sourceSharedCompletionEquiv434 (P g) (E g)
      (shared g) (e g) w (hP g) (hs g) (hInj g) (hAvoid g))).trans
        (sourceFiniteListFamilyEquiv434 B).symm)
  let asm := fun b : (g : G) → Fin (t g) → ℕ =>
    fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g)
  have hh := Fintype.sum_equiv eqv.symm
    (fun b => K (asm b.val)) (fun a => K a.val) (fun b => rfl)
  calc
    _ = ∑ a : ↑(Fintype.piFinset F), K a.val := (Finset.sum_coe_sort _ K).symm
    _ = ∑ b : ↑(Fintype.piFinset B), K (asm b.val) := hh.symm
    _ = _ := Finset.sum_coe_sort _ (fun b => K (asm b))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyRestriction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Actual physical completions still restrict to unshared divisors
when shared primes divide the endpoint. No clean condition is assumed. -/
theorem source_global_dirty_restrict_mem434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g}) (w : ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime) (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (a : G → Fin M → ℕ) (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w) :
    (fun g j => a g (e g j)) ∈ bigMarkLists P t w := by
  classical
  rw [source_global_shared_completions_eq434 P M E s w hP hs hDisj] at ha
  apply Fintype.mem_piFinset.mpr
  intro g
  exact source_shared_restrict_mem434 (P g) (E g) (s g) (e g) w (hP g) (hs g)
    (a g) ((Fintype.mem_piFinset.mp ha) g)

/-- Restriction is injective on real physical rows, even in the dirty
case. Hence no extra multiplicity occurs when bounding their mass. -/
theorem source_global_dirty_restrict_inj434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g}) (w : ℕ) :
    Set.InjOn (fun a : G → Fin M → ℕ => fun g j => a g (e g j))
      (↑(sourceGlobalSharedCompletions434 P M E s w)) := by
  classical
  intro a ha b hb hab
  have ha' := Fintype.mem_piFinset.mp ha
  have hb' := Fintype.mem_piFinset.mp hb
  funext g i
  by_cases hi : i ∈ E g
  · exact ((Finset.mem_filter.mp (ha' g)).2 ⟨i,hi⟩).trans
      ((Finset.mem_filter.mp (hb' g)).2 ⟨i,hi⟩).symm
  · have h := congrFun (congrFun hab g) ((e g).symm ⟨i,hi⟩)
    simpa only [Equiv.apply_symm_apply] using h

/-- Weighted actual dirty-row restriction, not merely a comparison
of list cardinalities. The target weight can couple all groups. -/
theorem source_global_dirty_weighted_sum_le434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g}) (w : ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime) (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (F : (G → Fin M → ℕ) → ℂ) (W : (∀ g,Fin (t g) → ℕ) → ℝ)
    (hW : ∀ b ∈ bigMarkLists P t w,0 ≤ W b)
    (hF : ∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ‖F a‖ ≤ W (fun g j => a g (e g j))) :
    ‖∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,F a‖ ≤
      ∑ b ∈ bigMarkLists P t w,W b := by
  classical
  let A := sourceGlobalSharedCompletions434 P M E s w
  let restr := fun a : G → Fin M → ℕ => fun g j => a g (e g j)
  have hSub : A.image restr ⊆ bigMarkLists P t w := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact source_global_dirty_restrict_mem434 P M E s t e w hP hs hDisj a ha
  calc
    _ ≤ ∑ a ∈ A,‖F a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ A,W (restr a) := Finset.sum_le_sum hF
    _ = ∑ b ∈ A.image restr,W b := by
      rw [Finset.sum_image (source_global_dirty_restrict_inj434 P M E s t e w)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSub (fun b hb _ => hW b hb)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryPhysicalCollisionDivisor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- A collision with one of the actual NONSHARED original physical
marked slots forces p to divide the STRIPPED source integer w.
This remains true if shared labels overlap an endpoint divisor,
since the exact physical completion still injects into the
original free marked list (no clean assumption is needed). -/
theorem source_auxiliary_physical_free_mark_dvd434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (w p : ℕ)
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (a : G → Fin M → ℕ)
    (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w)
    (g : G) (j : Fin (t g))
    (hColl : a g (e g j)=p) : p ∣ w := by
  have hRestr := source_global_dirty_restrict_mem434
    P M E s t e w hP hs hDisj a ha
  have hGroup := (Fintype.mem_piFinset.mp hRestr) g
  have hDiv := (source_ordered_marks_mem434 (P g) (t g) w
    (fun j => a g (e g j))).mp hGroup
  simpa only [hColl] using (hDiv.1 j).2

/-- The true ORIGINAL auxiliary free label p divides the
stripped source integer whenever it hits either unshared physical
endpoint list. The target is the genuine SIGNED shift by k*p*D,
and no independent divisibility of the two endpoints is assumed. -/
theorem source_auxiliary_physical_either_end_dvd434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p w D : ℕ) (k : ℤ)
    (hShift : 0 < (w:ℤ)+k*(p*D:ℕ))
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (a b : G → Fin M → ℕ)
    (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w)
    (hb : b ∈ sourceGlobalSharedCompletions434 P M E s
      (((w:ℤ)+k*(p*D:ℕ)).toNat))
    (hCollision : (∃ g j,a g (e g j)=p) ∨
      (∃ g j,b g (e g j)=p)) : p ∣ w := by
  rcases hCollision with hSource | hTarget
  · obtain ⟨g,j,hj⟩ := hSource
    exact source_auxiliary_physical_free_mark_dvd434
      P M E s t e w p hP hs hDisj a ha g j hj
  · obtain ⟨g,j,hj⟩ := hTarget
    have hDivTarget := source_auxiliary_physical_free_mark_dvd434
      P M E s t e (((w:ℤ)+k*(p*D:ℕ)).toNat) p
      hP hs hDisj b hb g j hj
    have hCast : (((w:ℤ)+k*(p*D:ℕ)).toNat) =
      (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat) := by
      simp only [Nat.cast_mul,mul_assoc]
    have hPos : 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) := by
      simpa only [Nat.cast_mul,mul_assoc] using hShift
    exact (source_auxiliary_shift_divisibility434 p w D k hPos).mp
      (hCast ▸ hDivTarget)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryPhysicalCollisionCharge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Literal source03 two-end physical marked completions, restricted
to the event that the auxiliary free prime p hits one of the
NONSHARED source or target marks. An arbitrary coupled Fmark
preserves the true pattern coefficient K_nu and both endpoint tests. -/
noncomputable def sourceAuxiliaryPhysicalCollisionMask434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p w wp : ℕ)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) : ℂ :=
  ∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
      if (∃ g j,a g (e g j)=p) ∨ (∃ g j,b g (e g j)=p)
      then Fmark a b else 0

/-- A physical free auxiliary-label collision cannot occur unless p
divides the STRIPPED source integer w. The same holds for hits at the
target endpoint, even when k<0. This eliminates the illicit
assumption that the physical collision event is independent of p. -/
theorem source_auxiliary_physical_collision_zero_off_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p w D : ℕ) (k : ℤ)
    (hShift : 0 < (w:ℤ)+k*(p*D:ℕ))
    (hNo : ¬p ∣ w)
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    sourceAuxiliaryPhysicalCollisionMask434 P M E s t e p w
      (((w:ℤ)+k*(p*D:ℕ)).toNat) Fmark = 0 := by
  classical
  unfold sourceAuxiliaryPhysicalCollisionMask434
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hNot : ¬((∃ g j,a g (e g j)=p) ∨
      (∃ g j,b g (e g j)=p)) := by
    intro hCollision
    exact hNo (source_auxiliary_physical_either_end_dvd434
      P M E s t e p w D k hShift hP hs hDisj a b ha hb hCollision)
  simp only [if_neg hNot]

/-- Complete exact finite change of variables for the source03
physical auxiliary collision error. The event-specific physical
row and its completely coupled K_nu are unchanged, the signed
shift is reduced from k*p*D to k*D, and the ORIGINAL harmonic
measure contributes exactly ONE 1/p outside the new y-sum.
No probabilistic approximation or divisor-moment bound occurs. -/
theorem source_auxiliary_original_collision_finite_charge434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p D N : ℕ) (k : ℤ) (hp : 0 < p)
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (Fmark : ℕ → ℕ → (G → Fin M → ℕ) →
      (G → Fin M → ℕ) → ℂ) :
    (∑ w ∈ Finset.Icc 1 N,
      if 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) then
        sourceAuxiliaryPhysicalCollisionMask434 P M E s t e
          p w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat)
          (Fmark w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat))*
          (w:ℂ)⁻¹
      else 0) =
    (p:ℂ)⁻¹*
      (∑ y ∈ Finset.Icc 1 (N/p),
        if 0 < (y:ℤ)+k*(D:ℤ) then
          sourceAuxiliaryPhysicalCollisionMask434 P M E s t e
            p (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat)
            (Fmark (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat))*
            (y:ℂ)⁻¹
        else 0) := by
  classical
  let F : ℕ → ℕ → ℂ := fun w wp =>
    sourceAuxiliaryPhysicalCollisionMask434 P M E s t e
      p w wp (Fmark w wp)
  have hZero (w : ℕ) (hNo : ¬p∣w)
      (hShift : 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ)) :
      F w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat) = 0 := by
    have hPos : 0 < (w:ℤ)+k*(p*D:ℕ) := by
      simpa only [Nat.cast_mul,mul_assoc] using hShift
    have hEq : (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat) =
      (((w:ℤ)+k*(p*D:ℕ)).toNat) := by
      simp only [Nat.cast_mul,mul_assoc]
    dsimp only [F]
    rw [hEq]
    exact source_auxiliary_physical_collision_zero_off_divisor434
      P M E s t e p w D k hPos hNo hP hs hDisj
      (Fmark w (((w:ℤ)+k*(p*D:ℕ)).toNat))
  change (∑ w ∈ Finset.Icc 1 N,
    if 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) then
      F w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat)*(w:ℂ)⁻¹ else 0) = _
  calc
    _ = ∑ w ∈ Finset.Icc 1 N,
      if p ∣ w then
        (if 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) then
          F w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat)*(w:ℂ)⁻¹ else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hdiv : p ∣ w
          · simp only [if_pos hdiv]
          · by_cases hpos : 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ)
            · simp only [if_pos hpos,if_neg hdiv,
                hZero w hdiv hpos,zero_mul]
            · simp only [if_neg hpos,if_neg hdiv]
    _ = (p:ℂ)⁻¹*
      (∑ y ∈ Finset.Icc 1 (N/p),
        if 0 < (y:ℤ)+k*(D:ℤ) then
          F (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat)*(y:ℂ)⁻¹
        else 0) :=
      source_auxiliary_harmonic_charge434 p D N k hp F
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCollisionActualReindex -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Positive source positions with a TRUE auxiliary divisor p
are exactly a p-fibre. Both signed shifted endpoints remain
positive under the reduced shift k*D, and the target toNat scales
EXACTLY by p. Nothing is assumed about squarefreeness. -/
theorem source_auxiliary_true_collision_reindex434
    (p w D : ℕ) (k : ℤ) (hp : p.Prime)
    (hw : 0 < w)
    (hShift : 0 < (w:ℤ)+k*(p*D:ℕ))
    (hDiv : p ∣ w) :
    ∃ y : ℕ,
      0 < y ∧ w=p*y ∧
      0 < (y:ℤ)+k*(D:ℤ) ∧
      (((w:ℤ)+k*(p*D:ℕ)).toNat) =
        p*(((y:ℤ)+k*(D:ℤ)).toNat) := by
  obtain ⟨y,hyw⟩ := hDiv
  have hy : 0 < y := by
    by_contra hnot
    have hz : y=0 := Nat.eq_zero_of_not_pos hnot
    subst y
    simp only [mul_zero] at hyw
    omega
  have hpPos : (0:ℤ) < p := by exact_mod_cast hp.pos
  have hLift : (0:ℤ) <
      ((p*y:ℕ):ℤ)+k*(p*D:ℕ) := by
    simpa only [←hyw] using hShift
  have hLift' : (0:ℤ) < ((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ) := by
    simpa only [Nat.cast_mul,mul_assoc] using hLift
  have hScaled : (0:ℤ) < (p:ℤ)*((y:ℤ)+k*(D:ℤ)) := by
    rw [←source_auxiliary_signed_shift_scaling434 p y D k]
    exact hLift'
  have hReduced : 0 < (y:ℤ)+k*(D:ℤ) := by
    by_contra hnot
    have hle : (y:ℤ)+k*(D:ℤ) ≤ 0 := le_of_not_gt hnot
    have hNonpos : (p:ℤ)*((y:ℤ)+k*(D:ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpPos.le hle
    omega
  have hToNat := source_auxiliary_signed_toNat_scaling434
    p y D k hp.pos hReduced
  have hToNat' : ((((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat) =
      p*(((y:ℤ)+k*(D:ℤ)).toNat) := by
    convert hToNat using 1
    push_cast
    ring
  refine ⟨y,hy,hyw,hReduced,?_⟩
  simpa only [hyw] using hToNat'

/-- Actual original source physical marks: if an auxiliary free p
hits either endpoint's unshared ordered marked list, the original
physical pair is exactly the correctly translated p-fibre.
No assumption that the p-label is distinct from OTHER auxiliary
labels is introduced. -/
theorem source_auxiliary_physical_collision_true_fibre434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p w D : ℕ) (k : ℤ) (hp : p.Prime) (hw : 0<w)
    (hShift : 0 < (w:ℤ)+k*(p*D:ℕ))
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (a b : G → Fin M → ℕ)
    (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w)
    (hb : b ∈ sourceGlobalSharedCompletions434 P M E s
      (((w:ℤ)+k*(p*D:ℕ)).toNat))
    (hCollision : (∃ g j,a g (e g j)=p) ∨
      (∃ g j,b g (e g j)=p)) :
    ∃ y : ℕ,
      0 < y ∧ w=p*y ∧
      0 < (y:ℤ)+k*(D:ℤ) ∧
      (((w:ℤ)+k*(p*D:ℕ)).toNat) =
        p*(((y:ℤ)+k*(D:ℤ)).toNat) := by
  have hDiv := source_auxiliary_physical_either_end_dvd434
    P M E s t e p w D k hShift hP hs hDisj a b ha hb hCollision
  exact source_auxiliary_true_collision_reindex434 p w D k hp hw hShift hDiv
end Green64Analytic.CorrelationSquare

end

/-! ## SourceMarkedFamilySplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exact finite marked-family marginalization. The right test can see
all right-hand lists jointly, not only their products. -/
theorem source_marked_family_sum_inr434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {π : ι ⊕ β → Type} [∀ g,DecidableEq (π g)]
    (F : ∀ g,Finset (π g)) (test : (∀ j,π (.inr j)) → ℂ) :
    (∑ a ∈ Fintype.piFinset F,test (fun j => a (.inr j))) =
      ((∏ i : ι,(F (.inl i)).card:ℕ):ℂ)*
        ∑ b ∈ Fintype.piFinset (fun j => F (.inr j)),test b := by
  classical
  let FL := fun i : ι => F (.inl i)
  let FR := fun j : β => F (.inr j)
  let eqv := (sourceFiniteListFamilyEquiv434 F).trans
    (Equiv.sumPiEquivProdPi (fun g => ↑(F g)))
  have hAll := Fintype.sum_equiv eqv
    (fun a => test (fun j => a.val (.inr j)))
    (fun ab => test (fun j => (ab.2 j).val)) (fun a => rfl)
  have hRight := Fintype.sum_equiv (sourceFiniteListFamilyEquiv434 FR).symm
    (fun b => test (fun j => (b j).val)) (fun b => test b.val) (fun b => rfl)
  calc
    _ = ∑ a : ↑(Fintype.piFinset F),test (fun j => a.val (.inr j)) :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ ab : (∀ i,↑(FL i)) × (∀ j,↑(FR j)),test (fun j => (ab.2 j).val) := hAll
    _ = ((Fintype.card (∀ i,↑(FL i)):ℕ):ℂ)*
        ∑ b : ∀ j,↑(FR j),test (fun j => (b j).val) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by
      rw [hRight,Finset.sum_coe_sort]
      simp only [Fintype.card_pi,Fintype.card_coe,FL,FR]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMarkedWeightSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exact all-group marked weight at the SOURCE distinguished-small /
other-small / big split. Large-mark tests remain arbitrary functions
of the full tuples; there is no product-measurability restriction. -/
theorem source_original_marked_weight_split434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (k : ℕ) (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ j,Fin (tb j) → ℕ) → ℂ) (n : ℕ) :
    actualBigMarkDecoration (Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb))
      (Sum.elim (fun _ : Unit => k) (Sum.elim ts tb)) q
      (Sum.elim (fun _ : Unit => Vs) (Sum.elim Vsmall Vbig))
      (fun a => b (fun j => a (.inr (.inr j)))) n =
    literalSourceWeight S Ts Tb q Vs Vsmall Vbig ts tb b k n := by
  classical
  let P := Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb)
  let t := Sum.elim (fun _ : Unit => k) (Sum.elim ts tb)
  let V := Sum.elim (fun _ : Unit => Vs) (Sum.elim Vsmall Vbig)
  have hSmall := source_marked_family_sum_inr434
    (fun g : ι ⊕ β => orderedBigMarks ((Sum.elim Ts Tb) g) ((Sum.elim ts tb) g) n) b
  have hDist := source_marked_family_sum_inr434
    (fun g => orderedBigMarks (P g) (t g) n)
    (fun a => b (fun j => a (.inr j)))
  simp only [P,t,Sum.elim_inl,Sum.elim_inr,Fintype.prod_unique] at hDist
  simp only [Sum.elim_inl,Sum.elim_inr] at hSmall
  rw [hSmall] at hDist
  have hSum : (∑ a ∈ bigMarkLists P t n,b (fun j => a (.inr (.inr j)))) =
      (((smallPrimeCount S n).descFactorial k:ℕ):ℂ)*
        ((∏ i : ι,(smallPrimeCount (Ts i) n).descFactorial (ts i):ℕ):ℂ)*
        (∑ a ∈ bigMarkLists Tb tb n,b a) := by
    simpa only [bigMarkLists,P,t,Sum.elim_inl,Sum.elim_inr,
      orderedBigMarks_card,mul_assoc] using hDist
  have hPref : bigMarkPrefactor P t q V n =
      ((q^((smallPrimeCount S n:ℤ)-(k:ℤ))/Vs^k:ℝ):ℂ)*
        bigMarkPrefactor Ts ts q Vsmall n*bigMarkPrefactor Tb tb q Vbig n := by
    simp only [bigMarkPrefactor,P,t,V,Fintype.prod_sum_type,Fintype.prod_unique,
      Sum.elim_inl,Sum.elim_inr]
    ring
  change actualBigMarkDecoration P t q V (fun a => b (fun j => a (.inr (.inr j)))) n = _
  rw [actualBigMarkDecoration,hSum,hPref,literalSourceWeight,literal_mark_sum_factor]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedNormalization -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 5000000

/-- Both half-damping factors at one endpoint leave the original
integer-exponent unshared marked prefactor. -/
theorem source_shared_damping_square434 (P R : Finset ℕ) (w M t : ℕ)
    (q : ℝ) (hq : 0 < q) (hP : ∀ p ∈ P, p.Prime) (hRP : R ⊆ P)
    (hAvoid : ∀ p ∈ R, ¬p ∣ w) (hM : R.card+t=M) :
    (q^(((smallPrimeCount P ((∏ p ∈ R,p)*w):ℝ)-(M:ℝ))/2))^2 =
      (q^((smallPrimeCount P w:ℤ)-(t:ℤ)):ℝ) := by
  rw [pow_two,←Real.rpow_add hq,source_shared_prime_count434 P R w hP hRP hAvoid,
    ←Real.rpow_intCast]
  congr 1
  rw [←hM]
  push_cast
  ring

/-- Exact joint V-normalization, including harmonic shared dilution.
This is valid also at V=0: the zero case is checked, not silently cancelled. -/
theorem source_shared_joint_normalization434 (V : ℂ) (s t : ℕ) :
    (V^(s+t))⁻¹*(V^t)⁻¹ = (V^s)⁻¹*(V^t)⁻¹*(V^t)⁻¹ := by
  rw [pow_add,mul_inv_rev]
  ring

/-- Literal physical mass and four endpoint half-dampings become the
shared harmonic mass and the TWO marked-list prefactors. -/
theorem source_shared_two_end_normalization434
    (P R : Finset ℕ) (w wp M t : ℕ) (q V : ℝ)
    (hq : 0 < q) (hP : ∀ p ∈ P, p.Prime) (hRP : R ⊆ P)
    (hAvoid : ∀ p ∈ R, ¬p ∣ w) (hAvoid' : ∀ p ∈ R, ¬p ∣ wp)
    (hM : R.card+t=M) :
    (((V:ℂ)^M)⁻¹*((V:ℂ)^t)⁻¹)*
      (((q^(((smallPrimeCount P ((∏ p ∈ R,p)*w):ℝ)-(M:ℝ))/2))^2:ℝ):ℂ)*
      (((q^(((smallPrimeCount P ((∏ p ∈ R,p)*wp):ℝ)-(M:ℝ))/2))^2:ℝ):ℂ) =
    ((V:ℂ)^R.card)⁻¹ *
      ((q^((smallPrimeCount P w:ℤ)-(t:ℤ))/V^t:ℝ):ℂ)*
      ((q^((smallPrimeCount P wp:ℤ)-(t:ℤ))/V^t:ℝ):ℂ) := by
  rw [source_shared_damping_square434 P R w M t q hq hP hRP hAvoid hM,
    source_shared_damping_square434 P R wp M t q hq hP hRP hAvoid' hM,
    ←hM,source_shared_joint_normalization434]
  push_cast
  simp only [div_eq_mul_inv]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedHarmonicMass -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 5000000

/-- The set product is the literal labelled product when the physical
shared list is injective; no multiplicity is discarded silently. -/
theorem source_shared_labelled_product434 {M : ℕ} (E : Finset (Fin M))
    (shared : E → ℕ) (hInj : Function.Injective shared) :
    (∏ p ∈ sourceSharedPrimeSet434 E shared,p) = ∏ i : E, shared i := by
  classical
  unfold sourceSharedPrimeSet434
  rw [Finset.prod_image (fun i hi j hj hij => hInj hij)]

theorem source_shared_labelled_card434 {M : ℕ} (E : Finset (Fin M))
    (shared : E → ℕ) (hInj : Function.Injective shared) :
    (sourceSharedPrimeSet434 E shared).card = E.card := by
  classical
  rw [sourceSharedPrimeSet434,Finset.card_image_of_injective _ hInj,
    Finset.card_univ,Fintype.card_coe]

/-- The exact shared probability mass, including the reciprocal dilation. -/
theorem source_shared_harmonic_mass434 {M : ℕ} (E : Finset (Fin M))
    (shared : E → ℕ) (hInj : Function.Injective shared) (V : ℂ) :
    (V^(sourceSharedPrimeSet434 E shared).card)⁻¹ *
      ((∏ p ∈ sourceSharedPrimeSet434 E shared,p:ℕ):ℂ)⁻¹ =
        ∏ i : E, (V*(shared i:ℂ))⁻¹ := by
  classical
  rw [source_shared_labelled_card434 E shared hInj,
    source_shared_labelled_product434 E shared hInj]
  simp only [Nat.cast_prod,mul_inv_rev,Finset.prod_mul_distrib,
    Finset.prod_inv_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe]
  ring

/-- The actual source parameter t=ell+|C| satisfies M=s+t. -/
theorem source_original_shared_card_add434
    (J ell : ℕ) (C : Finset (Fin J))
    (shared : sourceOriginalSharedSlots434 J ell C → ℕ)
    (hInj : Function.Injective shared) :
    (sourceSharedPrimeSet434 _ shared).card + (ell+C.card) = J+ell := by
  rw [source_shared_labelled_card434 _ shared hInj,source_original_shared_slot_card434]
  have hC : C.card ≤ J := by simpa only [Fintype.card_fin] using C.card_le_univ
  omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedGlobalMass -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 5000000

theorem source_shared_global_set_disjoint434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset G)) R := by
  intro g hg h hh hne
  apply Finset.disjoint_left.mpr
  intro p hp hpp
  exact hne (hDisj g h p (hRP g hp) (hRP h hpp))

/-- Global shared dilation is the actual labelled product, without
losing a shared prime or duplicating one across distinct groups. -/
theorem source_shared_global_labelled_product434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M)) (shared : ∀ g, E g → ℕ)
    (hs : ∀ g i, shared g i ∈ P g) (hInj : ∀ g, Function.Injective (shared g))
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) :
    (∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (shared g)),p) =
      ∏ g,∏ i : E g,shared g i := by
  classical
  have hRP : ∀ g, sourceSharedPrimeSet434 (E g) (shared g) ⊆ P g := by
    intro g p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hs g i
  rw [Finset.prod_biUnion (source_shared_global_set_disjoint434 P _ hRP hDisj)]
  apply Finset.prod_congr rfl
  intro g hg
  exact source_shared_labelled_product434 (E g) (shared g) (hInj g)

/-- Exact product probability on all original shared slots. The harmonic
factor 1/D_R is included once, not once per endpoint. -/
theorem source_shared_global_harmonic_mass434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M)) (shared : ∀ g, E g → ℕ) (V : G → ℂ)
    (hs : ∀ g i, shared g i ∈ P g) (hInj : ∀ g, Function.Injective (shared g))
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) :
    (∏ g,(V g^(sourceSharedPrimeSet434 (E g) (shared g)).card)⁻¹)*
      ((∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (shared g)),p:ℕ):ℂ)⁻¹ =
      ∏ g,∏ i : E g,(V g*(shared g i:ℂ))⁻¹ := by
  classical
  rw [source_shared_global_labelled_product434 P M E shared hs hInj hDisj]
  calc
    _ = ∏ g, (V g^(sourceSharedPrimeSet434 (E g) (shared g)).card)⁻¹ *
        ((∏ i : E g,shared g i:ℕ):ℂ)⁻¹ := by
      simp only [Nat.cast_prod,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g hg
      rw [←source_shared_harmonic_mass434 (E g) (shared g) (hInj g) (V g),
        source_shared_labelled_product434 (E g) (shared g) (hInj g)]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedFullScalar -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual global shared dilation has slot-count parity. -/
theorem source_shared_global_parity434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M)) (s : ∀ g, E g → ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hs : ∀ g i, s g i ∈ P g)
    (hInj : ∀ g, Function.Injective (s g))
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) :
    literalSourceParity (Finset.univ.biUnion P)
      (∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (s g)),p) =
        (-1:ℂ)^(∑ g,(E g).card) := by
  classical
  rw [source_shared_global_labelled_product434 P M E s hs hInj hDisj]
  have h := source_shared_product_parity434 (Finset.univ.biUnion P)
    (Finset.univ : Finset ((g : G) × E g)) (fun gi => s gi.1 gi.2)
    (fun gi _ => hP gi.1 _ (hs gi.1 gi.2))
    (fun gi _ => Finset.mem_biUnion.mpr ⟨gi.1,Finset.mem_univ _,hs gi.1 gi.2⟩)
  simpa only [Fintype.prod_sigma,Finset.card_univ,Fintype.card_sigma,
    Fintype.card_coe] using h

/-- Both ORIGINAL prime-slot cores, independent signs and phases, and
harmonic normalization, on one actual shared fibre. -/
theorem source_shared_actual_core_harmonic434
    (P R prime1 prime2 : Finset ℕ) (w wp free q1 q2 slots : ℕ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1) (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ) (eps1 eps2 : Bool)
    (hR : ∀ p ∈ R, p.Prime) (hRP : R ⊆ P)
    (hw : 0 < w) (hwp : 0 < wp) (hfree : 0 < free) (hZ : 0 < Z)
    (hSign : literalSourceParity P (∏ p ∈ R,p)=(-1:ℂ)^slots) :
    let d := ∏ p ∈ R,p
    let F := fun n => sourceCore (sourceOutsidePart P n) prime1 alpha1 c1 q1 chi1 s01 s11
    let H := fun n => sourceCore (sourceOutsidePart P n) prime2 alpha2 c2 q2 chi2 s02 s12
    psi (((d*w:ℕ):ℝ)/(Z*((d*free:ℕ):ℝ)))*((d*w:ℕ):ℂ)⁻¹*
      sourcePhase (d*free) (-(a1+a2))*sourcePhase (d*w) a1*sourcePhase (d*wp) a2*
      star (F (d*w))*H (d*wp)*sourceEndpointSign434 P eps1 (d*w)*
        sourceEndpointSign434 P eps2 (d*wp) =
    (d:ℂ)⁻¹*((if eps1 then (-1:ℂ)^slots else 1)*(if eps2 then (-1:ℂ)^slots else 1))*
      (psi ((w:ℝ)/(Z*(free:ℝ)))*(w:ℂ)⁻¹*sourcePhase free (-(a1+a2))*
        sourcePhase w a1*sourcePhase wp a2*star (F w)*H wp*
        sourceEndpointSign434 P eps1 w*sourceEndpointSign434 P eps2 wp) := by
  classical
  dsimp only
  have hd : 0 < ∏ p ∈ R,p := Finset.prod_pos (fun p hp => (hR p hp).pos)
  rw [source_literal_core_shared_invariant434 P R prime1 w q1 alpha1 c1 chi1 s01 s11 hR hRP hw.ne',
    source_literal_core_shared_invariant434 P R prime2 wp q2 alpha2 c2 chi2 s02 s12 hR hRP hwp.ne']
  have hScalar := source_shared_harmonic_scalar434 (∏ p ∈ R,p) free w wp Z a1 a2 psi hd hfree hw hwp hZ
  have hSigns := source_shared_dilation_independent_signs434 P (∏ p ∈ R,p) w wp slots
    eps1 eps2 hd.ne' hw.ne' hwp.ne' hSign
  calc
    _ = (psi (((((∏ p ∈ R,p)*w:ℕ):ℝ))/(Z*((((∏ p ∈ R,p)*free:ℕ):ℝ))))*
        ((((∏ p ∈ R,p)*w:ℕ):ℂ))⁻¹*sourcePhase ((∏ p ∈ R,p)*free) (-(a1+a2))*
        sourcePhase ((∏ p ∈ R,p)*w) a1*sourcePhase ((∏ p ∈ R,p)*wp) a2)*
      (star (sourceCore (sourceOutsidePart P w) prime1 alpha1 c1 q1 chi1 s01 s11)*
        sourceCore (sourceOutsidePart P wp) prime2 alpha2 c2 q2 chi2 s02 s12)*
      (sourceEndpointSign434 P eps1 ((∏ p ∈ R,p)*w)*
        sourceEndpointSign434 P eps2 ((∏ p ∈ R,p)*wp)) := by ring
    _ = _ := by rw [hScalar,hSigns]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryChargedSignedKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact original lifted summand after charging ONE auxiliary p.
The shifted target is the actual signed integer shift, tested for
positivity before toNat. Both ORIGINAL sourceCore's, source phases,
1/(p*y), and independent parity twists survive. Neither the
marked-weight tests nor any relative-mass estimate is assumed. -/
theorem source_auxiliary_original_signed_charged_kernel434
    (P prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hp : p.Prime) (hpP : p ∈ P) (hy : 0 < y)
    (hD : 0 < D) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(D:ℤ)) :
    let yp := ((y:ℤ)+k*(D:ℤ)).toNat
    let zp := (((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat
    let F := fun n => sourceCore (sourceOutsidePart P n)
      prime1 alpha1 c1 q1 chi1 s01 s11
    let G := fun n => sourceCore (sourceOutsidePart P n)
      prime2 alpha2 c2 q2 chi2 s02 s12
    psi (((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ)))*((p*y:ℕ):ℂ)⁻¹*
      sourcePhase (p*D) (-(a1+a2))*
      sourcePhase (p*y) a1*sourcePhase zp a2*
      star (F (p*y))*G zp*
      sourceEndpointSign434 P eps1 (p*y)*
        sourceEndpointSign434 P eps2 zp =
    (p:ℂ)⁻¹*((if eps1 then (-1:ℂ) else 1)*
      (if eps2 then (-1:ℂ) else 1))*
      (psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
        sourcePhase D (-(a1+a2))*
        sourcePhase y a1*sourcePhase yp a2*
        star (F y)*G yp*
        sourceEndpointSign434 P eps1 y*
          sourceEndpointSign434 P eps2 yp) := by
  have hYP : 0 < ((y:ℤ)+k*(D:ℤ)).toNat := by omega
  have hZp := source_auxiliary_signed_toNat_scaling434
    p y D k hp.pos hShift
  have hSign : literalSourceParity P (∏ z ∈ ({p}:Finset ℕ), z) =
      (-1:ℂ)^(1:ℕ) := by
    simpa only [Finset.prod_singleton,pow_one] using
      source_literal_parity_prime434 P p hp hpP
  have hPrime : ∀ z ∈ ({p}:Finset ℕ), z.Prime := by
    intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    exact hp
  have hBase := source_shared_actual_core_harmonic434
    P {p} prime1 prime2 y (((y:ℤ)+k*(D:ℤ)).toNat)
    D q1 q2 1 alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    hPrime (Finset.singleton_subset_iff.mpr hpP) hy hYP hD hZ hSign
  have hZp' : ((((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat) =
      p * (((y:ℤ)+k*(D:ℤ)).toNat) := by
    convert hZp using 1
    push_cast
    ring
  dsimp only
  rw [hZp']
  simpa only [Finset.prod_singleton,pow_one] using hBase
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFibreSum -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Source lifted physical summand at a genuinely p-divisible
position, retaining the original translated endpoint and all
original character/core/phase/parity factors. -/
noncomputable def sourceAuxiliaryLiftedSummand434
    (P prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) : ℂ :=
  let zp := (((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat
  let F := fun n => sourceCore (sourceOutsidePart P n)
    prime1 alpha1 c1 q1 chi1 s01 s11
  let G := fun n => sourceCore (sourceOutsidePart P n)
    prime2 alpha2 c2 q2 chi2 s02 s12
  psi (((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ)))*((p*y:ℕ):ℂ)⁻¹*
    sourcePhase (p*D) (-(a1+a2))*
    sourcePhase (p*y) a1*sourcePhase zp a2*
    star (F (p*y))*G zp*
    sourceEndpointSign434 P eps1 (p*y)*
      sourceEndpointSign434 P eps2 zp

/-- The source free-prime-charged summand, where the entire core
is evaluated at y,y+kD. The p-dependent reciprocal factor is
intentionally OUTSIDE this definition. -/
noncomputable def sourceAuxiliaryStrippedSummand434
    (P prime1 prime2 : Finset ℕ) (y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) : ℂ :=
  let yp := ((y:ℤ)+k*(D:ℤ)).toNat
  let F := fun n => sourceCore (sourceOutsidePart P n)
    prime1 alpha1 c1 q1 chi1 s01 s11
  let G := fun n => sourceCore (sourceOutsidePart P n)
    prime2 alpha2 c2 q2 chi2 s02 s12
  psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
    sourcePhase D (-(a1+a2))*
    sourcePhase y a1*sourcePhase yp a2*
    star (F y)*G yp*
    sourceEndpointSign434 P eps1 y*
      sourceEndpointSign434 P eps2 yp

theorem source_auxiliary_lifted_stripped_exact434
    (P prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hp : p.Prime) (hpP : p ∈ P) (hy : 0 < y)
    (hD : 0 < D) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(D:ℤ)) :
    sourceAuxiliaryLiftedSummand434 P prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 =
    (p:ℂ)⁻¹*((if eps1 then (-1:ℂ) else 1)*
      (if eps2 then (-1:ℂ) else 1))*
    sourceAuxiliaryStrippedSummand434 P prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  simpa only [sourceAuxiliaryLiftedSummand434,
    sourceAuxiliaryStrippedSummand434] using
    source_auxiliary_original_signed_charged_kernel434
      P prime1 prime2 p y D q1 q2 k alpha1 alpha2 c1 c2
      chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
      hp hpP hy hD hZ hShift

/-- Sum the LITERAL charged lift: no diagonal delta or nonlinear
shift was replaced. The independent signs become only a unit
scalar constant on this very p-fibre. -/
theorem source_auxiliary_original_fibre_sum_exact434
    (P prime1 prime2 : Finset ℕ) (p D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (S : Finset ℕ)
    (hp : p.Prime) (hpP : p ∈ P)
    (hD : 0 < D) (hZ : 0 < Z)
    (hS : ∀ y ∈ S, 0 < y ∧ 0 < (y:ℤ)+k*(D:ℤ)) :
    (∑ y ∈ S,sourceAuxiliaryLiftedSummand434 P prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2) =
    (p:ℂ)⁻¹*((if eps1 then (-1:ℂ) else 1)*
      (if eps2 then (-1:ℂ) else 1))*
    ∑ y ∈ S,sourceAuxiliaryStrippedSummand434 P prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact source_auxiliary_lifted_stripped_exact434 P prime1 prime2
    p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    hp hpP (hS y hy).1 hD hZ (hS y hy).2
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryExactNorm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The true source stripped auxiliary term has exactly the absolute
amplitude of the two unmarked prime-slot cores and the remaining
harmonic cutoff; every phase and endpoint sign is unitary. -/
theorem source_auxiliary_stripped_summand_norm434
    (P prime1 prime2 : Finset ℕ) (y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) :
    let yp := ((y:ℤ)+k*(D:ℤ)).toNat
    ‖sourceAuxiliaryStrippedSummand434 P prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ =
    ‖psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
      sourcePhase y a1*sourcePhase yp a2‖*
    ‖sourceCore (sourceOutsidePart P y)
      prime1 alpha1 c1 q1 chi1 s01 s11‖*
    ‖sourceCore (sourceOutsidePart P yp)
      prime2 alpha2 c2 q2 chi2 s02 s12‖ := by
  dsimp only
  simp only [sourceAuxiliaryStrippedSummand434,norm_mul,
    sourcePhase_norm,source_endpoint_sign_norm434,norm_star,
    mul_one,one_mul]

/-- True per-p absolute charge, with arbitrary independently selected
endpoint signs and the two literal prime-slot cores. -/
theorem source_auxiliary_lifted_summand_norm434
    (P prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hp : p.Prime) (hpP : p ∈ P) (hy : 0 < y)
    (hD : 0 < D) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(D:ℤ)) :
    let yp := ((y:ℤ)+k*(D:ℤ)).toNat
    ‖sourceAuxiliaryLiftedSummand434 P prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ =
    (p:ℝ)⁻¹*
      (‖psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
        sourcePhase y a1*sourcePhase yp a2‖*
      ‖sourceCore (sourceOutsidePart P y)
        prime1 alpha1 c1 q1 chi1 s01 s11‖*
      ‖sourceCore (sourceOutsidePart P yp)
        prime2 alpha2 c2 q2 chi2 s02 s12‖) := by
  dsimp only
  have hFactor : ‖((if eps1 then (-1:ℂ) else 1)*
      (if eps2 then (-1:ℂ) else 1))‖ = 1 := by
    simpa only [pow_one] using source_shared_pattern_sign_norm434 1 eps1 eps2
  have hEq := source_auxiliary_lifted_stripped_exact434
    P prime1 prime2 p y D q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    hp hpP hy hD hZ hShift
  rw [hEq]
  simp only [norm_mul,norm_inv,Complex.norm_natCast,hFactor,one_mul]
  have hStripped := source_auxiliary_stripped_summand_norm434
    P prime1 prime2 y D q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
  dsimp only at hStripped
  rw [hStripped]
  simp only [norm_mul,norm_inv,Complex.norm_natCast,sourcePhase_norm,
    mul_one,one_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryGeneralParityKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- Exact source lifted auxiliary summand with the REAL distinction
between all marked primes P and the optional parity set Ptw ⊆ P.
The previous special-case kernel demanded p∈Ptw and was insufficient. -/
noncomputable def sourceAuxiliaryGeneralLifted434
    (P Ptw prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) : ℂ :=
  let zp := (((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat
  let F := fun n => sourceCore (sourceOutsidePart P n)
    prime1 alpha1 c1 q1 chi1 s01 s11
  let G := fun n => sourceCore (sourceOutsidePart P n)
    prime2 alpha2 c2 q2 chi2 s02 s12
  psi (((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ)))*((p*y:ℕ):ℂ)⁻¹*
    sourcePhase (p*D) (-(a1+a2))*
    sourcePhase (p*y) a1*sourcePhase zp a2*
    star (F (p*y))*G zp*
    sourceEndpointSign434 Ptw eps1 (p*y)*
      sourceEndpointSign434 Ptw eps2 zp

/-- Corresponding exactly charged source summand with independent
parity Ptw. The p-dependent reciprocal factor lives outside. -/
noncomputable def sourceAuxiliaryGeneralStripped434
    (P Ptw prime1 prime2 : Finset ℕ) (y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) : ℂ :=
  let yp := ((y:ℤ)+k*(D:ℤ)).toNat
  let F := fun n => sourceCore (sourceOutsidePart P n)
    prime1 alpha1 c1 q1 chi1 s01 s11
  let G := fun n => sourceCore (sourceOutsidePart P n)
    prime2 alpha2 c2 q2 chi2 s02 s12
  psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
    sourcePhase D (-(a1+a2))*
    sourcePhase y a1*sourcePhase yp a2*
    star (F y)*G yp*
    sourceEndpointSign434 Ptw eps1 y*
      sourceEndpointSign434 Ptw eps2 yp

/-- Actual source auxiliary charge, including both cases p∈Ptw and
p∉Ptw. The two endpoint signs are selected independently. -/
theorem source_auxiliary_general_signed_charge434
    (P Ptw prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hp : p.Prime) (hpP : p ∈ P)
    (hy : 0 < y) (hD : 0 < D) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(D:ℤ)) :
    sourceAuxiliaryGeneralLifted434 P Ptw prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 =
    (p:ℂ)⁻¹*
      ((if eps1 then (if p∈Ptw then (-1:ℂ) else 1) else 1)*
        (if eps2 then (if p∈Ptw then (-1:ℂ) else 1) else 1))*
      sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
        y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  let yp : ℕ := ((y:ℤ)+k*(D:ℤ)).toNat
  have hYP : 0 < yp := by dsimp only [yp]; omega
  have hZp := source_auxiliary_signed_toNat_scaling434
    p y D k hp.pos hShift
  have hZp' : ((((p*y:ℕ):ℤ)+k*(p*D:ℕ)).toNat) = p*yp := by
    convert hZp using 1
    push_cast
    ring
  let F : ℕ → ℂ := fun n =>
    sourceCore (sourceOutsidePart P n)
      prime1 alpha1 c1 q1 chi1 s01 s11
  let G : ℕ → ℂ := fun n =>
    sourceCore (sourceOutsidePart P n)
      prime2 alpha2 c2 q2 chi2 s02 s12
  have hCore1 : F (p*y) = F y :=
    source_auxiliary_original_core_invariant434
      P prime1 p y q1 alpha1 c1 chi1 s01 s11 hp hpP hy
  have hCore2 : G (p*yp) = G yp :=
    source_auxiliary_original_core_invariant434
      P prime2 p yp q2 alpha2 c2 chi2 s02 s12 hp hpP hYP
  have hScalar := source_shared_harmonic_scalar434
    p D y yp Z a1 a2 psi hp.pos hD hy hYP hZ
  have hSigns := source_auxiliary_prime_two_sign_choices434
    Ptw p y yp eps1 eps2 hp hy hYP
  unfold sourceAuxiliaryGeneralLifted434 sourceAuxiliaryGeneralStripped434
  simp only [hZp']
  change
    (psi (((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ)))*((p*y:ℕ):ℂ)⁻¹*
      sourcePhase (p*D) (-(a1+a2))*
      sourcePhase (p*y) a1*sourcePhase (p*yp) a2*
      star (F (p*y))*G (p*yp)*
      sourceEndpointSign434 Ptw eps1 (p*y)*
      sourceEndpointSign434 Ptw eps2 (p*yp)) = _
  rw [hCore1,hCore2]
  calc
    _ = (psi (((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ)))*((p*y:ℕ):ℂ)⁻¹*
        sourcePhase (p*D) (-(a1+a2))*
        sourcePhase (p*y) a1*sourcePhase (p*yp) a2)*
      (star (F y)*G yp)*
      (sourceEndpointSign434 Ptw eps1 (p*y)*
        sourceEndpointSign434 Ptw eps2 (p*yp)) := by ring
    _ = ((p:ℂ)⁻¹*psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
        sourcePhase D (-(a1+a2))*
        sourcePhase y a1*sourcePhase yp a2)*
      (star (F y)*G yp)*
      (((if eps1 then (if p∈Ptw then (-1:ℂ) else 1) else 1)*
        (if eps2 then (if p∈Ptw then (-1:ℂ) else 1) else 1))*
       sourceEndpointSign434 Ptw eps1 y*
        sourceEndpointSign434 Ptw eps2 yp) := by
      rw [hScalar,hSigns]
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryGeneralFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- General auxiliary charge with the original independent parity
subset Ptw, including p ∉ Ptw, summed over a genuine finite fibre. -/
theorem source_auxiliary_general_fibre_sum434
    (P Ptw prime1 prime2 : Finset ℕ) (p D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (S : Finset ℕ)
    (hp : p.Prime) (hpP : p ∈ P)
    (hD : 0 < D) (hZ : 0 < Z)
    (hS : ∀ y ∈ S, 0 < y ∧ 0 < (y:ℤ)+k*(D:ℤ)) :
    (∑ y ∈ S,sourceAuxiliaryGeneralLifted434 P Ptw prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2) =
    (p:ℂ)⁻¹*
      ((if eps1 then (if p∈Ptw then (-1:ℂ) else 1) else 1)*
       (if eps2 then (if p∈Ptw then (-1:ℂ) else 1) else 1))*
    ∑ y ∈ S,sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact source_auxiliary_general_signed_charge434
    P Ptw prime1 prime2 p y D q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    hp hpP (hS y hy).1 hD hZ (hS y hy).2

/-- Both independently chosen parity characters have a common
unit-modulus product on a fixed charged auxiliary p fibre. -/
theorem source_auxiliary_choice_norm434
    (Ptw : Finset ℕ) (p : ℕ) (e1 e2 : Bool) :
    ‖((if e1 then (if p∈Ptw then (-1:ℂ) else 1) else 1)*
      (if e2 then (if p∈Ptw then (-1:ℂ) else 1) else 1))‖ = 1 := by
  by_cases hm : p ∈ Ptw <;> cases e1 <;> cases e2 <;> simp [hm]

/-- Exact fibre norm: the only p-dependent modulus is 1/p,
including both mixed sign channels and p not in the twist set. -/
theorem source_auxiliary_general_fibre_norm434
    (P Ptw prime1 prime2 : Finset ℕ) (p D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (S : Finset ℕ)
    (hp : p.Prime) (hpP : p ∈ P)
    (hD : 0 < D) (hZ : 0 < Z)
    (hS : ∀ y ∈ S, 0 < y ∧ 0 < (y:ℤ)+k*(D:ℤ)) :
    ‖∑ y ∈ S,sourceAuxiliaryGeneralLifted434 P Ptw prime1 prime2
      p y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ =
    (p:ℝ)⁻¹*
      ‖∑ y ∈ S,sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
        y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ := by
  rw [source_auxiliary_general_fibre_sum434 P Ptw prime1 prime2
    p D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 S hp hpP hD hZ hS]
  simp only [norm_mul,norm_inv,Complex.norm_natCast]
  by_cases hm : p ∈ Ptw <;> cases eps1 <;> cases eps2 <;>
    simp [hm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryGeneralPointwise -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Exact 1/p norm identity for EACH genuinely lifted original
source03 auxiliary term. Unlike the whole-fibre identity, this
can multiply arbitrary bounded coefficients depending on p,y,
physical lists and K_nu, without assuming coherent cancellation. -/
theorem source_auxiliary_general_pointwise_norm434
    (P Ptw prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hp : p.Prime) (hpP : p ∈ P)
    (hy : 0 < y) (hD : 0 < D) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(D:ℤ)) :
    ‖sourceAuxiliaryGeneralLifted434
       P Ptw prime1 prime2 p y D q1 q2 k
       alpha1 alpha2 c1 c2 chi1 chi2 s01 s11 s02 s12 Z a1 a2
       psi eps1 eps2‖ =
       (p:ℝ)⁻¹ *
       ‖sourceAuxiliaryGeneralStripped434
         P Ptw prime1 prime2 y D q1 q2 k
         alpha1 alpha2 c1 c2 chi1 chi2 s01 s11 s02 s12 Z a1 a2
         psi eps1 eps2‖ := by
  have hS : ∀ z ∈ ({y}:Finset ℕ),
      0 < z ∧ 0 < (z:ℤ)+k*(D:ℤ) := by
    intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    exact ⟨hy,hShift⟩
  have hh := source_auxiliary_general_fibre_norm434
    P Ptw prime1 prime2 p D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 ({y}:Finset ℕ)
    hp hpP hD hZ hS
  simpa only [Finset.sum_singleton] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedGlobalNormalization -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 8000000

/-- Literal original global half damping at a natural physical position. -/
noncomputable def sourcePhysicalGroupedHalf434 {G : Type} [Fintype G]
    (P : G → Finset ℕ) (M : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  q^((((∑ g,smallPrimeCount (P g) n:ℕ):ℝ)-(M*Fintype.card G:ℕ))/2)

/-- Sum the actual count identities without adding a count hypothesis. -/
theorem source_shared_global_count_exponent434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (M : ℕ) (t : G → ℕ) (w : ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h)
    (hAvoid : ∀ g p, p ∈ R g → ¬p ∣ w) (hM : ∀ g, (R g).card+t g=M) :
    (((∑ g,smallPrimeCount (P g) ((∏ p ∈ Finset.univ.biUnion R,p)*w):ℕ):ℝ)-
      (M*Fintype.card G:ℕ)) = ∑ g,((smallPrimeCount (P g) w:ℝ)-(t g:ℝ)) := by
  classical
  have hCounts (g : G) := source_group_count_global_shared434 P R hP hRP hDisj g w (hAvoid g)
  simp_rw [hCounts]
  push_cast
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hSum : (∑ g,((R g).card:ℝ)) + (∑ g,(t g:ℝ)) = (M:ℝ)*(Fintype.card G:ℝ) := by
    rw [←Finset.sum_add_distrib]
    have hc (g : G) : ((R g).card:ℝ)+(t g:ℝ)=(M:ℝ) := by exact_mod_cast hM g
    simp_rw [hc]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  linarith

/-- All original global half-dampings equal the product of original
marked group prefactors after the true shared dilation is removed. -/
theorem source_shared_global_half_square434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (M : ℕ) (t : G → ℕ) (w : ℕ) (q : ℝ) (hq : 0 < q)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h)
    (hAvoid : ∀ g p, p ∈ R g → ¬p ∣ w) (hM : ∀ g, (R g).card+t g=M) :
    (sourcePhysicalGroupedHalf434 P M q ((∏ p ∈ Finset.univ.biUnion R,p)*w))^2 =
      ∏ g,(q^((smallPrimeCount (P g) w:ℤ)-(t g:ℤ)):ℝ) := by
  classical
  unfold sourcePhysicalGroupedHalf434
  rw [pow_two,←Real.rpow_add hq]
  have halg (v : ℝ) : v/2+v/2=v := by ring
  rw [halg,source_shared_global_count_exponent434 P R M t w hP hRP hDisj hAvoid hM,
    Real.rpow_sum_of_pos hq]
  apply Finset.prod_congr rfl
  intro g hg
  rw [←Real.rpow_intCast]
  congr 1
  push_cast
  rfl

theorem source_shared_global_two_end_normalization434
    {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (M : ℕ) (t : G → ℕ) (w wp : ℕ) (q : ℝ) (V : G → ℝ)
    (hq : 0 < q) (hP : ∀ g p, p ∈ P g → p.Prime) (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h)
    (hAvoid : ∀ g p, p ∈ R g → ¬p ∣ w)
    (hAvoid' : ∀ g p, p ∈ R g → ¬p ∣ wp) (hM : ∀ g, (R g).card+t g=M) :
    (∏ g,((V g:ℂ)^M)⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
      ((sourcePhysicalGroupedHalf434 P M q ((∏ p ∈ Finset.univ.biUnion R,p)*w))^2:ℝ)*
      ((sourcePhysicalGroupedHalf434 P M q ((∏ p ∈ Finset.univ.biUnion R,p)*wp))^2:ℝ) =
    (∏ g,((V g:ℂ)^(R g).card)⁻¹)*bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp := by
  classical
  rw [source_shared_global_half_square434 P R M t w q hq hP hRP hDisj hAvoid hM,
    source_shared_global_half_square434 P R M t wp q hq hP hRP hDisj hAvoid' hM]
  push_cast
  unfold bigMarkPrefactor
  simp only [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [←hM g,source_shared_joint_normalization434]
  push_cast
  simp only [div_eq_mul_inv]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyDamping -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

theorem source_small_count_mul_mono434 (P : Finset ℕ) (d w : ℕ) :
    smallPrimeCount P w ≤ smallPrimeCount P (d*w) := by
  apply Finset.card_le_card
  intro p hp
  have h := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨h.1,dvd_mul_of_dvd_right h.2 d⟩

/-- Explicit loss for actual overlapping physical marks. No statement
that the physical row is already clean is used in this bound. -/
theorem source_global_dirty_damping_le434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M d w : ℕ) (t : G → ℕ) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (sourcePhysicalGroupedHalf434 P M q (d*w))^2 ≤
      q^(-((M*Fintype.card G:ℕ):ℝ))*
        ∏ g,(q^((smallPrimeCount (P g) w:ℤ)-(t g:ℤ)):ℝ) := by
  classical
  have hProd : (∏ g,(q^((smallPrimeCount (P g) w:ℤ)-(t g:ℤ)):ℝ)) =
      q^(∑ g,((smallPrimeCount (P g) w:ℝ)-(t g:ℝ))) := by
    rw [Real.rpow_sum_of_pos hq]
    apply Finset.prod_congr rfl
    intro g hg
    rw [←Real.rpow_intCast]
    congr 1
    push_cast
    rfl
  have hCounts : (∑ g,smallPrimeCount (P g) w) ≤ ∑ g,smallPrimeCount (P g) (d*w) :=
    Finset.sum_le_sum (fun g _ => source_small_count_mul_mono434 (P g) d w)
  have hCountsR : (∑ g,(smallPrimeCount (P g) w:ℝ)) ≤
      ∑ g,(smallPrimeCount (P g) (d*w):ℝ) := by exact_mod_cast hCounts
  have ht : 0 ≤ ∑ g,(t g:ℝ) := Finset.sum_nonneg (fun g _ => Nat.cast_nonneg _)
  rw [hProd,←Real.rpow_add hq]
  unfold sourcePhysicalGroupedHalf434
  rw [pow_two,←Real.rpow_add hq]
  apply Real.rpow_le_rpow_of_exponent_ge hq hq1
  push_cast
  rw [Finset.sum_sub_distrib]
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyRows -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Actual two-endpoint physical rows, with arbitrary coupled
coefficients. Injective restriction controls their multiplicities
WITHOUT excluding shared/endpoint overlaps first. -/
theorem source_global_dirty_two_row_bound434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g}) (w wp : ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime) (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (K : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (hK : ∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,‖K a b‖ ≤ B) :
    ‖∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,K a b‖ ≤
    B*(bigMarkLists P t w).card*(bigMarkLists P t wp).card := by
  have hInner (a : G → Fin M → ℕ) (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w) :
      ‖∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,K a b‖ ≤
        (bigMarkLists P t wp).card*B := by
    have h := source_global_dirty_weighted_sum_le434 P M E s t e wp hP hs hDisj
      (K a) (fun _ => B) (fun _ _ => hB) (hK a ha)
    simpa only [Finset.sum_const,nsmul_eq_mul] using h
  have hOut := source_global_dirty_weighted_sum_le434 P M E s t e w hP hs hDisj
    (fun a => ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,K a b)
    (fun _ => (bigMarkLists P t wp).card*B) (fun _ _ => mul_nonneg (Nat.cast_nonneg _) hB) hInner
  simp only [Finset.sum_const,nsmul_eq_mul] at hOut
  exact hOut.trans_eq (by ring)

/-- Repeated shared labels cannot appear in an original physical row,
because the full endpoint list consists of distinct marked primes. -/
theorem source_global_physical_shared_injective434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (w : ℕ)
    (a : G → Fin M → ℕ) (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w) :
    ∀ g,Function.Injective (s g) := by
  intro g i j hij
  have h := Finset.mem_filter.mp ((Fintype.mem_piFinset.mp ha) g)
  have hInj := (source_ordered_marks_mem434 (P g) M _ (a g)).mp h.1
  apply Subtype.ext
  apply hInj.2
  exact (h.2 i).trans (hij.trans (h.2 j).symm)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCleanGlobalPairing -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 12000000

/-- Exact clean shared-fibre identity for ALL groups in the original
physical row. The original arbitrary two-list coefficient K is retained. -/
theorem source_original_clean_global_pairing434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ)
    (J ell : ℕ) (C : G → Finset (Fin J))
    (shared : ∀ g, sourceOriginalSharedSlots434 J ell (C g) → ℕ)
    (w wp : ℕ) (q : ℝ) (V : G → ℝ) (hq : 0 < q)
    (hP : ∀ g p, p ∈ P g → p.Prime) (hs : ∀ g i, shared g i ∈ P g)
    (hInj : ∀ g, Function.Injective (shared g))
    (hAvoid : ∀ g i, ¬shared g i ∣ w) (hAvoid' : ∀ g i, ¬shared g i ∣ wp)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h)
    (K : (G → Fin (J+ell) → ℕ) → (G → Fin (J+ell) → ℕ) → ℂ) :
    let E := fun g => sourceOriginalSharedSlots434 J ell (C g)
    let R := fun g => sourceSharedPrimeSet434 (E g) (shared g)
    let d := ∏ p ∈ Finset.univ.biUnion R,p
    let t := fun g => ell+(C g).card
    let e := fun g => sourceOriginalFreeSlotEquiv434 J ell (C g)
    (∏ g,((V g:ℂ)^(J+ell))⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*(d:ℂ)⁻¹*
      ((sourcePhysicalGroupedHalf434 P (J+ell) q (d*w))^2:ℝ)*
      ((sourcePhysicalGroupedHalf434 P (J+ell) q (d*wp))^2:ℝ)*
      (∑ a ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared wp,K a b) =
    (∏ g,∏ i : E g, ((V g:ℂ)*(shared g i:ℂ))⁻¹)*
      bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
      (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
        K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (a g))
          (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g))) := by
  classical
  dsimp only
  let E := fun g => sourceOriginalSharedSlots434 J ell (C g)
  let R := fun g => sourceSharedPrimeSet434 (E g) (shared g)
  let t := fun g => ell+(C g).card
  let e := fun g => sourceOriginalFreeSlotEquiv434 J ell (C g)
  have hRP : ∀ g, R g ⊆ P g := by
    intro g p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hs g i
  have hAw : ∀ g p, p ∈ R g → ¬p ∣ w := by
    intro g p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hAvoid g i
  have hAw' : ∀ g p, p ∈ R g → ¬p ∣ wp := by
    intro g p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hAvoid' g i
  have hM : ∀ g, (R g).card+t g=J+ell :=
    fun g => source_original_shared_card_add434 J ell (C g) (shared g) (hInj g)
  have hN := source_shared_global_two_end_normalization434 P R (J+ell) t w wp
    q V hq hP hRP hDisj hAw hAw' hM
  have hMass := source_shared_global_harmonic_mass434 P (J+ell) E shared
    (fun g => (V g:ℂ)) hs hInj hDisj
  have hSum : (∑ a ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared w,
      ∑ b ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared wp,K a b) =
    ∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
      K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (a g))
        (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g)) := by
    rw [source_global_shared_family_sum434 P (J+ell) E shared t e w
      hP hs hInj hAvoid hDisj]
    apply Finset.sum_congr rfl
    intro a ha
    exact source_global_shared_family_sum434 P (J+ell) E shared t e wp
      hP hs hInj hAvoid' hDisj _
  rw [hSum]
  calc
    _ = ((∏ g,((V g:ℂ)^(J+ell))⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
        ((sourcePhysicalGroupedHalf434 P (J+ell) q ((∏ p ∈ Finset.univ.biUnion R,p)*w))^2:ℝ)*
        ((sourcePhysicalGroupedHalf434 P (J+ell) q ((∏ p ∈ Finset.univ.biUnion R,p)*wp))^2:ℝ))*
        ((∏ p ∈ Finset.univ.biUnion R,p:ℕ):ℂ)⁻¹*
        (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
          K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (a g))
            (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g))) := by
      dsimp only [R,E,t,e]; ring
    _ = _ := by rw [hN,←hMass]; dsimp only [R,E,t,e]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedIndependentLaw -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable def sourceSharedLaw434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℝ) (a : ι → ℕ) : ℝ := ∏ i,mu i (a i)

theorem source_shared_law_nonneg434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S) :
    0 ≤ sourceSharedLaw434 mu a := by
  classical
  exact Finset.prod_nonneg (fun i _ => hmu i _ ((Fintype.mem_piFinset.mp ha) i))

theorem source_shared_law_total434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1) :
    (∑ a ∈ Fintype.piFinset S,sourceSharedLaw434 mu a)=1 := by
  classical
  unfold sourceSharedLaw434
  rw [←Finset.prod_univ_sum]
  simp only [hMass,Finset.prod_const_one]

/-- Exact product expectation on the original finite independent draws. -/
theorem source_shared_law_product_test434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu test : ι → ℕ → ℝ) :
    (∑ a ∈ Fintype.piFinset S,sourceSharedLaw434 mu a*(∏ i,test i (a i))) =
      ∏ i,∑ p ∈ S i,mu i p*test i p := by
  classical
  simp only [sourceSharedLaw434,←Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum S (fun i p => mu i p*test i p)).symm

/-- The exact one-coordinate marginal, for arbitrary real tests. -/
theorem source_shared_law_single_test434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1) (i : ι) (test : ℕ → ℝ) :
    (∑ a ∈ Fintype.piFinset S,sourceSharedLaw434 mu a*test (a i)) =
      ∑ p ∈ S i,mu i p*test p := by
  classical
  have h := source_shared_law_product_test434 S mu
    (fun j p => if j=i then test p else 1)
  simpa only [Finset.prod_ite_eq',Finset.mem_univ,ite_true,mul_ite,mul_one,
    Finset.sum_ite_irrel,hMass] using h

/-- Two distinct source slots are genuinely independent, including
repeated prime values. No distinctness conditioning is inserted. -/
theorem source_shared_law_pair_test434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1)
    (i j : ι) (hne : i ≠ j) (f g : ℕ → ℝ) :
    (∑ a ∈ Fintype.piFinset S,sourceSharedLaw434 mu a*f (a i)*g (a j)) =
      (∑ p ∈ S i,mu i p*f p)*(∑ p ∈ S j,mu j p*g p) := by
  classical
  have h := source_shared_law_product_test434 S mu
    (fun k p => (if k=i then f p else 1)*(if k=j then g p else 1))
  have hRow (k : ι) :
      (∑ p ∈ S k,mu k p*((if k=i then f p else 1)*(if k=j then g p else 1))) =
      (if k=i then ∑ p ∈ S i,mu i p*f p else 1)*
        (if k=j then ∑ p ∈ S j,mu j p*g p else 1) := by
    by_cases hi : k=i
    · subst k; simp only [ite_true,if_neg hne,mul_one]
    · by_cases hj : k=j
      · subst k; simp only [if_neg hi,ite_true,one_mul]
      · simp only [if_neg hi,if_neg hj,mul_one,hMass]
  simp only [hRow,Finset.prod_mul_distrib,Finset.prod_ite_eq',
    Finset.mem_univ,ite_true] at h
  simpa only [mul_assoc] using h
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullFreeProduct -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- True ORIGINAL free dilation with one labelled auxiliary slot
removed, retaining repeated prime values in OTHER labelled slots. -/
noncomputable def sourceAuxiliaryOtherProduct434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι) : ℕ :=
  ∏ j : {j : ι // j ≠ slot}, labels j.val

theorem source_auxiliary_original_full_product_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι) :
    (∏ j : ι,labels j) =
      labels slot*sourceAuxiliaryOtherProduct434 labels slot := by
  classical
  exact Fintype.prod_eq_mul_prod_subtype_ne labels slot

/-- The ORIGINAL independent prime probability law splits into the
charged atom mu_i(p_i) times all the other original atoms. This is
an equality EVEN IF some other slot draws the same prime p_i. -/
theorem source_auxiliary_original_full_probability_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℝ) (labels : ι → ℕ) (slot : ι) :
    sourceSharedLaw434 mu labels =
      mu slot (labels slot)*
        ∏ j : {j : ι // j ≠ slot},
          mu j.val (labels j.val) := by
  classical
  unfold sourceSharedLaw434
  exact Fintype.prod_eq_mul_prod_subtype_ne
    (fun j => mu j (labels j)) slot

/-- All the other ORIGINAL auxiliary prime factors form a positive
product; it is not assumed to be squarefree or disjoint from p_i. -/
theorem source_auxiliary_original_other_product_pos434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι)
    (hPrime : ∀ j,(labels j).Prime) :
    0 < sourceAuxiliaryOtherProduct434 labels slot := by
  classical
  unfold sourceAuxiliaryOtherProduct434
  exact Finset.prod_pos (fun j hj => (hPrime j.val).pos)

/-- The TRUE source signed shift with the full original independent
free-label tuple factors through ANY selected charged slot p_i,
without changing k or requiring distinctness between slots. -/
theorem source_auxiliary_original_full_shift_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι) (y : ℕ) (k : ℤ) :
    (((labels slot*y:ℕ):ℤ)+
       k*((∏ j : ι,labels j:ℕ):ℤ)) =
      (labels slot:ℤ)*
        ((y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ)) := by
  rw [source_auxiliary_original_full_product_split434 labels slot]
  simpa only [Nat.cast_mul,mul_assoc] using
    source_auxiliary_signed_shift_scaling434
      (labels slot) y (sourceAuxiliaryOtherProduct434 labels slot) k
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTupleCollision -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Collision of an actual auxiliary slot in the FULL original free
dilation D_C = product of every auxiliary label: the physical w is
divisible by the CHOSEN prime, even if other slots draw that prime.
The exact new shift is k times the product of all OTHER labelled
slots, and the endpoint toNat is transferred without truncation. -/
theorem source_auxiliary_original_full_tuple_collision_fibre434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
    [Fintype G] [DecidableEq G]
    (labels : ι → ℕ) (slot : ι)
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (w : ℕ) (k : ℤ)
    (hp : (labels slot).Prime) (hw : 0 < w)
    (hShift : 0 < (w:ℤ)+k*((∏ j : ι,labels j:ℕ):ℤ))
    (hP : ∀ g z,z ∈ P g → z.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h z,z ∈ P g → z ∈ P h → g=h)
    (a b : G → Fin M → ℕ)
    (ha : a ∈ sourceGlobalSharedCompletions434 P M E s w)
    (hb : b ∈ sourceGlobalSharedCompletions434 P M E s
      (((w:ℤ)+k*((∏ j : ι,labels j:ℕ):ℤ)).toNat))
    (hCollision :
      (∃ g j,a g (e g j)=labels slot) ∨
      (∃ g j,b g (e g j)=labels slot)) :
    ∃ y : ℕ,
      0 < y ∧ w=(labels slot)*y ∧
      0 < (y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ) ∧
      (((w:ℤ)+k*((∏ j : ι,labels j:ℕ):ℤ)).toNat) =
        (labels slot)*
          (((y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat) := by
  let d : ℕ := sourceAuxiliaryOtherProduct434 labels slot
  have hProd := source_auxiliary_original_full_product_split434 labels slot
  have hShift' : 0 < (w:ℤ)+k*((labels slot*d:ℕ):ℤ) := by
    simpa only [d,←hProd] using hShift
  have hb' : b ∈ sourceGlobalSharedCompletions434 P M E s
      (((w:ℤ)+k*((labels slot*d:ℕ):ℤ)).toNat) := by
    simpa only [d,←hProd] using hb
  obtain ⟨y,hy,hyw,hReduced,hToNat⟩ :=
    source_auxiliary_physical_collision_true_fibre434
      P M E s t e (labels slot) w d k hp hw hShift'
      hP hs hDisj a b ha hb' hCollision
  refine ⟨y,hy,hyw,?_,?_⟩
  · simpa only [d] using hReduced
  · simpa only [d,←hProd] using hToNat
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTupleKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The LITERAL source03 free-dilation summand uses the product of
ALL labelled auxiliary primes. One selected charged slot is NOT
deleted from the original kernel before defining this expression. -/
noncomputable def sourceAuxiliaryOriginalFullTupleKernel434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι)
    (P Ptw prime1 prime2 : Finset ℕ)
    (y q1 q2 : ℕ) (k : ℤ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) : ℂ :=
  let d : ℕ := ∏ j : ι, labels j
  let n : ℕ := (labels slot)*y
  let np : ℕ := (((n:ℕ):ℤ)+k*(d:ℤ)).toNat
  psi ((n:ℝ)/(Z*(d:ℝ)))*(n:ℂ)⁻¹*
    sourcePhase d (-(a1+a2))*
    sourcePhase n a1*sourcePhase np a2*
    star (sourceCore (sourceOutsidePart P n)
      prime1 alpha1 c1 q1 chi1 s01 s11)*
    sourceCore (sourceOutsidePart P np)
      prime2 alpha2 c2 q2 chi2 s02 s12*
    sourceEndpointSign434 Ptw eps1 n*
      sourceEndpointSign434 Ptw eps2 np

/-- Exact original full-product source03 arithmetic is the already
proved charged one-slot kernel with d = product of ALL OTHER slots.
This equality remains valid when OTHER auxiliary labels equal the
charged prime. It retains true full source core and both parity sets. -/
theorem source_auxiliary_original_full_tuple_kernel_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι)
    (P Ptw prime1 prime2 : Finset ℕ)
    (y q1 q2 : ℕ) (k : ℤ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (hPrime : ∀ j,(labels j).Prime)
    (hP : labels slot ∈ P)
    (hy : 0 < y) (hZ : 0 < Z)
    (hShift : 0 < (y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ)) :
    sourceAuxiliaryOriginalFullTupleKernel434
      labels slot P Ptw prime1 prime2 y q1 q2 k
      alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 =
    ((labels slot:ℂ)⁻¹)*
      ((if eps1 then (if labels slot∈Ptw then (-1:ℂ) else 1) else 1)*
       (if eps2 then (if labels slot∈Ptw then (-1:ℂ) else 1) else 1))*
    sourceAuxiliaryGeneralStripped434
      P Ptw prime1 prime2 y (sourceAuxiliaryOtherProduct434 labels slot)
      q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  let d : ℕ := sourceAuxiliaryOtherProduct434 labels slot
  have hd : 0 < d :=
    source_auxiliary_original_other_product_pos434 labels slot hPrime
  have hBase := source_auxiliary_general_signed_charge434
    P Ptw prime1 prime2 (labels slot) y d q1 q2 k
    alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    (hPrime slot) hP hy hd hZ (by simpa only [d] using hShift)
  have hLiteral : sourceAuxiliaryOriginalFullTupleKernel434
      labels slot P Ptw prime1 prime2 y q1 q2 k
      alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 =
    sourceAuxiliaryGeneralLifted434
      P Ptw prime1 prime2 (labels slot) y d q1 q2 k
      alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
    unfold sourceAuxiliaryOriginalFullTupleKernel434
    rw [source_auxiliary_original_full_product_split434 labels slot]
    rfl
  rw [hLiteral]
  simpa only [d] using hBase
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTupleLiteral -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- UNCONDITIONAL literal identification of the complete source03
free-product arithmetic kernel with the chosen p-fibre source kernel.
No primality, noncollision or distinctness hypotheses are needed for
this identity; only removal of the SELECTED SLOT from the product. -/
theorem source_auxiliary_full_tuple_literal_lifted434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (labels : ι → ℕ) (slot : ι)
    (P Ptw prime1 prime2 : Finset ℕ)
    (y q1 q2 : ℕ) (k : ℤ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) :
    sourceAuxiliaryOriginalFullTupleKernel434
      labels slot P Ptw prime1 prime2 y q1 q2 k
      alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 =
    sourceAuxiliaryGeneralLifted434
      P Ptw prime1 prime2 (labels slot) y
      (sourceAuxiliaryOtherProduct434 labels slot) q1 q2 k
      alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 := by
  unfold sourceAuxiliaryOriginalFullTupleKernel434
  rw [source_auxiliary_original_full_product_split434 labels slot]
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedCollisionMass -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Literal excluded-prime mass of one independent source slot. -/
theorem source_shared_law_excluded_mass434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1) (i : ι) (B : Finset ℕ) :
    (∑ a ∈ Fintype.piFinset S,if a i ∈ B then sourceSharedLaw434 mu a else 0) =
      ∑ p ∈ S i,if p ∈ B then mu i p else 0 := by
  classical
  have hh := source_shared_law_single_test434 S mu hMass i (fun p => if p ∈ B then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero] using hh

/-- Two slots coincide with at most the largest mass of the second slot.
The original product law still allows collisions; none have been removed. -/
theorem source_shared_law_collision_mass434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p) (i j : ι) (hne : i ≠ j)
    (delta : ℝ) (hd : 0 ≤ delta) (hAtom : ∀ p ∈ S j,mu j p ≤ delta) :
    (∑ a ∈ Fintype.piFinset S,if a i=a j then sourceSharedLaw434 mu a else 0) ≤ delta := by
  classical
  have hPoint (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S) :
      (if a i=a j then sourceSharedLaw434 mu a else 0) =
      ∑ p ∈ S i,sourceSharedLaw434 mu a*(if a i=p then 1 else 0)*(if a j=p then 1 else 0) := by
    rw [Finset.sum_eq_single (a i)]
    · by_cases he : a i=a j <;> simp [he,eq_comm]
    · intro p hp hnep
      simp only [if_neg (Ne.symm hnep),mul_zero,zero_mul]
    · intro hi
      exact (hi ((Fintype.mem_piFinset.mp ha) i)).elim
  calc
    _ = ∑ a ∈ Fintype.piFinset S,∑ p ∈ S i,
        sourceSharedLaw434 mu a*(if a i=p then 1 else 0)*(if a j=p then 1 else 0) :=
      Finset.sum_congr rfl hPoint
    _ = ∑ p ∈ S i,∑ a ∈ Fintype.piFinset S,
        sourceSharedLaw434 mu a*(if a i=p then 1 else 0)*(if a j=p then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ p ∈ S i,mu i p*(if p ∈ S j then mu j p else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [source_shared_law_pair_test434 S mu hMass i j hne
        (fun n => if n=p then 1 else 0) (fun n => if n=p then 1 else 0)]
      simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',hp,ite_true]
    _ ≤ ∑ p ∈ S i,mu i p*delta := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hmu i p hp)
      split_ifs with hj
      · exact hAtom p hj
      · exact hd
    _ = delta := by rw [←Finset.sum_mul,hMass,one_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedBadUnion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Weighted finite union bound applied before any conditioning. -/
theorem source_finite_weighted_bad_union434 {α ε : Type}
    (F : Finset α) (E : Finset ε) (w : α → ℝ)
    (bad : α → Prop) (event : α → ε → Prop)
    (hw : ∀ a ∈ F,0 ≤ w a)
    (hCover : ∀ a ∈ F,bad a → ∃ e ∈ E,event a e) :
    (∑ a ∈ F,if bad a then w a else 0) ≤
      ∑ e ∈ E,∑ a ∈ F,if event a e then w a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  have hwa : 0 ≤ w a := hw a ha
  have hnn (j : ε) : 0 ≤ (if event a j then w a else 0) := by
    split_ifs <;> positivity
  by_cases hb : bad a
  · obtain ⟨e,he,hEv⟩ := hCover a ha hb
    rw [if_pos hb]
    have hs := Finset.single_le_sum (fun j hj => hnn j) he
    simpa only [if_pos hEv] using hs
  · rw [if_neg hb]
    exact Finset.sum_nonneg (fun e he => hnn e)

noncomputable def sourceSharedClean434 {ι : Type} (B : ι → Finset ℕ) (a : ι → ℕ) : Prop :=
  Function.Injective a ∧ ∀ i,a i ∉ B i

/-- The true lost mass from removing repeated or forbidden source draws.
No renormalization of the surviving law is performed. -/
theorem source_shared_clean_defect434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S B : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hMass : ∀ i, ∑ p ∈ S i,mu i p=1)
    (hmu : ∀ i p,p ∈ S i → 0 ≤ mu i p)
    (delta beta : ℝ) (hd : 0 ≤ delta)
    (hAtom : ∀ i p,p ∈ S i → mu i p ≤ delta)
    (hExcluded : ∀ i,(∑ p ∈ S i,if p ∈ B i then mu i p else 0) ≤ beta) :
    1-(∑ a ∈ Fintype.piFinset S,if sourceSharedClean434 B a then sourceSharedLaw434 mu a else 0) ≤
      (Fintype.card ι:ℝ)*beta+(Fintype.card ι:ℝ)^2*delta := by
  classical
  let event : (ι → ℕ) → ι ⊕ (ι × ι) → Prop := fun a e =>
    match e with
    | .inl i => a i ∈ B i
    | .inr ij => ij.1 ≠ ij.2 ∧ a ij.1=a ij.2
  let cost : ι ⊕ (ι × ι) → ℝ := Sum.elim (fun _ => beta) (fun _ => delta)
  have hCover : ∀ a ∈ Fintype.piFinset S,¬sourceSharedClean434 B a →
      ∃ e ∈ (Finset.univ : Finset (ι ⊕ (ι × ι))),event a e := by
    intro a ha hb
    by_cases hi : Function.Injective a
    · have hh : ∃ i,a i ∈ B i := by
        by_contra hn
        apply hb
        exact ⟨hi,by simpa using hn⟩
      obtain ⟨i,hbi⟩ := hh
      exact ⟨.inl i,Finset.mem_univ _,hbi⟩
    · simp only [Function.Injective,not_forall] at hi
      obtain ⟨i,j,hij⟩ := hi
      obtain ⟨he,hne⟩ := hij
      exact ⟨.inr (i,j),Finset.mem_univ _,hne,he⟩
  have hUnion := source_finite_weighted_bad_union434 (Fintype.piFinset S)
    Finset.univ (sourceSharedLaw434 mu) (fun a => ¬sourceSharedClean434 B a)
    event (source_shared_law_nonneg434 S mu hmu) hCover
  have hDefect : 1-(∑ a ∈ Fintype.piFinset S,
      if sourceSharedClean434 B a then sourceSharedLaw434 mu a else 0) =
      ∑ a ∈ Fintype.piFinset S,if ¬sourceSharedClean434 B a then sourceSharedLaw434 mu a else 0 := by
    rw [←source_shared_law_total434 S mu hMass,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hc : sourceSharedClean434 B a <;> simp only [hc,ite_true,ite_false,not_true_eq_false,not_false_eq_true,sub_self,sub_zero]
  have hU : (∑ a ∈ Fintype.piFinset S,
      if ¬sourceSharedClean434 B a then sourceSharedLaw434 mu a else 0) ≤
      ∑ e : ι ⊕ (ι × ι),∑ a ∈ Fintype.piFinset S,
        if event a e then sourceSharedLaw434 mu a else 0 := by
    convert hUnion using 1
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hc : sourceSharedClean434 B a <;>
      simp only [hc,not_true_eq_false,not_false_eq_true,ite_true,ite_false]
  rw [hDefect]
  apply hU.trans
  calc
    _ ≤ ∑ e : ι ⊕ (ι × ι),cost e := by
      apply Finset.sum_le_sum
      intro e he
      cases e with
      | inl i =>
        dsimp only [cost,Sum.elim_inl]
        convert (source_shared_law_excluded_mass434 S mu hMass i (B i)).le.trans (hExcluded i) using 1
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a i ∈ B i <;> simp [event,h]
      | inr ij =>
        obtain ⟨i,j⟩ := ij
        by_cases hij : i=j
        · subst j
          simpa [event,cost] using hd
        · dsimp only [cost,Sum.elim_inr]
          convert source_shared_law_collision_mass434 S mu hMass hmu i j hij delta hd (hAtom j) using 1
          apply Finset.sum_congr rfl
          intro a ha
          by_cases heq : a i=a j <;> simp [event,hij,heq]
    _ = _ := by
      simp only [Fintype.sum_sum_type,cost,Sum.elim_inl,
        Sum.elim_inr,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_prod,Nat.cast_mul]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedPrimeLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The original source law mu_g(p)=1/(p V_g), without any truncation
or conditioning on distinctness. -/
noncomputable def sourcePrimeSharedAtom434 (V : ℝ) (p : ℕ) : ℝ := 1/((p:ℝ)*V)

theorem source_prime_shared_atom_total434 (S : Finset ℕ) (V : ℝ)
    (hV : V=∑ p ∈ S,1/(p:ℝ)) (hv : V ≠ 0) :
    (∑ p ∈ S,sourcePrimeSharedAtom434 V p)=1 := by
  unfold sourcePrimeSharedAtom434
  simp only [one_div,mul_inv_rev,←Finset.mul_sum]
  have he : (∑ p ∈ S,(p:ℝ)⁻¹)=V := by simpa only [one_div] using hV.symm
  rw [he,inv_mul_cancel₀ hv]

theorem source_prime_shared_atom_le434 (Q v V : ℝ) (p : ℕ)
    (hQ : 0 < Q) (hv : 0 < v) (hp : Q ≤ (p:ℝ)) (hV : v ≤ V) :
    sourcePrimeSharedAtom434 V p ≤ 1/(Q*v) := by
  unfold sourcePrimeSharedAtom434
  exact one_div_le_one_div_of_le (mul_pos hQ hv)
    (mul_le_mul hp hV hv.le (Nat.cast_nonneg p))

theorem source_excluded_atom_card_bound434 (S B : Finset ℕ) (mu : ℕ → ℝ)
    (delta : ℝ) (hd : 0 ≤ delta) (hAtom : ∀ p ∈ S,mu p ≤ delta) :
    (∑ p ∈ S,if p ∈ B then mu p else 0) ≤ (B.card:ℝ)*delta := by
  classical
  rw [←Finset.sum_filter]
  have hs : S.filter (fun p => p ∈ B) ⊆ B := fun p hp => (Finset.mem_filter.mp hp).2
  calc
    _ ≤ ∑ p ∈ S.filter (fun p => p ∈ B),delta :=
      Finset.sum_le_sum (fun p hp => hAtom p (Finset.mem_filter.mp hp).1)
    _ = ((S.filter (fun p => p ∈ B)).card:ℝ)*delta := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hs) hd

/-- Actual independent prime law: clean mass differs from one by an
explicit quadratic slot cost times the TRUE atom size. -/
theorem source_prime_shared_clean_defect434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (B : Finset ℕ) (V : ι → ℝ) (Q v : ℝ)
    (hQ : 0 < Q) (hv : 0 < v)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) (hVmin : ∀ i,v ≤ V i)
    (hPmin : ∀ i p,p ∈ S i → Q ≤ (p:ℝ)) :
    1-(∑ a ∈ Fintype.piFinset S,
      if sourceSharedClean434 (fun _ => B) a then
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) a else 0) ≤
      ((Fintype.card ι:ℝ)*(B.card:ℝ)+(Fintype.card ι:ℝ)^2)/(Q*v) := by
  classical
  let mu := fun i => sourcePrimeSharedAtom434 (V i)
  have hmass : ∀ i,∑ p ∈ S i,mu i p=1 := fun i =>
    source_prime_shared_atom_total434 (S i) (V i) (hV i) (hv.trans_le (hVmin i)).ne'
  have hmu : ∀ i p,p ∈ S i → 0 ≤ mu i p := by
    intro i p hp
    have hVi := hv.trans_le (hVmin i)
    dsimp only [mu,sourcePrimeSharedAtom434]
    positivity
  have hdelta : 0 ≤ 1/(Q*v) := by positivity
  have hAtom : ∀ i p,p ∈ S i → mu i p ≤ 1/(Q*v) := fun i p hp =>
    source_prime_shared_atom_le434 Q v (V i) p hQ hv (hPmin i p hp) (hVmin i)
  have hExcluded : ∀ i,(∑ p ∈ S i,if p ∈ B then mu i p else 0) ≤
      (B.card:ℝ)*(1/(Q*v)) := fun i =>
    source_excluded_atom_card_bound434 (S i) B (mu i) (1/(Q*v)) hdelta (hAtom i)
  have hh := source_shared_clean_defect434 S (fun _ => B) mu hmass hmu
    (1/(Q*v)) ((B.card:ℝ)*(1/(Q*v))) hdelta hAtom hExcluded
  exact hh.trans_eq (by ring)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryReciprocalCharge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Original free prime law mu(p)=1/(p*V) pays one MORE 1/p
when the harmonic summand is reindexed w=p*y. The resulting
charge is bounded by Q^{-1}, with no appeal to an unproved
distribution or to a spurious pointwise collision probability. -/
theorem source_auxiliary_true_reciprocal_charge434
    (S : Finset ℕ) (V Q : ℝ) (hQ : 0 < Q)
    (hV : V = ∑ p ∈ S, 1/(p:ℝ)) (hVp : 0 < V)
    (hMin : ∀ p ∈ S,Q ≤ (p:ℝ)) :
    (∑ p ∈ S,sourcePrimeSharedAtom434 V p*(p:ℝ)⁻¹) ≤ Q⁻¹ := by
  have hTotal := source_prime_shared_atom_total434 S V hV hVp.ne'
  have hTerm (p : ℕ) (hp : p ∈ S) :
      sourcePrimeSharedAtom434 V p*(p:ℝ)⁻¹ ≤
        sourcePrimeSharedAtom434 V p*Q⁻¹ := by
    have hpPos : (0:ℝ) < p := hQ.trans_le (hMin p hp)
    have hMu : 0 ≤ sourcePrimeSharedAtom434 V p := by
      unfold sourcePrimeSharedAtom434
      positivity
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using
        one_div_le_one_div_of_le hQ (hMin p hp)) hMu
  calc
    _ ≤ ∑ p ∈ S,sourcePrimeSharedAtom434 V p*Q⁻¹ :=
      Finset.sum_le_sum hTerm
    _ = Q⁻¹ := by rw [←Finset.sum_mul,hTotal,one_mul]

/-- Original independent auxiliary labels retain their FULL law.
The source reciprocal charge applies to any named slot, regardless
of coincidences with labels in the other slots. -/
theorem source_auxiliary_independent_slot_charge434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ) (Q : ℝ)
    (hQ : 0 < Q)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ))
    (hVp : ∀ i,0 < V i)
    (hMin : ∀ i p,p ∈ S i → Q ≤ (p:ℝ)) (i : ι) :
    (∑ a ∈ Fintype.piFinset S,
      sourceSharedLaw434 (fun j => sourcePrimeSharedAtom434 (V j)) a*
        (a i:ℝ)⁻¹) ≤ Q⁻¹ := by
  let μ : ι → ℕ → ℝ := fun j => sourcePrimeSharedAtom434 (V j)
  have hmass (j : ι) : ∑ p ∈ S j,μ j p=1 :=
    source_prime_shared_atom_total434 (S j) (V j) (hV j) (hVp j).ne'
  rw [source_shared_law_single_test434 S μ hmass i (fun p => (p:ℝ)⁻¹)]
  exact source_auxiliary_true_reciprocal_charge434
    (S i) (V i) Q hQ (hV i) (hVp i) (hMin i)

/-- Union over all free slots costs at most #slots/Q. This is the
size of the CHARGED harmonic mass, not the uncharged collision event. -/
theorem source_auxiliary_all_slots_charge434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ) (Q : ℝ)
    (hQ : 0 < Q)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ))
    (hVp : ∀ i,0 < V i)
    (hMin : ∀ i p,p ∈ S i → Q ≤ (p:ℝ)) :
    (∑ a ∈ Fintype.piFinset S,
      sourceSharedLaw434 (fun j => sourcePrimeSharedAtom434 (V j)) a*
        ∑ i : ι,(a i:ℝ)⁻¹) ≤
      (Fintype.card ι:ℝ)*Q⁻¹ := by
  calc
    _ = ∑ i : ι,∑ a ∈ Fintype.piFinset S,
        sourceSharedLaw434 (fun j => sourcePrimeSharedAtom434 (V j)) a*
          (a i:ℝ)⁻¹ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : ι,Q⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      exact source_auxiliary_independent_slot_charge434 S V Q
        hQ hV hVp hMin i
    _ = (Fintype.card ι:ℝ)*Q⁻¹ := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryChargedSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The charged auxiliary free-label mass has arbitrary log saving,
uniformly for O(log L) original free slots. This is deliberately
NOT called the uncharged collision probability: that needs the
exact w=p*y reindex and endpoint L2 bound. -/
theorem eventually_source_auxiliary_charged_slots_saving434
    (a Cs D : ℝ) (ha : 0 < a) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (S : ι → Finset ℕ) (V : ι → ℝ),
      (Fintype.card ι:ℝ) ≤ Cs*Real.log L →
      (∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) →
      (∀ i,0 < V i) →
      (∀ i p,p ∈ S i → Real.exp (L^a) ≤ (p:ℝ)) →
      (∑ labels ∈ Fintype.piFinset S,
        sourceSharedLaw434
          (fun i => sourcePrimeSharedAtom434 (V i)) labels*
          (∑ i : ι,(labels i:ℝ)⁻¹)) ≤ L^(-D) := by
  filter_upwards [eventually_source_fixed_poly_exp_saving a Cs 1 D ha]
    with L hBudget
  intro ι _ _ S V hCard hV hVp hMin
  have hLp : 0 < L := by linarith [hBudget.1]
  have hLog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hCardL : (Fintype.card ι:ℝ) ≤ Cs*L :=
    hCard.trans (mul_le_mul_of_nonneg_left hLog hCs)
  have hBase := source_auxiliary_all_slots_charge434 S V
    (Real.exp (L^a)) (Real.exp_pos _) hV hVp hMin
  calc
    _ ≤ (Fintype.card ι:ℝ)*(Real.exp (L^a))⁻¹ := hBase
    _ ≤ Cs*L*Real.exp (-(L^a)) := by
      rw [Real.exp_neg]
      exact mul_le_mul_of_nonneg_right hCardL (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = Cs*L^(1:ℝ)*Real.exp (-(L^a)) := by rw [Real.rpow_one]
    _ ≤ 1/L^D := hBudget.2
    _ = L^(-D) := by rw [Real.rpow_neg hLp.le,one_div]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryWeightedFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- A variable-p family of genuine charged auxiliary fibres can be
summed against ORIGINAL normalized prime weights without assuming
that the fibre test is independent of p. One uniform stripped L2
envelope suffices, with the actual reciprocal charge 1/p. -/
theorem source_auxiliary_weighted_charged_fibre_bound434
    (S : Finset ℕ) (V Q B : ℝ) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hV : V = ∑ p ∈ S, 1/(p:ℝ)) (hVp : 0 < V)
    (hMin : ∀ p ∈ S,Q ≤ (p:ℝ))
    (K : ℕ → ℂ) (hK : ∀ p ∈ S,‖K p‖ ≤ (p:ℝ)⁻¹*B) :
    ‖∑ p ∈ S, (sourcePrimeSharedAtom434 V p:ℂ)*K p‖ ≤
      Q⁻¹*B := by
  have hmu : ∀ p ∈ S, 0 ≤ sourcePrimeSharedAtom434 V p := by
    intro p hp
    have hP : (0:ℝ) < p := hQ.trans_le (hMin p hp)
    unfold sourcePrimeSharedAtom434
    positivity
  have hBasic := source_auxiliary_true_reciprocal_charge434
    S V Q hQ hV hVp hMin
  calc
    _ ≤ ∑ p ∈ S,‖(sourcePrimeSharedAtom434 V p:ℂ)*K p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ S,sourcePrimeSharedAtom434 V p*((p:ℝ)⁻¹*B) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hmu p hp)]
      exact mul_le_mul_of_nonneg_left (hK p hp) (hmu p hp)
    _ = (∑ p ∈ S,sourcePrimeSharedAtom434 V p*(p:ℝ)⁻¹)*B := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ Q⁻¹*B := mul_le_mul_of_nonneg_right hBasic hB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalWeightedFibres -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Sum the ACTUAL original p-charged kernel over a finite source
prime family, with p-dependent reduced shift D(p) and completely
p-dependent physical y-window T(p). The hypothesis is precisely
the uncharged source L2 bound, not an artificial independence
of the original source summand and its divisor p. -/
theorem source_auxiliary_original_weighted_fibres434
    (P Ptw prime1 prime2 : Finset ℕ) (S : Finset ℕ)
    (V Q B : ℝ) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hV : V=∑ p ∈ S,1/(p:ℝ)) (hVp : 0 < V)
    (hMin : ∀ p ∈ S,Q ≤ (p:ℝ))
    (D : ℕ → ℕ) (k : ℤ) (q1 q2 : ℕ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (T : ℕ → Finset ℕ)
    (hPrime : ∀ p ∈ S,p.Prime)
    (hP : ∀ p ∈ S,p ∈ P)
    (hD : ∀ p ∈ S,0 < D p) (hZ : 0 < Z)
    (hT : ∀ p ∈ S,∀ y ∈ T p,
      0 < y ∧ 0 < (y:ℤ)+k*(D p:ℤ))
    (hStripped : ∀ p ∈ S,
      ‖∑ y ∈ T p,
        sourceAuxiliaryGeneralStripped434
          P Ptw prime1 prime2 y (D p) q1 q2
          k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ ≤ B) :
    ‖∑ p ∈ S,(sourcePrimeSharedAtom434 V p:ℂ)*
      (∑ y ∈ T p,sourceAuxiliaryGeneralLifted434
        P Ptw prime1 prime2 p y (D p) q1 q2
        k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2)‖ ≤
      Q⁻¹*B := by
  apply source_auxiliary_weighted_charged_fibre_bound434
    S V Q B hQ hB hV hVp hMin
    (fun p => ∑ y ∈ T p,sourceAuxiliaryGeneralLifted434
      P Ptw prime1 prime2 p y (D p) q1 q2
      k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2)
  intro p hp
  rw [source_auxiliary_general_fibre_norm434
    P Ptw prime1 prime2 p (D p) q1 q2
    k alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    (T p) (hPrime p hp) (hP p hp)
    (hD p hp) hZ (hT p hp)]
  exact mul_le_mul_of_nonneg_left (hStripped p hp)
    (inv_nonneg.mpr (Nat.cast_nonneg _))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedEndpointExclusions -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Genuine excluded values: prime divisors of BOTH endpoints, plus
previously specified auxiliary prime labels. -/
noncomputable def sourceSharedForbidden434 (w wp : ℕ) (aux : Finset ℕ) : Finset ℕ :=
  w.primeFactors ∪ wp.primeFactors ∪ aux

theorem source_shared_forbidden_mem434 (w wp p : ℕ) (aux : Finset ℕ)
    (hw : w ≠ 0) (hwp : wp ≠ 0) (hp : p.Prime) :
    p ∈ sourceSharedForbidden434 w wp aux ↔ p ∣ w ∨ p ∣ wp ∨ p ∈ aux := by
  simp only [sourceSharedForbidden434,Finset.mem_union,Nat.mem_primeFactors,or_assoc]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.2.1
    · exact Or.inr (Or.inl h.2.1)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl ⟨hp,h,hw⟩
    · exact Or.inr (Or.inl ⟨hp,h,hwp⟩)
    · exact Or.inr (Or.inr h)

theorem source_prime_factors_pow_card434 (n : ℕ) (hn : 0 < n) :
    2^n.primeFactors.card ≤ n := by
  calc
    _ = ∏ p ∈ n.primeFactors,2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors,p := Finset.prod_le_prod
      (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem source_prime_factors_card_log2434 (n : ℕ) (hn : 0 < n) :
    n.primeFactors.card ≤ n.log2 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by norm_num) (source_prime_factors_pow_card434 n hn)

theorem source_prime_factors_card_real_log434 (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card:ℝ) ≤ Real.log (n:ℝ)/Real.log 2 := by
  have hp : (2:ℝ)^n.primeFactors.card ≤ (n:ℝ) := by
    exact_mod_cast source_prime_factors_pow_card434 n hn
  have hh := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  rw [Real.log_pow] at hh
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hh

theorem source_shared_forbidden_card434 (w wp : ℕ) (aux : Finset ℕ)
    (hw : 0 < w) (hwp : 0 < wp) :
    (sourceSharedForbidden434 w wp aux).card ≤ w.log2+wp.log2+aux.card := by
  have h₁ := Finset.card_union_le w.primeFactors wp.primeFactors
  have h₂ := Finset.card_union_le (w.primeFactors ∪ wp.primeFactors) aux
  have hw' := source_prime_factors_card_log2434 w hw
  have hwp' := source_prime_factors_card_log2434 wp hwp
  unfold sourceSharedForbidden434
  omega

/-- Concrete lost independent mass for the ACTUAL two-end clean
condition, including each of its forbidden prime divisors. -/
theorem source_actual_shared_clean_defect434 {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ) (w wp : ℕ) (aux : Finset ℕ) (Q v : ℝ)
    (hw : 0 < w) (hwp : 0 < wp) (hQ : 0 < Q) (hv : 0 < v)
    (hPrime : ∀ i p,p ∈ S i → p.Prime)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) (hVmin : ∀ i,v ≤ V i)
    (hPmin : ∀ i p,p ∈ S i → Q ≤ (p:ℝ)) :
    1-(∑ a ∈ Fintype.piFinset S,
      if Function.Injective a ∧ (∀ i,¬a i ∣ w ∧ ¬a i ∣ wp ∧ a i ∉ aux) then
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) a else 0) ≤
    ((Fintype.card ι:ℝ)*((w.log2:ℝ)+(wp.log2:ℝ)+(aux.card:ℝ))+
      (Fintype.card ι:ℝ)^2)/(Q*v) := by
  classical
  have he : (∑ a ∈ Fintype.piFinset S,
      if Function.Injective a ∧ (∀ i,¬a i ∣ w ∧ ¬a i ∣ wp ∧ a i ∉ aux) then
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) a else 0) =
    ∑ a ∈ Fintype.piFinset S,
      if sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux) a then
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hPr (i : ι) := hPrime i _ ((Fintype.mem_piFinset.mp ha) i)
    simp only [sourceSharedClean434,source_shared_forbidden_mem434 w wp _ aux hw.ne' hwp.ne' (hPr _),not_or]
  rw [he]
  apply (source_prime_shared_clean_defect434 S (sourceSharedForbidden434 w wp aux)
    V Q v hQ hv hV hVmin hPmin).trans
  have hc : ((sourceSharedForbidden434 w wp aux).card:ℝ) ≤
      (w.log2:ℝ)+(wp.log2:ℝ)+(aux.card:ℝ) := by
    exact_mod_cast source_shared_forbidden_card434 w wp aux hw hwp
  apply div_le_div_of_nonneg_right _ (mul_pos hQ hv).le
  have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ _)
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDefectSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Original endpoints in the physical range give a LOGARITHMIC number
of forbidden primes, including all auxiliary labels. -/
theorem source_shared_forbidden_log_budget434 (w wp : ℕ) (aux : Finset ℕ) (L Ca : ℝ)
    (hw : 0 < w) (hwp : 0 < wp) (hL : 1 ≤ L) (hCa : 0 ≤ Ca)
    (hwSize : (w:ℝ) ≤ Real.exp (2*L)) (hwpSize : (wp:ℝ) ≤ Real.exp (2*L))
    (haux : (aux.card:ℝ) ≤ Ca*Real.log L) :
    ((sourceSharedForbidden434 w wp aux).card:ℝ) ≤ (4/Real.log 2+Ca)*L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < L := by linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hB (n : ℕ) (hn : 0 < n) (hnSize : (n:ℝ) ≤ Real.exp (2*L)) :
      (n.primeFactors.card:ℝ) ≤ (2*L)/Real.log 2 := by
    have hnP : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hl := Real.log_le_log hnP hnSize
    rw [Real.log_exp] at hl
    exact (source_prime_factors_card_real_log434 n hn).trans
      (div_le_div_of_nonneg_right hl hlog2.le)
  have hCard : ((sourceSharedForbidden434 w wp aux).card:ℝ) ≤
      (w.primeFactors.card:ℝ)+(wp.primeFactors.card:ℝ)+(aux.card:ℝ) := by
    exact_mod_cast (Finset.card_union_le (w.primeFactors ∪ wp.primeFactors) aux).trans
      (Nat.add_le_add_right (Finset.card_union_le w.primeFactors wp.primeFactors) aux.card)
  have hAux := haux.trans (mul_le_mul_of_nonneg_left hlogL hCa)
  have hBound := hCard.trans (add_le_add (add_le_add (hB w hw hwSize) (hB wp hwp hwpSize)) hAux)
  exact hBound.trans_eq (by ring)

/-- Arbitrary uniform logarithmic saving for the TRUE discarded source
shared-draw mass, not a hypothesized generic error scalar. -/
theorem eventually_source_actual_shared_defect_saving434
    (a v Cs Ca D : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (V : ι → ℝ) (w wp : ℕ) (aux : Finset ℕ),
    0 < w → 0 < wp → (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
    (Fintype.card ι:ℝ) ≤ Cs*Real.log L → (aux.card:ℝ) ≤ Ca*Real.log L →
    (∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) → (∀ i,v ≤ V i) →
    (∀ i p,p ∈ S i → Real.exp (L^a) ≤ (p:ℝ)) →
    1-(∑ s ∈ Fintype.piFinset S,
      if sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux) s then
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) s else 0) ≤ L^(-D) := by
  let Cb : ℝ := 4/Real.log 2+Ca
  let K : ℝ := (Cs*Cb+Cs^2)/v
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  filter_upwards [eventually_source_fixed_poly_exp_saving a K 2 D ha] with L hL
  intro ι _ _ S V w wp aux hw hwp hwSize hwpSize hslots haux hV hVmin hPmin
  have hLp : 0 < L := by linarith [hL.1]
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hs : (Fintype.card ι:ℝ) ≤ Cs*L := hslots.trans (mul_le_mul_of_nonneg_left hlogL hCs)
  have hb := source_shared_forbidden_log_budget434 w wp aux L Ca hw hwp hL.1 hCa hwSize hwpSize haux
  have hBase := source_prime_shared_clean_defect434 S (sourceSharedForbidden434 w wp aux) V
    (Real.exp (L^a)) v (Real.exp_pos _) hv hV hVmin hPmin
  apply hBase.trans
  calc
    _ ≤ ((Cs*L)*(Cb*L)+(Cs*L)^2)/(Real.exp (L^a)*v) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hprod := mul_le_mul hs hb (Nat.cast_nonneg _) (by positivity : 0 ≤ Cs*L)
      have hsq : (Fintype.card ι:ℝ)^2 ≤ (Cs*L)^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2
      exact add_le_add hprod hsq
    _ = K*L^(2:ℝ)*Real.exp (-(L^a)) := by
      rw [Real.rpow_two,Real.exp_neg]
      dsimp only [K]
      ring
    _ ≤ 1/L^D := hL.2
    _ = L^(-D) := by rw [Real.rpow_neg hLp.le,one_div]
end Green64Analytic.CorrelationSquare

end

