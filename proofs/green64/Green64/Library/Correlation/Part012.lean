module

public import Green64.Library.Correlation.Part011
public import Green64.Library.Correlation.Part010
public import Green64.Library.Weights.Part002
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Correlation / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryPrimitiveGWeightedFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- An actual fixed-input slice of the indexed source G fibre, retaining ALL
zero coefficients. The output pending multiset is frozen by the lifespan. -/
def memoryPrimitiveGFixedInputFibre
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap ×
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) :=
  Finset.univ.filter (fun yc =>
    (⟨x, yc.1, yc.2⟩ :
      Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      Σ _ : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullGhostWitness SP smallMod BP bigMod (J+ell) cap xx) ∈
      physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memorySeenBeforeGValues BP bigMod A life i) ∧
    ∀ g, (Green64Fock.fockToList ((yc.1.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))

/-- Exhaustive summation of the original G weights on that ACTUAL slice.
No cardinality or occurrence-level bijection assumption is supplied. -/
theorem memory_source_primitive_G_fixed_input_sum
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i)) :
    (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      A life offset i x,
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x yc.1 yc.2) =
    ∑ e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
        ↥(memoryGhostBirthSet (A g) (life g) i),
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x
        (memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i x hOld hcap e)
        (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e) := by
  let make := fun e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
        ↥(memoryGhostBirthSet (A g) (life g) i) =>
    (memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i x hOld hcap e,
     memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e)
  have hmake : Function.Injective make := by
    intro e f he
    have hc := congrArg Prod.snd he
    funext g
    exact memory_ghost_lift_order_injective (bigMod g) (A g) (life g) offset i
      (hs g) _ (hOld g) (cap g) (hcap g) (congrFun hc g)
  let T := Finset.univ.image make
  have hsub : T ⊆ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      A life offset i x := by
    intro yc hy
    obtain ⟨e, he, hye⟩ := Finset.mem_image.mp hy
    subst yc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact memory_primitive_G_indexed_eligible SP smallMod BP bigMod J ell cap
        A life offset i hinj hs x hOld hcap e
    · intro g
      change (Green64Fock.fockToList
        (memoryGhostOutputFock (bigMod g) (A g) (life g) offset i
          _ (hOld g) (cap g) (hcap g) (e g))).Perm _
      rw [memory_ghost_output_list_exact]
      exact memory_ghost_after_perm_canonical (bigMod g) (A g) (life g) offset i
        (hs g) _ (hOld g) (e g)
  have hzero : ∀ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      A life offset i x, yc ∉ T →
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x yc.1 yc.2 = 0 := by
    intro yc hy hnot
    by_contra hn
    have hspec := (Finset.mem_filter.mp hy).2
    obtain ⟨e, he, hu⟩ := memory_source_primitive_G_unique_inverse SP smallMod BP bigMod
      J ell cap A life offset i hs hcap q rho N Vbig mu x yc.1 yc.2
      hOld hspec.2 hspec.1 hn
    apply hnot
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_univ _, Prod.ext he.2.symm he.1.symm⟩
  rw [← Finset.sum_subset hsub hzero]
  exact Finset.sum_image (fun a _ b _ he => hmake he)

/-- The source coefficient after summing unordered ghost births; only the
original 1/b! has disappeared. OLD death and continuing-zero factors remain. -/
def memoryPrimitiveGUnorderedCoefficient
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℂ :=
  ∏ g : BG,
    (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ)) ^
      (memoryGhostDeathSet (A g) (life g) i).card *
    (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2) ^
      (memoryContinuingZeroSet (bigMod g) (A g) (life g) offset i).card *
    (-((sourceVisitEta q N i : ℝ) : ℂ) * (Vbig g : ℂ) / (rho : ℂ)) ^
      (memoryGhostBirthSet (A g) (life g) i).card *
    (∏ p ∈ memoryGhostBirthSet (A g) (life g) i, (mu g p : ℂ))

theorem memory_source_primitive_G_fixed_input_weighted_fibre
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i)) :
    (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      A life offset i x,
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x yc.1 yc.2) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset i q rho N Vbig mu := by
  rw [memory_source_primitive_G_fixed_input_sum SP smallMod BP bigMod J ell cap
    A life offset i hinj hs hcap q rho N Vbig mu x hOld]
  simp_rw [memory_primitive_G_branch_coefficient_exact SP smallMod BP bigMod J ell cap
    A life offset i hs x hOld hcap]
  let factor := fun g : BG =>
    (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ)) ^
      (memoryGhostDeathSet (A g) (life g) i).card *
    (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2) ^
      (memoryContinuingZeroSet (bigMod g) (A g) (life g) offset i).card *
    (1 / (Nat.factorial (memoryGhostBirthSet (A g) (life g) i).card : ℂ)) *
    (-((sourceVisitEta q N i : ℝ) : ℂ) * (Vbig g : ℂ) / (rho : ℂ)) ^
      (memoryGhostBirthSet (A g) (life g) i).card *
    (∏ p ∈ memoryGhostBirthSet (A g) (life g) i, (mu g p : ℂ))
  rw [← Fintype.prod_sum (fun g
    (_ : Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) => factor g)]
  dsimp only [factor]
  unfold memoryPrimitiveGUnorderedCoefficient
  apply Finset.prod_congr rfl
  intro g hg
  let S := memoryGhostBirthSet (A g) (life g) i
  have hc : Fintype.card (Fin S.card ≃ ↥S) = Nat.factorial S.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_equiv (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
  have hf : (Nat.factorial S.card : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero S.card
  change (Nat.factorial S.card : ℂ) * (_ * _ * (1 / (Nat.factorial S.card : ℂ)) * _ * _) = _
  field_simp [hf]
  <;> ring
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGOrbitFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- Original conditional Hilbert masses summed over ALL input representatives,
and original source ghost coefficients summed over ALL actual eligible output
witnesses in the frozen pending fibre. Both normalization cancellations are
derived, with no uniform-weight or occurrence-cardinality premise. -/
theorem memory_source_primitive_G_orbit_weighted_fibre
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g) (hmu : ∀ g p, 0 < mu g p)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld0 : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i)) :
    (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
        A life offset i x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x yc.1 yc.2)) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset i q rho N Vbig mu := by
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0
  let S := (Finset.univ : Finset
    (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
      (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x = y)
  have hrep : ∀ x ∈ S, ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i) := by
    intro x hx g
    have he := (Finset.mem_filter.mp hx).2
    have hmult := congrArg (fun z : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (z.2 g).2) he
    have hperm : (Green64Fock.fockToList ((x.2 g).2)).Perm
        (Green64Fock.fockToList ((x0.2 g).2)) := Multiset.coe_eq_coe.mp hmult
    exact hperm.trans (hOld0 g)
  have hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap :=
    Finset.mem_image.mpr ⟨x0, Finset.mem_univ _, rfl⟩
  have hm : (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (physicalOrbitMass_pos SP smallMod BP bigMod (J+ell) cap Vsmall mu hV hmu y hy)
  have hnorm :
      (∑ x ∈ S, (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ)) = 1 := by
    rw [← Finset.sum_div]
    have hsummass : (∑ x ∈ S,
        (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ)) =
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) := by
      simp only [physicalOrbitMass, Complex.ofReal_sum]
      rfl
    rw [hsummass, div_self hm]
  change (∑ x ∈ S, _ * _) = _
  calc
    _ = ∑ x ∈ S,
        ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
          (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ)) *
        memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset i q rho N Vbig mu := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [memory_source_primitive_G_fixed_input_weighted_fibre SP smallMod BP bigMod J ell cap
        A life offset i hinj hs hcap q rho N Vbig mu x (hrep x hx)]
    _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEInverse -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

/-- Exhaustive E store recovery from the ACTUAL output multiset. -/
theorem memory_E_actual_stores_recovered
    (hsupport : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA0 : ∀ p, i ∈ A p ↔ ∃ j, x.1 j = p)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hOut : (physicalPendingOutput modulus M B x sigma step c).Perm
      (memoryCanonicalPendingList modulus A life offset true (i+1))) :
    c.1 = memoryEStoreSlots modulus M B A life i x sigma := by
  ext j
  simp only [memoryEStoreSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  have hactive : i ∈ A (x.1 (sigma j)) := (hA0 _).mpr ⟨sigma j, rfl⟩
  constructor
  · intro hj
    let z : Green64Fock.Atom P modulus := ⟨x.1 (sigma j), (step : ZMod (modulus (x.1 (sigma j))))⟩
    have hz : z ∈ physicalPendingOutput modulus M B x sigma step c :=
      List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨j, Finset.mem_toList.mpr hj, rfl⟩))
    have hb := ((memory_pending_mem_iff modulus A life offset (i+1) true z).mp
      (hOut.mem_iff.mp hz)).1
    change memoryScheduleBefore (A (x.1 (sigma j))) (life (x.1 (sigma j))) (i+1) at hb
    cases hl : life (x.1 (sigma j)) with
    | none => simp only [hl, memoryScheduleBefore] at hb
    | some jd =>
      simp only [hl, memoryScheduleBefore] at hb
      exact ⟨hactive, hb.2.2, by omega⟩
  · intro hs
    have hbefore : memoryScheduleBefore (A (x.1 (sigma j))) (life (x.1 (sigma j))) (i+1) := by
      cases hl : life (x.1 (sigma j)) with
      | none => simp only [hl, memoryScheduleStore] at hs
      | some jd =>
        simp only [hl, memoryScheduleStore] at hs
        have hsupportp := hsupport (x.1 (sigma j))
        rw [hl] at hsupportp
        have hlo := (hsupportp.2.1 i hactive).1
        exact ⟨by omega, by omega, hs.2.1⟩
    let z : Green64Fock.Atom P modulus := ⟨x.1 (sigma j),
      memoryScheduleResidue (modulus (x.1 (sigma j)))
        (fun t => (offset t : ZMod (modulus (x.1 (sigma j))))) (life (x.1 (sigma j))) (i+1)⟩
    have hz : z ∈ physicalPendingOutput modulus M B x sigma step c :=
      hOut.mem_iff.mpr
        ((memory_pending_mem_iff modulus A life offset (i+1) true z).mpr ⟨hbefore, rfl⟩)
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hz
      have hspec := memory_E_old_atom_spec modulus M B A life offset i x hOld k
      have hp : (x.2.2 k).1 = x.1 (sigma j) := congrArg Sigma.fst he
      have hinactive : i ∉ A (x.2.2 k).1 := by
        have ha := hspec.1
        cases hl : life (x.2.2 k).1 with
        | none => simp only [hl, memoryScheduleAfter] at ha
        | some jd =>
          simp only [hl, memoryScheduleAfter] at ha
          exact ha.2.2
      exact False.elim (hinactive (hp.symm ▸ hactive))
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hz
      have hp : x.1 (sigma k) = x.1 (sigma j) := congrArg Sigma.fst he
      have heq : k = j := sigma.injective (hx hp)
      simpa only [heq] using Finset.mem_toList.mp hk


/-- Every actual OLD deletion in E is forced by the canonical target activity;
the injection has no independent combinatorial multiplicity. -/
theorem memory_E_actual_selected_old_recovered
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hleg : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c)
    (hOut : (physicalPendingOutput modulus M B x sigma step c).Perm
      (memoryCanonicalPendingList modulus A life offset true (i+1)))
    (k : Fin x.2.1.val) :
    k ∈ selectedOld modulus M B x c ↔
      memorySchedulePromote (A (x.2.2 k).1) (life (x.2.2 k).1) i := by
  have hspec := (memory_E_old_atom_spec modulus M B A life offset i x hOld k).1
  constructor
  · intro hk
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
    have hp := hleg.promoted_matches j
    rw [he] at hp
    have ha1 := (hA1 _).mpr ⟨tau j.1, hp⟩
    cases hl : life (x.2.2 k).1 with
    | none => simp only [hl, memoryScheduleAfter] at hspec
    | some jd =>
      simp only [hl, memoryScheduleAfter] at hspec
      exact ⟨hspec.2.2, ha1, hspec.1⟩
  · intro hp
    by_contra hk
    let z := Green64PhysicalEdge.translateAtom step (x.2.2 k)
    have hz : z ∈ physicalPendingOutput modulus M B x sigma step c :=
      List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨k,
        Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩), rfl⟩))
    have ha := ((memory_pending_mem_iff modulus A life offset (i+1) true z).mp
      (hOut.mem_iff.mp hz)).1
    change memoryScheduleBefore (A (x.2.2 k).1) (life (x.2.2 k).1) (i+1) at ha
    cases hl : life (x.2.2 k).1 with
    | none => simp only [hl, memoryScheduleBefore] at ha
    | some jd =>
      simp only [hl, memoryScheduleBefore] at ha
      simp only [hl, memorySchedulePromote] at hp
      exact ha.2.2 hp.2.1

/-- The literal store subset, promotion slots, and OLD injection are ALL
uniquely recovered on the original BigEdgeChoice carrier. -/
theorem memory_E_actual_choice_recovered
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA0 : ∀ p, i ∈ A p ↔ ∃ j, x.1 j = p)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hleg : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c)
    (hOut : (physicalPendingOutput modulus M B x sigma step c).Perm
      (memoryCanonicalPendingList modulus A life offset true (i+1))) :
    c = memoryPrimitiveEChoice modulus M B A life offset i hs x hOld target htarget sigma tau := by
  have hstores := memory_E_actual_stores_recovered modulus M B A life offset i
    hs x hx hA0 hOld sigma step c hOut
  have hselected := memory_E_actual_selected_old_recovered modulus M B A life offset i
    x hOld target hA1 shared sigma tau D step c hleg hOut
  have hpromotes : c.2.1 = memoryEPromoteSlots M A life i target tau := by
    ext j
    simp only [memoryEPromoteSlots, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      let jj : ↥c.2.1 := ⟨j, hj⟩
      have hsel : c.2.2 jj ∈ selectedOld modulus M B x c :=
        Finset.mem_image.mpr ⟨jj, Finset.mem_univ _, rfl⟩
      have hpr := (hselected _).mp hsel
      rw [← hleg.promoted_matches jj] at hpr
      exact hpr
    · intro hp
      let jj : ↥(memoryEPromoteSlots M A life i target tau) :=
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
      let k := memoryEPromotionIndex modulus M B A life offset i hs x hOld target tau jj
      have hkprime : (x.2.2 k).1 = target (tau j) :=
        congrArg Sigma.fst (memory_E_promotion_index_atom_exact modulus M B A life offset i
          hs x hOld target tau jj)
      have hk : k ∈ selectedOld modulus M B x c := (hselected k).mpr (hkprime.symm ▸ hp)
      obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hk
      have hmatch := hleg.promoted_matches l
      rw [he, hkprime] at hmatch
      have heq : l.1 = j := tau.injective (htarget hmatch)
      exact heq ▸ l.2
  rcases c with ⟨stores, ⟨promotes, emb⟩⟩
  dsimp only at hstores hpromotes
  subst stores
  subst promotes
  unfold memoryPrimitiveEChoice
  apply Prod.ext
  · rfl
  · apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Function.Embedding.ext
      intro j
      apply memory_E_old_prime_injective modulus M B A life offset i x hOld
      exact (hleg.promoted_matches j).symm.trans
        (congrArg Sigma.fst (memory_E_promotion_index_atom_exact modulus M B A life offset i
          hs x hOld target tau j)).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEFullInverse -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- Full backward E recovery on the original dependent source carrier.
Every frozen sampling coordinate, Nu label, auxiliary, BIG and SMALL endpoint
permutation survives literally. Only the store/OLD injection is reconstructed.
The output hypothesis is the actual canonical pending fibre condition. -/
theorem memory_source_primitive_E_full_inverse
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : ∀ g, Function.Injective (x.2 g).1)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j,
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z)
    (houtput : sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z =
      (iy.1, fun g => (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g),
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1) :
          Multiset (Green64Fock.Atom (BP g) (bigMod g)))))) :
    z = memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
      A life offset i hs x hOld iy z.1 z.2.1 z.2.2.1.sigmaBig z.2.2.1.tauBig
        z.2.2.2.1 z.2.2.2.2 := by
  let b := z.2.2.1
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1 o k
  have hsmall : b.smallTarget = iy.1 := congrArg Prod.fst houtput
  have htarget : ∀ g, (b.bigChoice g).1 =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) := by
    intro g
    exact congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) houtput
  have hpending : ∀ g, (physicalPendingOutput (bigMod g) (J+ell) (cap g)
      (x.2 g) (b.sigmaBig g) step (b.bigChoice g).2).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1)) := by
    intro g
    exact Multiset.coe_eq_coe.mp
      (congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (yy.2 g).2) houtput)
  have hbiglegal := hlegal.2.2.2.1
  have hc : ∀ g, (b.bigChoice g).2 =
      memoryPrimitiveEChoice (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
        (hs g) (x.2 g) (hOld g) _ (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g))
        (b.sigmaBig g) (b.tauBig g) := by
    intro g
    apply memory_E_actual_choice_recovered (bigMod g) (J+ell) (cap g)
      (A g) (life g) offset i (hs g) (x.2 g) (hx g) (hA0 g) (hOld g)
      (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
      (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g)) (hA1 g)
      (sourceBigShared J ell m (patterns z.1) g)
      (b.sigmaBig g) (b.tauBig g)
      (sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
        (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1) step
    · rw [← htarget g]
      exact hbiglegal g
    · exact hpending g
  have hbc : b.bigChoice = fun g =>
      (⟨Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g),
        memoryPrimitiveEChoice (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
          (hs g) (x.2 g) (hOld g) _ (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g))
          (b.sigmaBig g) (b.tauBig g)⟩ : BigPhysicalBranch (bigMod g) (J+ell) (cap g) (x.2 g)) := by
    funext g
    exact Prod.ext (htarget g) (hc g)
  rcases z with ⟨nu, aux, branch, ss, st⟩
  cases branch with
  | mk bs bt choices small =>
    dsimp only [b] at hsmall hbc
    unfold memoryPrimitiveESourceChoice
    simp only
    rw [hbc, hsmall]
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEWeightedFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- Original sampling coordinates only. OLD choices are not added to this frame. -/
abbrev MemoryPrimitiveEFrame :=
  (Σ nu : Nu, SourceBigAux BP J m (patterns nu)) ×
    BigGroupPerm (BG := BG) (J+ell) × BigGroupPerm (BG := BG) (J+ell) ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)

def memoryPrimitiveEFrameOf
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x) :
    MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns :=
  (⟨z.1, z.2.1⟩, z.2.2.1.sigmaBig, z.2.2.1.tauBig, z.2.2.2.1, z.2.2.2.2)

def memoryPrimitiveEFrameChoice
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x :=
  memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
    A life offset i hs x hOld iy f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2

def memoryPrimitiveECanonicalOutput
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell) :
    FullPhysicalOutput SP smallMod BP bigMod (J+ell) :=
  (iy.1, fun g => (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g),
    (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1) :
      Multiset (Green64Fock.Atom (BP g) (bigMod g)))))

/-- Full actual indexed E slice: preserves zero coefficients, Nu, auxiliary,
all four permutation families, actual SMALL target and actual birth test. -/
def memoryPrimitiveEFixedFrameFibre
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (o k : ℤ) (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    Finset (FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x) :=
  Finset.univ.filter (fun z =>
    (⟨x, z⟩ : Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xx) ∈
      physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod J ell m cap patterns o k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memoryBornBeforeValues BP bigMod life (i+1)) ∧
    memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns x z = f ∧
    sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z =
      memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell A life offset i iy)

/-- Decisive exhaustive E reconstruction on each complete original frame.
This uses the predecessor inverse rather than positing a fibre bijection. -/
theorem memory_source_primitive_E_fixed_frame_mem_iff
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : ∀ g, Function.Injective (x.2 g).1)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j,
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (o k : ℤ) (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x) :
    z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
      A life offset i x iy o k f ↔
    z = memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
      A life offset i hs x hOld iy f ∧
    memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
      A life offset i hs x hOld iy f ∈
      memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
        A life offset i x iy o k f := by
  constructor
  · intro hz
    have hp := (Finset.mem_filter.mp hz).2
    have hleg := (Finset.mem_filter.mp hp.1).2.2.1
    have hinv := memory_source_primitive_E_full_inverse SP smallMod BP bigMod J ell m
      cap patterns A life offset i hs x hx hA0 hOld iy hA1 o k z hleg hp.2.2
    have he : z = memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy f := by
      rw [← hp.2.1]
      exact hinv
    exact ⟨he, he ▸ hz⟩
  · rintro ⟨rfl, hz⟩
    exact hz

/-- Complete ORIGINAL E coefficient sum at a fixed frame, including all zero
terms. No factorial, OLD multiplicity or conditional mass is silently inserted. -/
theorem memory_source_primitive_E_fixed_frame_weighted_sum
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : ∀ g, Function.Injective (x.2 g).1)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j,
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
        A life offset i x iy o k f,
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig mu Knu zeta theta o k x z) =
    if memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy f ∈
      memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
        A life offset i x iy o k f then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig mu Knu zeta theta o k x
        (memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
          A life offset i hs x hOld iy f)
    else 0 := by
  let c := memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
    A life offset i hs x hOld iy f
  have hm := memory_source_primitive_E_fixed_frame_mem_iff SP smallMod BP bigMod
    J ell m cap patterns A life offset i hs x hx hA0 hOld iy hA1 o k f
  by_cases hc : c ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap
      patterns A life offset i x iy o k f
  · have he : memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap
        patterns A life offset i x iy o k f = {c} := by
      ext z
      rw [hm z]
      change (z = c ∧ c ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap
        patterns A life offset i x iy o k f) ↔ z ∈ ({c} : Finset _)
      simp only [hc, and_true, Finset.mem_singleton]
    rw [if_pos hc, he, Finset.sum_singleton]
  · have he : memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap
        patterns A life offset i x iy o k f = ∅ := by
      ext z
      rw [hm z]
      change (z = c ∧ c ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap
        patterns A life offset i x iy o k f) ↔ z ∈ (∅ : Finset _)
      simp [hc]
    rw [if_neg hc, he, Finset.sum_empty]
end Green64FullPhysicalE

end

end

/-! ## MemorySourceGWeightedFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Exact source specialization: support and Hilbert positivity are derived
from the original domain and nonzero frozen lifespan terms. The equality sums
the actual indexed G branches with their original source mu-tilde and original
conditional Fock masses. It is a local weighted fibre, not MemoryIdentityTarget. -/
theorem memory_source_canonical_G_weighted_fibre
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R i : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (2*R+1))
    (offset : ℕ → ℤ)
    (hn : ∀ g p, memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q (2*R))
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (2*R+1) (life g p) ≠ 0)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld0 : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i)) :
    (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
        A life offset i x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i Vbig
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x yc.1 yc.2)) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset i q rho (2*R) Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) := by
  apply memory_source_primitive_G_orbit_weighted_fibre SP smallMod BP bigMod J ell cap
    A life offset i hdomain.big_injective
  · intro g p
    exact memory_frozen_nonzero_schedule_support (bigMod g p) (sourceVisitEta q (2*R))
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (2*R+1) (life g p) (hn g p)
  · exact hdomain.cap_saturated
  · exact hdomain.Vsmall_pos
  · intro g p
    exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hdomain.q_pos) (le_of_lt hdomain.q_lt_one)
      (hdomain.Vbig_pos g) (hdomain.big_above_visits g p)
  · exact hOld0
end Green64FullPhysicalE

end

end

/-! ## PhysicalOrientedInitialRootFibreCancellation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The ROOT's independent initial physical ordered Fock
representative is integrated by its true Hilbert mass. Summing that
representative over its *actual* symmetric Fock orbit cancels the
subsequent G_0 input conditional-orbit denominator exactly once.
Repeated identical Fock atoms are retained in the orbit fibre.

This is the missing root-level disintegration required before mapping
the full finite indexed trace to one PhysicalFiniteActualWitnessPath,
whose before(0) is the actual G_0 input representative. -/
theorem physical_initial_root_Fock_fibre_cancel
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g : SG, 0 < Vsmall g)
    (hmu : ∀ g : BG, ∀ p : BP g, 0 < muBig g p)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (hxy : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x = y) :
    (∑ x0 ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap x0 = y,
      (fullPhysicalMass SP smallMod BP bigMod (J+ell)
         cap Vsmall muBig x0 : ℂ) *
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell)
        cap Vsmall muBig x : ℂ) /
       (physicalOrbitMass SP smallMod BP bigMod
         (J+ell) cap Vsmall muBig y : ℂ))) =
    (fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig x : ℂ) := by
  have hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod
      (J+ell) cap := Finset.mem_image.mpr
    ⟨x, Finset.mem_univ _, hxy⟩
  have hpos : 0 < physicalOrbitMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig y :=
    physicalOrbitMass_pos SP smallMod BP bigMod (J+ell)
      cap Vsmall muBig hV hmu y hy
  have hden : (physicalOrbitMass SP smallMod BP bigMod
    (J+ell) cap Vsmall muBig y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  calc
    _ = (∑ x0 ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap x0 = y,
        (fullPhysicalMass SP smallMod BP bigMod (J+ell)
          cap Vsmall muBig x0 : ℂ)) *
        ((fullPhysicalMass SP smallMod BP bigMod
          (J+ell) cap Vsmall muBig x : ℂ) /
          (physicalOrbitMass SP smallMod BP bigMod
            (J+ell) cap Vsmall muBig y : ℂ)) := by
            rw [Finset.sum_mul]
    _ = (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig y : ℂ) *
        ((fullPhysicalMass SP smallMod BP bigMod
          (J+ell) cap Vsmall muBig x : ℂ) /
          (physicalOrbitMass SP smallMod BP bigMod
            (J+ell) cap Vsmall muBig y : ℂ)) := by
          rw [physicalOrbitMass, Complex.ofReal_sum]
    _ = _ := by field_simp [hden]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootVacuumFibreUnique -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- At a genuine physical ROOT vacuum, the projected SMALL Haar
and BIG active state determines the FULL ordered physical Fock
representative uniquely: every BIG Fock group has the sole j=0
vacuum state. No positivity hypothesis or artificial prior
choice of an ordering is needed. -/
theorem physical_root_vacuum_projection_unique
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hxy : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap y)
    (hv : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) = 1) :
    x = y := by
  have hZero : ∀ g : BG,
      Green64Fock.fockMultiset (((x.2 g).2)) = 0 := by
    have hv' : (if (∀ g : BG,
        ((physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x).2 g).2 = 0) then
      (1:ℂ) else 0) = 1 := hv
    by_cases hz : ∀ g : BG,
        ((physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x).2 g).2 = 0
    · exact hz
    · simp [hz] at hv'
  have hZeroY : ∀ g : BG,
      Green64Fock.fockMultiset (((y.2 g).2)) = 0 := by
    intro g
    have hg := congrArg
      (fun o : FullPhysicalOutput SP smallMod BP bigMod
        (J+ell) => (o.2 g).2) hxy
    exact hg.symm.trans (hZero g)
  have hSmall : x.1 = y.1 := congrArg
    (fun o : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      o.1) hxy
  have hActive (g : BG) : (x.2 g).1 = (y.2 g).1 := congrArg
    (fun o : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (o.2 g).1) hxy
  apply Prod.ext hSmall
  funext g
  apply Prod.ext (hActive g)
  have hx : (x.2 g).2 =
      Green64Fock.vacuumState
        (Green64Fock.Atom (BP g) (bigMod g)) (cap g) :=
    Green64Fock.fockMultiset_empty_implies_vacuum
      (x.2 g).2 (hZero g)
  have hy : (y.2 g).2 =
      Green64Fock.vacuumState
        (Green64Fock.Atom (BP g) (bigMod g)) (cap g) :=
    Green64Fock.fockMultiset_empty_implies_vacuum
      (y.2 g).2 (hZeroY g)
  exact hx.trans hy.symm

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootVacuumFibreSingleton -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The genuine original ROOT physical Fock fibre of an initial
vacuum has exactly one ordered physical representative.
No OLD Fock multiplicity exists yet, so it cannot acquire an
unwanted factor 1/j! or a second orbit normalization. -/
theorem physical_root_vacuum_input_fibre_singleton
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hv : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) = 1) :
    actualPhysicalInputFibre SP smallMod BP bigMod
      (J+ell) cap
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) = {x} := by
  ext z
  simp only [actualPhysicalInputFibre, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    exact (physical_root_vacuum_projection_unique
      SP smallMod BP bigMod J ell cap x z h.symm hv).symm
  · intro hz
    subst z
    rfl

/-- On a TRUE SOURCE root vacuum, even the first G_0 Hilbert
input conditional-probability weight equals exactly 1. The
initial Fock orbit is a singleton, not a duplicated parameter. -/
theorem physical_root_vacuum_input_ratio_one
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hv : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) = 1) :
    ((fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig x : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap x) : ℂ)) = 1 := by
  have h := physical_oriented_full_input_fibre_uniform_weight
    SP smallMod BP bigMod (J+ell) cap Vsmall muBig hV hmu x
  dsimp only at h
  rw [physical_root_vacuum_input_fibre_singleton
    SP smallMod BP bigMod J ell cap x hv] at h
  simpa using h

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootNonzeroWitnessSupport -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The REAL finite source root support of nonzero oriented physical
witness paths. Every original witness with zero complex contribution
is excluded by its actual source scalar, not by a guessed combinatorial
legality condition or a set of numerical prime values. -/
noncomputable def physicalOrientedRootNonzeroIndices
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    Finset (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
  letI : Fintype (PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  Finset.univ.filter (fun xt =>
    physicalOrientedRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0)

/-- The genuine corrected oriented physical ROOT moment is a
finite sum of all and ONLY NONZERO original indexed physical paths.
The theorem uses the previously kernel-checked exhaustive carrier,
not an arbitrary family W. -/
theorem physical_oriented_root_nonzero_witness_sum_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R =
    ∑ xt ∈ physicalOrientedRootNonzeroIndices SP smallMod
        BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
        zeta theta k R,
      physicalOrientedRootIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu
        zeta theta k R xt := by
  letI : Fintype (PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  rw [physical_oriented_finite_root_full_indexed_exact
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R]
  unfold physicalOrientedFullRootIndexedSum
    physicalOrientedRootNonzeroIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro xt hxt
  by_cases hn : physicalOrientedRootIndexedWeight SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
    zeta theta k R xt ≠ 0
  · simp [hn]
  · simp at hn
    simp [hn]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootContributingConditions -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
/-- Every NONZERO original root indexed source witness has the
genuine physical root vacuum and the ORIGINAL global numeric
distinct-birth condition. This is deduced from actual scalar
support, not added as a separate assumption on source witnesses. -/
theorem physical_oriented_root_nonzero_initial_conditions
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R)
    (hw : physicalOrientedRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R xt ≠ 0) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) = 1 ∧
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap xt.1).Nodup := by
  have hBirth : (physicalInitialBirths SP smallMod BP bigMod
      J ell cap xt.1).Nodup := by
    by_contra hn
    have hz : physicalOrientedRootIndexedWeight SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig
      Knu zeta theta k R xt = 0 := by
      simp [physicalOrientedRootIndexedWeight, hn]
    exact hw hz
  have hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) = 1 := by
    by_cases hz : ∀ g : BG,
      ((physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1).2 g).2 = 0
    · simp [physicalVacuum, hz]
    · have hzero : physicalOrientedRootIndexedWeight SP smallMod
        BP bigMod J ell m cap patterns q rho Vsmall Vbig
        Knu zeta theta k R xt = 0 := by
        simp [physicalOrientedRootIndexedWeight, physicalVacuum, hz]
      exact False.elim (hw hzero)
  exact ⟨hVac,hBirth⟩

/-- Therefore the root's independent initial G0 ordered Fock
representative is unique on EVERY contributing source witness;
its only possible Fock-sector mass is the true vacuum j=0 mass. -/
theorem physical_oriented_root_contributing_first_Fock_unique
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod
      BP bigMod J ell m cap patterns k R)
    (hw : physicalOrientedRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R xt ≠ 0)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hproj : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) :
    x = xt.1 :=
  physical_root_vacuum_projection_unique
    SP smallMod BP bigMod J ell cap xt.1 x hproj.symm
    (physical_oriented_root_nonzero_initial_conditions
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt hw).1 |>.symm

end Green64FullPhysicalE

end

/-! ## MemorySourceRootConditions -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
/-- Nonzero contributing trace for the unchanged source-correct root weight. -/
abbrev MemorySourceContributingRootTrace
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :=
  {xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R //
    memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0}

/-- Every NONZERO original root indexed source witness has the
genuine physical root vacuum and the ORIGINAL global numeric
distinct-birth condition. This is deduced from actual scalar
support, not added as a separate assumption on source witnesses. -/
theorem memory_source_root_nonzero_initial_conditions
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R)
    (hw : memorySourceRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R xt ≠ 0) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) = 1 ∧
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap xt.1).Nodup := by
  have hBirth : (physicalInitialBirths SP smallMod BP bigMod
      J ell cap xt.1).Nodup := by
    by_contra hn
    have hz : memorySourceRootIndexedWeight SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig
      Knu zeta theta k R xt = 0 := by
      simp [memorySourceRootIndexedWeight, hn]
    exact hw hz
  have hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) = 1 := by
    by_cases hz : ∀ g : BG,
      ((physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1).2 g).2 = 0
    · simp [physicalVacuum, hz]
    · have hzero : memorySourceRootIndexedWeight SP smallMod
        BP bigMod J ell m cap patterns q rho Vsmall Vbig
        Knu zeta theta k R xt = 0 := by
        simp [memorySourceRootIndexedWeight, physicalVacuum, hz]
      exact False.elim (hw hzero)
  exact ⟨hVac,hBirth⟩

/-- Therefore the root's independent initial G0 ordered Fock
representative is unique on EVERY contributing source witness;
its only possible Fock-sector mass is the true vacuum j=0 mass. -/
theorem memory_source_root_first_Fock_unique
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod
      BP bigMod J ell m cap patterns k R)
    (hw : memorySourceRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R xt ≠ 0)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hproj : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap xt.1) :
    x = xt.1 :=
  physical_root_vacuum_projection_unique
    SP smallMod BP bigMod J ell cap xt.1 x hproj.symm
    (memory_source_root_nonzero_initial_conditions
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt hw).1 |>.symm

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootGoodTraceType -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- This is the REAL FINITE rooted physical source witness type,
not an arbitrary W-index family. Each element is a fully indexed
legal original-oriented G0/E0/.../GN trace with a nonzero original
physical Hilbert weighted complex coefficient. The final vacuum,
initial vacuum, valid ghost input/output and global numeric
distinctness follow from the source operator support. -/
abbrev PhysicalOrientedContributingRootTrace
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :=
  {xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R //
    xt ∈ physicalOrientedRootNonzeroIndices SP smallMod BP
      bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R}

@[reducible] noncomputable def
    physicalOrientedContributingRootTraceFintype
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    Fintype (PhysicalOrientedContributingRootTrace SP smallMod
      BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) := by
  letI := physicalOrientedRootIndexedTraceFintype SP smallMod
    BP bigMod J ell m cap patterns k R
  infer_instance
/-- The corrected source moment is now an EXACT FINITE
Fintype.sum over genuinely contributing complete oriented
physical witness paths. This supplies an ACTUAL, independently
constructed W type for subsequent source-to-Hlit disintegration.

Remaining debt: map these nonzero recursive traces (including each
ordered representative, terminal G and seen register) to the typed
PhysicalFiniteActualWitnessPath carrier and remove any pure Fock
representative multiplicity, not assume that correspondence. -/
theorem physical_oriented_root_contributing_Fintype_sum_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R =
    ∑ w : PhysicalOrientedContributingRootTrace SP smallMod
       BP bigMod J ell m cap patterns
       q rho Vsmall Vbig Knu zeta theta k R,
      physicalOrientedRootIndexedWeight SP smallMod BP bigMod
       J ell m cap patterns q rho Vsmall Vbig Knu
       zeta theta k R w.val := by
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod
      BP bigMod J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod
      BP bigMod J ell m cap patterns k R
  letI := physicalOrientedContributingRootTraceFintype
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R
  rw [physical_oriented_root_nonzero_witness_sum_exact
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R]
  exact (finite_indexed_legal_subtype_sum
    (physicalOrientedRootNonzeroIndices SP smallMod BP bigMod
      J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R)
    (physicalOrientedRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R)).symm

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceOccurrenceArrays -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Extract the COMPLETE G witness at every actual chronological
visit 0,...,remaining, including terminal G. The carrier is
still the original indexed physical G OLD/ghost witness, not a
quotient or an assumed physical transition. -/
noncomputable def physicalOrientedTraceGWitness (k : ℤ) :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen) →
    Fin (remaining+1) →
      PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
        J ell cap
  | 0, _, _, _, t, _ => t.val
  | n+1, start, _, _, ⟨ab, tail⟩, j =>
      Fin.cases ab.val.1
        (fun i => physicalOrientedTraceGWitness k n (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns (physicalAlternatingSign start)
            k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns _ ab.val) tail i) j

/-- Extract original E input ordered Fock representative and its
COMPLETE independently permuted oriented source choice at each E
visit 0,...,remaining-1. Source ν/free-D labels and OLD promotion
injections are retained as original occurrences. -/
noncomputable def physicalOrientedTraceEWitness (k : ℤ) :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen) →
    Fin remaining →
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
        J ell m cap patterns
  | 0, _, _, _, _, j => j.elim0
  | n+1, start, _, _, ⟨ab,tail⟩, j =>
      Fin.cases ab.val.2
        (fun i => physicalOrientedTraceEWitness k n (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns (physicalAlternatingSign start)
            k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns _ ab.val) tail i) j

/-- The real chronological numerical prime seen register at each
G visit. This matches the global birth-set update made by each
original G/E witness; no independently chosen ledger is inserted. -/
noncomputable def physicalOrientedTraceSeen (k : ℤ) :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen) →
    Fin (remaining+1) → Finset ℕ
  | 0, _, _, seen, _, _ => seen
  | n+1, start, _, seen, ⟨ab,tail⟩, j =>
      Fin.cases seen
        (fun i => physicalOrientedTraceSeen k n (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns (physicalAlternatingSign start)
            k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail i) j

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceInitialFields -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original G_0 input of the indexed finite witness trace projects
to precisely the physical source orbit passed to the root operation.
The equality is extracted from the ACTUAL G legal fibre, never
postulated or obtained by an arbitrary Markov-type source map. -/
theorem physical_oriented_trace_first_G_projection
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen) :
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t 0).1) =
    y := by
  cases remaining with
  | zero =>
    change physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap t.val.1 = y
    exact (Finset.mem_filter.mp t.property).2.1
  | succ n =>
    rcases t with ⟨ab, tail⟩
    change physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap ab.val.1.1 = y
    have hG := (Finset.mem_sigma.mp ab.property).1
    exact (Finset.mem_filter.mp hG).2.1

/-- Actual source global seen-birth set at the first G visit
equals the caller's original numerical initial-birth seen set. -/
theorem physical_oriented_trace_first_seen
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen) :
    physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t 0 =
      seen := by
  cases remaining with
  | zero => rfl
  | succ n =>
    rcases t with ⟨ab, tail⟩
    rfl

/-- The first E witness input is a G-output Fock state with
exactly the same projected memory MULTISET, SMALL Haar residues
and active prime arrays as the real first G-output representative.
Its OLD ordering may still differ: that is the physical quotient
which carries the true conditional Fock orbit mass. -/
theorem physical_oriented_trace_first_E_input_projection
    (k : ℤ) (n start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k (n+1) start y seen) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).1) =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).2.1) := by
  rcases t with ⟨ab, tail⟩
  change physicalFockProjection SP smallMod BP bigMod
    (J+ell) cap ab.val.2.1 =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap ab.val.1.2.1
  have hE := (Finset.mem_sigma.mp ab.property).2
  exact (Finset.mem_filter.mp hE).2.1

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceAllEInput -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- At EVERY real E_i in a complete indexed finite witness trace,
the E input ordered physical Fock representative projects to the
G-output orbit selected at the same visit; the OLD ordering itself
is intentionally not equated. This is a true finite Fock-multiset
glue, including repeated physical atoms. -/
theorem physical_oriented_trace_all_E_inputs
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin remaining) :
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t j).1) =
    physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t
        (Fin.castSucc j)).2.1) := by
  induction remaining generalizing start y seen with
  | zero =>
    exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    cases j using Fin.cases with
    | zero =>
      exact physical_oriented_trace_first_E_input_projection
        SP smallMod BP bigMod J ell m cap patterns
        k n start y seen ⟨ab,tail⟩
    | succ j =>
      let yNext := physicalOrientedGEIndexedOutput SP smallMod BP
        bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val
      let seenNext := physicalOrientedGEIndexedNextSeen
        SP smallMod BP bigMod J ell m cap patterns
        seen ab.val
      exact ih (start+1) yNext seenNext tail j

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceAllNextOutput -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Every actual next G input state in the recursively indexed
original physical trace has exactly the projected active/SMALL Haar/
Fock memory output of the previous genuine oriented E witness.

The source E-output is matched to the NEXT G-input Fock orbit,
never equated to an arbitrarily chosen ordered representative.
This is the missing E_output glue in PhysicalFiniteActualWitnessPath
at ALL visits, with correct source-alternating sign. -/
theorem physical_oriented_trace_all_E_outputs
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin remaining) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t
        (Fin.succ j)).1) =
    sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t j).1)
      (physicalAlternatingSign (start+j.val)) k
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t j).2) := by
  induction remaining generalizing start y seen with
  | zero => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP
        bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen
        SP smallMod BP bigMod J ell m cap patterns
        seen ab.val
    cases j using Fin.cases with
    | zero =>
      change physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1)
          yNext seenNext tail 0).1) = yNext
      exact physical_oriented_trace_first_G_projection
        SP smallMod BP bigMod J ell m cap patterns
        k n (start+1) yNext seenNext tail
    | succ j =>
      change physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1) yNext seenNext tail j.succ).1) =
        sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns
          ((physicalOrientedTraceEWitness SP smallMod BP bigMod
            J ell m cap patterns k n (start+1) yNext seenNext tail j).1)
          (physicalAlternatingSign (start + (j.val+1))) k
          ((physicalOrientedTraceEWitness SP smallMod BP bigMod
            J ell m cap patterns k n (start+1) yNext seenNext tail j).2)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (start+1) yNext seenNext tail j)

end Green64FullPhysicalE

end

/-! ## MemorySourceRootInitialBridge -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The actual nonzero rooted carrier provides the complete initial
conditions needed for its eventual chronological witness path.
In particular the root state, not a freely chosen input, determines
the initial seen register and the very first G-input orbit. -/
theorem memory_source_root_initial_bridge
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap w.val.1).Nodup ∧
    (∀ g : BG, Green64Fock.fockMultiset ((w.val.1.2 g).2) = 0) ∧
    physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset w.val.2 0 =
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset ∧
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap w.val.1).toFinset w.val.2 0).1) =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1 := by
  have hw : memorySourceRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    w.property
  obtain ⟨hv, hn⟩ := memory_source_root_nonzero_initial_conditions
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w.val hw
  refine ⟨hn, ?_, ?_, ?_⟩
  · by_contra hn
    have hzero : physicalVacuum SP smallMod BP bigMod J ell
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap w.val.1) = 0 := by
      simp [physicalVacuum, physicalFockProjection, hn]
    rw [hzero] at hv
    norm_num at hv
  · exact physical_oriented_trace_first_seen
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      _ _ w.val.2
  · exact physical_oriented_trace_first_G_projection
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      _ _ w.val.2

/-- The first actual indexed G input is not merely orbit-equivalent:
the initial vacuum forces its ordered Fock representative to be
exactly the root state, removing an otherwise possible fibre choice. -/
theorem memory_source_root_first_G_state_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    (physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset w.val.2 0).1 = w.val.1 := by
  have hw : memorySourceRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    w.property
  apply memory_source_root_first_Fock_unique
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w.val hw
  exact (memory_source_root_initial_bridge
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w).2.2.2
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootWitnessInitialBridge -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The actual nonzero rooted carrier provides the complete initial
conditions needed for its eventual chronological witness path.
In particular the root state, not a freely chosen input, determines
the initial seen register and the very first G-input orbit. -/
theorem physical_oriented_contributing_root_initial_bridge
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : PhysicalOrientedContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap w.val.1).Nodup ∧
    (∀ g : BG, Green64Fock.fockMultiset ((w.val.1.2 g).2) = 0) ∧
    physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset w.val.2 0 =
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset ∧
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap w.val.1).toFinset w.val.2 0).1) =
      physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1 := by
  have hw : physicalOrientedRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    (Finset.mem_filter.mp w.property).2
  obtain ⟨hv, hn⟩ := physical_oriented_root_nonzero_initial_conditions
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w.val hw
  refine ⟨hn, ?_, ?_, ?_⟩
  · by_contra hn
    have hzero : physicalVacuum SP smallMod BP bigMod J ell
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap w.val.1) = 0 := by
      simp [physicalVacuum, physicalFockProjection, hn]
    rw [hzero] at hv
    norm_num at hv
  · exact physical_oriented_trace_first_seen
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      _ _ w.val.2
  · exact physical_oriented_trace_first_G_projection
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      _ _ w.val.2

/-- The first actual indexed G input is not merely orbit-equivalent:
the initial vacuum forces its ordered Fock representative to be
exactly the root state, removing an otherwise possible fibre choice. -/
theorem physical_oriented_contributing_first_G_state_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : PhysicalOrientedContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    (physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap w.val.1).toFinset w.val.2 0).1 = w.val.1 := by
  have hw : physicalOrientedRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    (Finset.mem_filter.mp w.property).2
  apply physical_oriented_root_contributing_first_Fock_unique
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w.val hw
  exact (physical_oriented_contributing_root_initial_bridge
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w).2.2.2
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceFirstPairEligible -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Real first E witness is legal and globally birth eligible,
by membership in the original dependent G/E choice carrier. -/
theorem physical_oriented_trace_first_pair_eligible
    (k : ℤ) (n start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k (n+1) start y seen) :
    physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).1)
      seen
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).2.2) ∧
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).1)
      (physicalAlternatingSign start) k
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).2) ∧
    orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k (n+1) start y seen t 0).1)
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k (n+1) start y seen t 0).2.2)).toFinset)
      ((physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (n+1) start y seen t 0).2) := by
  rcases t with ⟨ab, tail⟩
  have hpair := ab.property
  have hG := (Finset.mem_sigma.mp hpair).1
  have hE := (Finset.mem_sigma.mp hpair).2
  exact ⟨(Finset.mem_filter.mp hG).2.2,
    (Finset.mem_filter.mp hE).2.2.1,
    (Finset.mem_filter.mp hE).2.2.2⟩
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceSeenUpdate -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exact chronological birth-register update at every genuine E visit. -/
theorem physical_oriented_trace_all_seen_updates
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin remaining) :
    physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
      k remaining start y seen t (Fin.succ j) =
    (physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
      k remaining start y seen t (Fin.castSucc j) ∪
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k remaining start y seen t
          (Fin.castSucc j)).1)
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k remaining start y seen t
          (Fin.castSucc j)).2.2)).toFinset) ∪
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns
        ((physicalOrientedTraceEWitness SP smallMod BP bigMod
          J ell m cap patterns k remaining start y seen t j).2)).toFinset := by
  induction remaining generalizing start y seen with
  | zero => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    refine Fin.cases ?_ (fun j => ?_) j
    · change physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
        k n (start+1) yNext seenNext tail (0 : Fin (n+1)) = seenNext
      cases n with
      | zero => rfl
      | succ n => rfl
    · exact ih (start+1) yNext seenNext tail j
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceAllPairEligible -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The actual G/E choices are legal at every chronological visit. -/
theorem physical_oriented_trace_all_pair_eligible
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin remaining) :
    let g := physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t (Fin.castSucc j)
    let e := physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t j
    let s := physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t (Fin.castSucc j)
    physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap
      g.1 s g.2.2 ∧
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns e.1
      (physicalAlternatingSign (start+j.val)) k e.2 ∧
    orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns
      (s ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap g.1 g.2.2).toFinset) e.2 := by
  induction remaining generalizing start y seen with
  | zero => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    cases j using Fin.cases with
    | zero =>
      exact physical_oriented_trace_first_pair_eligible SP smallMod BP bigMod
        J ell m cap patterns k n start y seen ⟨ab,tail⟩
    | succ j =>
      have hidx : start + (Fin.succ j).val = (start+1) + j.val := by
        simp only [Fin.val_succ]
        omega
      rw [hidx]
      exact ih (start+1) yNext seenNext tail j
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceAllGNonzero -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original indexed G branch scalar at any G visit, terminal included. -/
noncomputable def physicalOrientedTraceGTerm
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin (remaining+1)) : ℂ :=
  let g := physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t j
  physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
    q rho N (start+j.val) Vbig muBig g.1 g.2.1 g.2.2

/-- Nonzero source trace weight implies nonzero G scalar at all visits,
including the separate terminal G_N witness. -/
theorem physical_oriented_trace_all_G_nonzero
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hw : physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t ≠ 0)
    (j : Fin (remaining+1)) :
    physicalOrientedTraceGTerm SP smallMod BP bigMod J ell m
      cap patterns q rho N Vbig muBig k remaining start y seen t j ≠ 0 := by
  induction remaining generalizing start y seen with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      change physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N start Vbig muBig t.val.1 t.val.2.1 t.val.2.2 ≠ 0
      intro hz
      apply hw
      change physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
        J ell cap q rho Vsmall Vbig muBig N start y t.val = 0
      simp [physicalOrientedIndexedTerminalWeight, hz]
    | succ j => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    have hpair : physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      Knu ((start : ℝ)*zeta) theta (physicalAlternatingSign start)
      k y ab.val ≠ 0 := by
      intro hz
      apply hw
      simp [physicalOrientedIndexedTraceWeight, hz]
    have htail : physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N n (start+1) yNext seenNext tail ≠ 0 := by
      intro hz
      apply hw
      change (physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ)*zeta) theta (physicalAlternatingSign start)
        k y ab.val) *
        (physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N n (start+1) yNext seenNext tail) = 0
      rw [hz, mul_zero]
    cases j using Fin.cases with
    | zero =>
      have hG : physicalGBranchTerm SP smallMod BP bigMod
        (J+ell) cap q rho N start Vbig muBig
        ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0 := by
        intro hz
        apply hpair
        simp [physicalOrientedGEIndexedWeight, hz]
      exact hG
    | succ j =>
      have hidx : start + (Fin.succ j).val = (start+1) + j.val := by
        simp only [Fin.val_succ]
        omega
      unfold physicalOrientedTraceGTerm
      rw [hidx]
      exact ih (start+1) yNext seenNext tail htail j
end Green64FullPhysicalE

end

/-! ## MemorySourceTraceGNonzero -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Nonzero source trace weight implies nonzero G scalar at all visits,
including the separate terminal G_N witness. -/
theorem memory_source_trace_all_G_nonzero
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hw : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t ≠ 0)
    (j : Fin (remaining+1)) :
    physicalOrientedTraceGTerm SP smallMod BP bigMod J ell m
      cap patterns q rho N Vbig muBig k remaining start y seen t j ≠ 0 := by
  induction remaining generalizing start y seen with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      change physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N start Vbig muBig t.val.1 t.val.2.1 t.val.2.2 ≠ 0
      intro hz
      apply hw
      change physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
        J ell cap q rho Vsmall Vbig muBig N start y t.val = 0
      simp [physicalOrientedIndexedTerminalWeight, hz]
    | succ j => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    have hpair : physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta (physicalAlternatingSign start)
      k y ab.val ≠ 0 := by
      intro hz
      apply hw
      simp [memorySourceIndexedTraceWeight, hz]
    have htail : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N n (start+1) yNext seenNext tail ≠ 0 := by
      intro hz
      apply hw
      change (physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta (physicalAlternatingSign start)
        k y ab.val) *
        (memorySourceIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N n (start+1) yNext seenNext tail) = 0
      rw [hz, mul_zero]
    cases j using Fin.cases with
    | zero =>
      have hG : physicalGBranchTerm SP smallMod BP bigMod
        (J+ell) cap q rho N start Vbig muBig
        ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0 := by
        intro hz
        apply hpair
        simp [physicalOrientedGEIndexedWeight, hz]
      exact hG
    | succ j =>
      have hidx : start + (Fin.succ j).val = (start+1) + j.val := by
        simp only [Fin.val_succ]
        omega
      unfold physicalOrientedTraceGTerm
      rw [hidx]
      exact ih (start+1) yNext seenNext tail htail j
end Green64FullPhysicalE

end

/-! ## MemorySourceRootGNonzero -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Nonzero original rooted scalar forces every true G_i,
including the independent terminal G_(2R), to be nonzero. -/
theorem memory_source_root_all_G_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R)
    (j : Fin (2*R+1)) :
    physicalOrientedTraceGTerm SP smallMod BP bigMod J ell m
      cap patterns q rho (2*R) Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 j ≠ 0 := by
  have hw : memorySourceRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    w.property
  have htrace : memorySourceIndexedTraceWeight
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k (2*R) (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 ≠ 0 := by
    intro hz
    apply hw
    simp [memorySourceRootIndexedWeight, hz]
  exact memory_source_trace_all_G_nonzero SP smallMod BP bigMod
    J ell m cap patterns q rho (2*R) Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k (2*R) 0
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      w.val.1).toFinset w.val.2 htrace j
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedContributingAllGNonzero -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Nonzero original rooted scalar forces every true G_i,
including the independent terminal G_(2R), to be nonzero. -/
theorem physical_oriented_contributing_all_G_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : PhysicalOrientedContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R)
    (j : Fin (2*R+1)) :
    physicalOrientedTraceGTerm SP smallMod BP bigMod J ell m
      cap patterns q rho (2*R) Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 j ≠ 0 := by
  have hw : physicalOrientedRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    (Finset.mem_filter.mp w.property).2
  have htrace : physicalOrientedIndexedTraceWeight
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k (2*R) (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 ≠ 0 := by
    intro hz
    apply hw
    simp [physicalOrientedRootIndexedWeight, hz]
  exact physical_oriented_trace_all_G_nonzero SP smallMod BP bigMod
    J ell m cap patterns q rho (2*R) Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k (2*R) 0
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      w.val.1).toFinset w.val.2 htrace j
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTraceAllGEligible -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The exact initial seen register is used at each G_i,
including terminal G, from the actual eligible G fibre. -/
theorem physical_oriented_trace_all_G_birth_eligible
    (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (j : Fin (remaining+1)) :
    let g := physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t j
    physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap
      g.1 (physicalOrientedTraceSeen SP smallMod BP bigMod
        J ell m cap patterns k remaining start y seen t j)
      g.2.2 := by
  induction remaining generalizing start y seen with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      change physicalGhostBatchEligible SP smallMod BP bigMod
        (J+ell) cap t.val.1 seen t.val.2.2
      exact (Finset.mem_filter.mp t.property).2.2
    | succ j => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    cases j using Fin.cases with
    | zero =>
      have hG := (Finset.mem_sigma.mp ab.property).1
      exact (Finset.mem_filter.mp hG).2.2
    | succ j =>
      exact ih (start+1) yNext seenNext tail j
end Green64FullPhysicalE

end

/-! ## MemorySourceRootToWitnessPath -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original root trace to chronological dependent G/E path.
    The nonempty E domain requires N=2R>0. -/
noncomputable def memory_source_root_to_actual_witness_path
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      k (2*R) := by
  let N := 2*R
  have hN : 0 < N := by dsimp [N]; omega
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1
  let seen0 := (physicalInitialBirths SP smallMod BP bigMod
    J ell cap w.val.1).toFinset
  let t := w.val.2
  let jG : ℕ → Fin (N+1) := fun i =>
    ⟨i % (N+1), Nat.mod_lt i (Nat.succ_pos N)⟩
  let jE : ℕ → Fin N := fun i => ⟨i % N, Nat.mod_lt i hN⟩
  let G : ℕ → PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap := fun i =>
    physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jG i)
  let E : ℕ → PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
      J ell m cap patterns := fun i =>
    physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jE i)
  let S : ℕ → Finset ℕ := fun i =>
    physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jG i)
  have hjG (i : ℕ) (hi : i ≤ N) :
      jG i = (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N+1)) := by
    apply Fin.ext
    change i % (N+1) = i
    exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hi)
  have hjE (i : ℕ) (hi : i < N) :
      jE i = (⟨i, hi⟩ : Fin N) := by
    apply Fin.ext
    change i % N = i
    exact Nat.mod_eq_of_lt hi
  have hG0 : (G 0).1 = w.val.1 := by
    dsimp only [G]
    rw [hjG 0 (Nat.zero_le N)]
    exact memory_source_root_first_G_state_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R w
  have hroot := memory_source_root_initial_bridge
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w
  refine {
    before := fun i => (G i).1
    afterG := fun i => (G i).2.1
    beforeE := fun i => (E i).1
    ghost := fun i => (G i).2.2
    edge := fun i => (E i).2
    seen := S
    initial_births_nodup := by
      simpa only [hG0] using hroot.1
    initial_vacuum := by
      simpa only [hG0] using hroot.2.1
    initial_seen := by
      change S 0 = (physicalInitialBirths SP smallMod BP bigMod
        J ell cap (G 0).1).toFinset
      rw [hG0]
      change physicalOrientedTraceSeen SP smallMod BP bigMod
        J ell m cap patterns k N 0 y seen0 t (jG 0) = seen0
      rw [hjG 0 (Nat.zero_le N)]
      exact hroot.2.2.1
    G_nonzero := by
      intro i hi
      have h := memory_source_root_all_G_nonzero
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R w
        (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (2*R+1))
      change physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N i Vbig (physicalSourceMuTilde BP bigMod q N Vbig)
        (G i).1 (G i).2.1 (G i).2.2 ≠ 0
      dsimp only [G]
      rw [hjG i hi]
      simpa only [physicalOrientedTraceGTerm, Nat.zero_add] using h
    G_birth_eligible := by
      intro i hi
      have h := physical_oriented_trace_all_G_birth_eligible
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N+1))
      change physicalGhostBatchEligible SP smallMod BP bigMod
        (J+ell) cap (G i).1 (S i) (G i).2.2
      dsimp only [G, S]
      rw [hjG i hi]
      exact h
    E_orbit_input := by
      intro i hi
      have h := physical_oriented_trace_all_E_inputs
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (E i).1 =
        physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (G i).2.1
      dsimp only [E, G]
      rw [hjE i hi, hjG i (Nat.le_of_lt hi)]
      exact h
    E_legal := by
      intro i hi
      change sourceOrientedPhysicalLegal SP smallMod BP bigMod
        J ell m cap patterns (E i).1 (physicalAlternatingSign i) k (E i).2
      dsimp only [E]
      rw [hjE i hi]
      simpa only [Fin.val_mk, Nat.zero_add] using
        (physical_oriented_trace_all_pair_eligible
          SP smallMod BP bigMod J ell m cap patterns
          k N 0 y seen0 t (⟨i, hi⟩ : Fin N)).2.1
    E_birth_eligible := by
      intro i hi
      have h := (physical_oriented_trace_all_pair_eligible
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)).2.2
      change orientedEFreshBatchEligible SP smallMod BP bigMod
        J ell m cap patterns
        (S i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap (G i).1 (G i).2.2).toFinset) (E i).2
      dsimp only [S, G, E]
      rw [hjE i hi, hjG i (Nat.le_of_lt hi)]
      exact h
    E_output := by
      intro i hi
      have h := physical_oriented_trace_all_E_outputs
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (G (i+1)).1 =
        sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns (E i).1 (physicalAlternatingSign i) k (E i).2
      dsimp only [G, E]
      rw [hjG (i+1) (Nat.succ_le_of_lt hi), hjE i hi]
      have hsucc :
          (⟨i+1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ : Fin (N+1)) =
          Fin.succ (⟨i, hi⟩ : Fin N) := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_mk]
      rw [hsucc]
      simpa only [Nat.zero_add] using h
    seen_update := by
      intro i hi
      have h := physical_oriented_trace_all_seen_updates
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change S (i+1) =
        ((S i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap (G i).1 (G i).2.2).toFinset) ∪
          (orientedEFreshBirths SP smallMod BP bigMod
            J ell m cap patterns (E i).2).toFinset)
      dsimp only [S, G, E]
      rw [hjG (i+1) (Nat.succ_le_of_lt hi),
        hjG i (Nat.le_of_lt hi), hjE i hi]
      exact h
  }
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootToWitnessPath -/

section

open Classical
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original root trace to chronological dependent G/E path.
    The nonempty E domain requires N=2R>0. -/
noncomputable def physical_oriented_root_to_actual_witness_path
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R)
    (w : PhysicalOrientedContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      k (2*R) := by
  let N := 2*R
  have hN : 0 < N := by dsimp [N]; omega
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1
  let seen0 := (physicalInitialBirths SP smallMod BP bigMod
    J ell cap w.val.1).toFinset
  let t := w.val.2
  let jG : ℕ → Fin (N+1) := fun i =>
    ⟨i % (N+1), Nat.mod_lt i (Nat.succ_pos N)⟩
  let jE : ℕ → Fin N := fun i => ⟨i % N, Nat.mod_lt i hN⟩
  let G : ℕ → PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap := fun i =>
    physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jG i)
  let E : ℕ → PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
      J ell m cap patterns := fun i =>
    physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jE i)
  let S : ℕ → Finset ℕ := fun i =>
    physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k N 0 y seen0 t (jG i)
  have hjG (i : ℕ) (hi : i ≤ N) :
      jG i = (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N+1)) := by
    apply Fin.ext
    change i % (N+1) = i
    exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hi)
  have hjE (i : ℕ) (hi : i < N) :
      jE i = (⟨i, hi⟩ : Fin N) := by
    apply Fin.ext
    change i % N = i
    exact Nat.mod_eq_of_lt hi
  have hG0 : (G 0).1 = w.val.1 := by
    dsimp only [G]
    rw [hjG 0 (Nat.zero_le N)]
    exact physical_oriented_contributing_first_G_state_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R w
  have hroot := physical_oriented_contributing_root_initial_bridge
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w
  refine {
    before := fun i => (G i).1
    afterG := fun i => (G i).2.1
    beforeE := fun i => (E i).1
    ghost := fun i => (G i).2.2
    edge := fun i => (E i).2
    seen := S
    initial_births_nodup := by
      simpa only [hG0] using hroot.1
    initial_vacuum := by
      simpa only [hG0] using hroot.2.1
    initial_seen := by
      change S 0 = (physicalInitialBirths SP smallMod BP bigMod
        J ell cap (G 0).1).toFinset
      rw [hG0]
      change physicalOrientedTraceSeen SP smallMod BP bigMod
        J ell m cap patterns k N 0 y seen0 t (jG 0) = seen0
      rw [hjG 0 (Nat.zero_le N)]
      exact hroot.2.2.1
    G_nonzero := by
      intro i hi
      have h := physical_oriented_contributing_all_G_nonzero
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R w
        (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (2*R+1))
      change physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N i Vbig (physicalSourceMuTilde BP bigMod q N Vbig)
        (G i).1 (G i).2.1 (G i).2.2 ≠ 0
      dsimp only [G]
      rw [hjG i hi]
      simpa only [physicalOrientedTraceGTerm, Nat.zero_add] using h
    G_birth_eligible := by
      intro i hi
      have h := physical_oriented_trace_all_G_birth_eligible
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N+1))
      change physicalGhostBatchEligible SP smallMod BP bigMod
        (J+ell) cap (G i).1 (S i) (G i).2.2
      dsimp only [G, S]
      rw [hjG i hi]
      exact h
    E_orbit_input := by
      intro i hi
      have h := physical_oriented_trace_all_E_inputs
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (E i).1 =
        physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (G i).2.1
      dsimp only [E, G]
      rw [hjE i hi, hjG i (Nat.le_of_lt hi)]
      exact h
    E_legal := by
      intro i hi
      change sourceOrientedPhysicalLegal SP smallMod BP bigMod
        J ell m cap patterns (E i).1 (physicalAlternatingSign i) k (E i).2
      dsimp only [E]
      rw [hjE i hi]
      simpa only [Fin.val_mk, Nat.zero_add] using
        (physical_oriented_trace_all_pair_eligible
          SP smallMod BP bigMod J ell m cap patterns
          k N 0 y seen0 t (⟨i, hi⟩ : Fin N)).2.1
    E_birth_eligible := by
      intro i hi
      have h := (physical_oriented_trace_all_pair_eligible
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)).2.2
      change orientedEFreshBatchEligible SP smallMod BP bigMod
        J ell m cap patterns
        (S i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap (G i).1 (G i).2.2).toFinset) (E i).2
      dsimp only [S, G, E]
      rw [hjE i hi, hjG i (Nat.le_of_lt hi)]
      exact h
    E_output := by
      intro i hi
      have h := physical_oriented_trace_all_E_outputs
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (G (i+1)).1 =
        sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns (E i).1 (physicalAlternatingSign i) k (E i).2
      dsimp only [G, E]
      rw [hjG (i+1) (Nat.succ_le_of_lt hi), hjE i hi]
      have hsucc :
          (⟨i+1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ : Fin (N+1)) =
          Fin.succ (⟨i, hi⟩ : Fin N) := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_mk]
      rw [hsucc]
      simpa only [Nat.zero_add] using h
    seen_update := by
      intro i hi
      have h := physical_oriented_trace_all_seen_updates
        SP smallMod BP bigMod J ell m cap patterns
        k N 0 y seen0 t (⟨i, hi⟩ : Fin N)
      change S (i+1) =
        ((S i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap (G i).1 (G i).2.2).toFinset) ∪
          (orientedEFreshBirths SP smallMod BP bigMod
            J ell m cap patterns (E i).2).toFinset)
      dsimp only [S, G, E]
      rw [hjG (i+1) (Nat.succ_le_of_lt hi),
        hjG i (Nat.le_of_lt hi), hjE i hi]
      exact h
  }
end Green64FullPhysicalE

end

