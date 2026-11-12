module

public import Green64.Library.Correlation.MemorySourceFiniteLifeReadout
public import Green64.Library.Correlation.Part008
public import Mathlib.Tactic.Ring
public import Green64.Library.Correlation.Part015
public import Green64.Library.Correlation.Part021
public import Mathlib.Data.List.Sigma
public import Green64.Library.Correlation.Part014
public import Green64.Library.Correlation.Part018
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part011
public import Green64.Library.Correlation.MemorySourceRootLifespanReadout
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part019

@[expose] public section

/-!
# Correlation / Part022

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemorySourceBirthClockReadout -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Chronological older births follow from the already proved lifespan
readout and the ACTUAL clock recurrence; no past-set hypothesis is added
to a source root. -/
theorem memory_life_fits_past_exact {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (n : ℕ)
    (life : P → Option (ℕ × ℕ)) (hl : PhysicalLifeFits c n life)
    (hzero : c.past 0 = ∅)
    (hfa : ∀ i, c.fresh i ⊆ c.active i)
    (hstep : ∀ i, c.past (i+1) = (c.past i ∪ c.fresh i) ∪ c.ghost i)
    (p : P) (i : ℕ) :
    p ∈ c.past i ↔ match life p with | none => False | some az => az.1 < i := by
  have hf := hl p
  cases he : life p with
  | none =>
    simp only [he] at hf ⊢
    induction i with
    | zero => simp [hzero]
    | succ i ih =>
      rw [hstep i]
      simp only [Finset.mem_union, ih, false_or]
      exact iff_false_intro (fun h => h.elim (fun h => (hf i).1 (hfa i h)) (hf i).2.2)
  | some az =>
    simp only [he] at hf ⊢
    induction i with
    | zero => simp [hzero]
    | succ i ih =>
      have hb : (p ∈ c.fresh i ∨ p ∈ c.ghost i) ↔ az.1 = i := by
        simpa only [Finset.mem_union] using (hf.2.2.2 i).2.2.2.1
      rw [hstep i]
      simp only [Finset.mem_union, or_assoc, ih, hb]
      omega

theorem memory_life_fits_current_fresh_exact {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (n : ℕ)
    (life : P → Option (ℕ × ℕ)) (hl : PhysicalLifeFits c n life)
    (hpast : ∀ p i, p ∈ c.past i ↔
      match life p with | none => False | some az => az.1 < i)
    (hfa : ∀ i, c.fresh i ⊆ c.active i)
    (halive : ∀ i, c.active i ⊆ c.past i ∪ c.fresh i)
    (p : P) (i : ℕ) :
    p ∈ c.fresh i ↔ match life p with
      | none => False | some az => az.1 = i ∧ p ∈ c.active i := by
  have hf := hl p
  cases he : life p with
  | none =>
    simp only [he] at hf ⊢
    exact iff_false_intro (fun h => (hf i).1 (hfa i h))
  | some az =>
    simp only [he] at hf ⊢
    constructor
    · intro h
      exact ⟨(hf.2.2.2 i).2.2.2.1.mp (Finset.mem_union_left _ h), hfa i h⟩
    · rintro ⟨ha, hact⟩
      rcases Finset.mem_union.mp (halive i hact) with hp | hp
      · have hh := (hpast p i).mp hp
        simp only [he] at hh
        omega
      · exact hp

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)

/-- The actual input numerical seen set at G_i, in every BIG group, has
exactly the canonical lifespan birthday test. Applies to the finite profile
derived from every source root; no auxiliary draws count as births. -/
theorem memory_actual_group_seen_life_exact
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) (life : BP g → Option (ℕ × ℕ))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1) life)
    (i : ℕ) (hi : i ≤ N) (p : BP g) :
    p ∈ actualNumericalSeenGroup BP bigMod (H.seen i) g ↔
      match life p with
      | none => False
      | some az => az.1 < i ∨ (az.1 = i ∧
        ∃ j : Fin (J+ell), ((H.before i).2 g).1 j = p) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H g
  have hzero : c.past 0 = ∅ :=
    (physical_source_clock_initial SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H hnum g).1
  have hrows := physical_source_clock_all_rows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H hnum g
  have hfa : ∀ i, c.fresh i ⊆ c.active i := fun i => (hrows i).1
  have hstep : ∀ i, c.past (i+1) = (c.past i ∪ c.fresh i) ∪ c.ghost i := by
    intro i
    rcases hrows i with ⟨_, _, _, _, _, _, _, _, _, hu⟩
    exact hu
  have hpast := memory_life_fits_past_exact c (N+1) life hl hzero hfa hstep
  have hlive : ∀ i, c.active i ⊆ c.past i ∪ c.fresh i := by
    intro t
    by_cases ht : t ≤ N
    · intro v hv
      have ha : ∃ j : Fin (J+ell), ((H.before t).2 g).1 j = v := by
        simpa only [c, physicalActualSourceSetClock, if_pos ht,
          Finset.mem_image, Finset.mem_univ, true_and] using hv
      obtain ⟨j, rfl⟩ := ha
      have hgood := physical_finite_actual_path_good_every_visit SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N H t ht
      have hseen := (hgood g).2.2.2.1 j
      have hgroup : ((H.before t).2 g).1 j ∈
          actualNumericalSeenGroup BP bigMod (H.seen t) g := by
        simpa [actualNumericalSeenGroup, physicalFockProjection] using hseen
      rw [physicalGroup_seen_eq_past_union_fresh SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N t H hnum ht g] at hgroup
      simpa only [c, physicalActualSourceSetClock, if_pos ht] using hgroup
    · simp [c, physicalActualSourceSetClock, ht]
  have hfresh := memory_life_fits_current_fresh_exact c (N+1) life hl hpast hfa hlive p i
  rw [physicalGroup_seen_eq_past_union_fresh SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N i H hnum hi g]
  have hp := hpast p i
  simp only [c, physicalActualSourceSetClock, if_pos hi] at hp hfresh
  simp only [Finset.mem_union, hp, hfresh]
  cases he : life p with
  | none => simp
  | some az =>
    simp only
    have hac : p ∈ (Finset.univ : Finset (Fin (J+ell))).image (((H.before i).2 g).1) ↔
        ∃ j : Fin (J+ell), ((H.before i).2 g).1 j = p := by
      simp [c, physicalActualSourceSetClock, hi]
    rw [hac]
end Green64FullPhysicalE

end

end

/-! ## MemoryClockResidueInduction -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Algebraic induction used with the actual physical clock below. Its local
laws are obligations discharged from original G/E operations, not assumptions
added to the Memory target. -/
theorem memory_clock_residue_induction {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (N : ℕ) (p : P) (modulus : ℕ)
    (h r s : ℕ → ZMod modulus) (a d : ℕ)
    (life : P → Option (ℕ × ℕ)) (hl : PhysicalLifeFits c (N+1) life)
    (he : life p = some (a,d))
    (hinitA : c.active 0 = c.fresh 0) (hinitP : c.pending 0 = ∅)
    (hG : ∀ i ≤ N, p ∈ (c.pending i \ c.ended i) ∪ c.ghost i →
      (p ∈ c.pending i ∧ p ∉ c.ended i → s i = r i) ∧
      (p ∈ c.ghost i → s i = 0))
    (hrows : ∀ i < N,
      c.active (i+1) = c.shared i ∪ c.promoted i ∪ c.fresh (i+1) ∧
      c.pending (i+1) = (((c.pending i \ c.ended i) ∪ c.ghost i) \ c.promoted i) ∪ c.stored i ∧
      c.shared i ⊆ c.active i ∧ c.stored i ⊆ c.active i ∧
      c.promoted i ⊆ (c.pending i \ c.ended i) ∪ c.ghost i)
    (hshared : ∀ i < N, p ∈ c.shared i → h (i+1) = h i)
    (hprom : ∀ i < N, p ∈ c.promoted i → s i + (h (i+1)-h i) = 0)
    (hstore : ∀ i < N, p ∈ c.stored i → r (i+1) = h (i+1)-h i)
    (hsurv : ∀ i < N,
      p ∈ ((c.pending i \ c.ended i) ∪ c.ghost i) \ c.promoted i →
      r (i+1) = s i + (h (i+1)-h i)) :
    ∀ i ≤ N, (p ∈ c.active i → h i = h a) ∧
      (p ∈ c.pending i → r i = h i-h a) ∧
      (p ∈ (c.pending i \ c.ended i) ∪ c.ghost i → s i = h i-h a) := by
  have hf := hl p
  simp only [he] at hf
  have hbirth (i : ℕ) (hp : p ∈ c.fresh i ∪ c.ghost i) : a = i :=
    (hf.2.2.2 i).2.2.2.1.mp hp
  have hafter (i : ℕ) (hi : i ≤ N)
      (hr : p ∈ c.pending i → r i = h i-h a)
      (hp : p ∈ (c.pending i \ c.ended i) ∪ c.ghost i) :
      s i = h i-h a := by
    rcases Finset.mem_union.mp hp with hpold | hpghost
    · have ho := Finset.mem_sdiff.mp hpold
      rw [(hG i hi (Finset.mem_union_left _ hpold)).1 ho, hr ho.1]
    · have ha := hbirth i (Finset.mem_union_right _ hpghost)
      rw [(hG i hi (Finset.mem_union_right _ hpghost)).2 hpghost, ha, sub_self]
  intro i
  induction i with
  | zero =>
    intro hi
    have hr : p ∈ c.pending 0 → r 0 = h 0-h a := by simp [hinitP]
    refine ⟨?_, hr, hafter 0 hi hr⟩
    intro hp
    have ha := hbirth 0 (Finset.mem_union_left _ (hinitA ▸ hp))
    rw [ha]
  | succ i ih =>
    intro hi
    have hiN : i < N := by omega
    obtain ⟨ha, hr, hs⟩ := ih (by omega)
    obtain ⟨hact,hpend,hsh,hst,hpr⟩ := hrows i hiN
    have hrnext : p ∈ c.pending (i+1) → r (i+1) = h (i+1)-h a := by
      rw [hpend]
      intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · rw [hsurv i hiN hp, hs (Finset.mem_sdiff.mp hp).1]
        ring
      · rw [hstore i hiN hp, ha (hst hp)]
    refine ⟨?_, hrnext, hafter (i+1) hi hrnext⟩
    rw [hact]
    intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hshared i hiN hp).trans (ha (hsh hp))
      · have hz := hprom i hiN hp
        rw [hs (hpr hp)] at hz
        have : h (i+1)-h a = 0 := by
          calc
            h (i+1)-h a = (h i-h a)+(h (i+1)-h i) := by ring
            _ = 0 := hz
        exact sub_eq_zero.mp this
    · have hb := hbirth (i+1) (Finset.mem_union_left _ hp)
      rw [hb]
end Green64FullPhysicalE

end

end

/-! ## MemoryActualClockResidueInduction -/

section

open Classical
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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)


/-- Actual root-path residue induction. The only profile premise is the
already checked SET-clock readout; every residue law is derived here from
the original physical G/E operations. -/
theorem memory_actual_clock_residue_induction
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) (life : BP g → Option (ℕ × ℕ))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1) life)
    (p : BP g) (a d : ℕ) (he : life p = some (a,d)) :
    ∀ i ≤ N,
      (p ∈ (physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig mu k N H g).active i →
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H i : ZMod (bigMod g p)) =
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H a : ZMod (bigMod g p))) ∧
      (p ∈ (physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig mu k N H g).pending i →
        physicalLiteralFockResidue BP bigMod cap SP smallMod (H.before i) ⟨g,p⟩ =
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H i : ZMod (bigMod g p)) -
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H a : ZMod (bigMod g p))) ∧
      (p ∈ ((physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig mu k N H g).pending i \
        (physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig mu k N H g).ended i) ∪
        (physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig mu k N H g).ghost i →
        physicalLiteralFockResidue BP bigMod cap SP smallMod (H.afterG i) ⟨g,p⟩ =
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H i : ZMod (bigMod g p)) -
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig mu k N H a : ZMod (bigMod g p))) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let h := fun i => (physicalActualOffset SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H i : ZMod (bigMod g p))
  let tag : PhysicalSourcePrime BP := ⟨g,p⟩
  have hB (i : ℕ) (hi : i ≤ N) :
      p ∈ c.pending i ↔ tag ∈ physicalActualLiteralPendingBefore SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_before_group_mem]
    simp [c, physicalActualSourceSetClock, hi, actualPhysicalPendingSet, tag]
  have hD (i : ℕ) (hi : i < N) :
      p ∈ c.ended i ↔ tag ∈ physicalActualLiteralEndedValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_ended_group_mem]
    simp [c, physicalActualSourceSetClock, hi, tag]
  have hGh (i : ℕ) (hi : i < N) :
      p ∈ c.ghost i ↔ tag ∈ physicalActualLiteralGhostBatch SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_ghost_group_mem]
    simp [c, physicalActualSourceSetClock, hi, physicalGhostGroupBornSet, tag]
  have hP (i : ℕ) (hi : i < N) :
      p ∈ c.promoted i ↔ tag ∈ physicalActualLiteralPromotionValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_promotion_group_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi]
    simp [c, physicalActualSourceSetClock, hi, tag]
  have hS (i : ℕ) (hi : i < N) :
      p ∈ c.stored i ↔ tag ∈ physicalActualLiteralStoreValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_store_group_mem]
    simp [c, physicalActualSourceSetClock, hi, tag]
  have hA (i : ℕ) (hi : i < N) :
      p ∈ (c.pending i \ c.ended i) ∪ c.ghost i ↔
      tag ∈ physicalActualLiteralPendingAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N H i := by
    rw [physical_actual_literal_G_global_support SP smallMod BP bigMod J ell m cap patterns q rho Vbig mu k N H i (le_of_lt hi)]
    simp only [Finset.mem_union, Finset.mem_sdiff, hB i (le_of_lt hi), hD i hi, hGh i hi]
  have hdelta (i : ℕ) : h (i+1)-h i =
      (physicalActualEdgeDelta SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H i : ZMod (bigMod g p)) := by
    dsimp [h]
    rw [physical_actual_offset_succ]
    push_cast
    abel
  have hin := physical_source_clock_initial SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H hnum g
  apply memory_clock_residue_induction c N p (bigMod g p) h
    (fun i => physicalLiteralFockResidue BP bigMod cap SP smallMod (H.before i) tag)
    (fun i => physicalLiteralFockResidue BP bigMod cap SP smallMod (H.afterG i) tag)
    a d life hl he hin.2.2.symm hin.2.1
  · intro i hi hp
    by_cases hiN : i < N
    · constructor
      · rintro ⟨hb,hd⟩
        exact physical_actual_literal_surviving_old_residue_unchanged
          SP smallMod BP bigMod J ell m cap patterns q rho Vbig mu k N H
          i hi tag ((hB i hi).mp hb) (fun hh => hd ((hD i hiN).mpr hh))
      · intro hg
        exact physical_actual_literal_ghost_birth_zero SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H i hi tag ((hGh i hiN).mp hg)
    · have hie : i = N := by omega
      subst i
      simp [c, physicalActualSourceSetClock] at hp
  · intro i hi
    obtain ⟨_,_,_,_,hsh,hst,hpr,ha,hp,_⟩ :=
      physical_source_clock_all_rows SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H hnum g i
    exact ⟨ha,hp,hsh, fun v hv => (Finset.mem_sdiff.mp (hst hv)).1,hpr⟩
  · intro i hi hp
    have hp' : p ∈ trueBigSharedValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) (sourceBigShared J ell m (patterns (H.edge i).1) g)
        ((H.edge i).2.2.1.sigmaBig g) := by
      simpa [c,physicalActualSourceSetClock,hi] using hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp'
    change ((H.beforeE i).2 g).1 (((H.edge i).2.2.1.sigmaBig g) j) = p at hjp
    have hz := oriented_big_shared_displacement_zero SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
      (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1 (physicalAlternatingSign i) k g j hj
    change (physicalActualEdgeDelta SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H i : ZMod (bigMod g (((H.beforeE i).2 g).1 (((H.edge i).2.2.1.sigmaBig g) j)))) = 0 at hz
    have hz' : (physicalActualEdgeDelta SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H i : ZMod (bigMod g p)) = 0 := by
      exact hjp ▸ hz
    exact sub_eq_zero.mp ((hdelta i).trans hz')
  · intro i hi hp
    rw [hdelta]
    exact physical_actual_literal_promotion_zero SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i hi tag ((hP i hi).mp hp)
  · intro i hi hp
    rw [hdelta]
    exact physical_actual_literal_store_reset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i hi tag ((hS i hi).mp hp)
  · intro i hi hp
    rw [hdelta]
    exact physical_actual_literal_surviving_fock_translation SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i hi tag
      ((hA i hi).mp (Finset.mem_sdiff.mp hp).1)
      (fun hh => (Finset.mem_sdiff.mp hp).2 ((hP i hi).mpr hh))
end Green64FullPhysicalE

end

end

/-! ## MemoryActualScheduleSupport -/

section

open Classical
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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)



/-- Death endpoints satisfy the original congruence, including the
actual terminal vacuum. No congruence field is assumed. -/
theorem memory_actual_finite_schedule_support
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (life : BP g → MemoryLifespanChoice (N+1))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life p))) (p : BP g) :
    MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H t : ZMod (bigMod g p)))
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g p) (life p) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let A := memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g p
  have hA (t : ℕ) : t ∈ A ↔ t ≤ N ∧ p ∈ c.active t := by
    by_cases ht : t ≤ N
    · simp [A, memorySourceWitnessActiveVisits, Nat.lt_succ_iff, c,
        physicalActualSourceSetClock, ht, Finset.mem_image, eq_comm]
    · simp [A, memorySourceWitnessActiveVisits, Nat.lt_succ_iff, ht]
  have hf := hl p
  cases he : life p with
  | none =>
    simp only [he, memoryFiniteLifeErase, Option.map_none] at hf
    change A = ∅
    ext t
    constructor
    · intro ht
      exact False.elim ((hf t).1 ((hA t).mp ht).2)
    · simp
  | some az =>
    have her : memoryFiniteLifeErase (life p) = some (az.1.val, az.2.val) := by
      simp [memoryFiniteLifeErase, he]
    simp only [her] at hf
    have hres := memory_actual_clock_residue_induction SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H hnum g
      (fun p => memoryFiniteLifeErase (life p)) hl p az.1.val az.2.val her
    have hdN : az.2.val ≤ N := Nat.le_of_lt_succ az.2.isLt
    have hdeath : (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H az.2.val : ZMod (bigMod g p)) =
        (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H az.1.val : ZMod (bigMod g p)) := by
      have hevent := (hf.2.2.2 az.2.val).2.2.2.2.mpr rfl
      rcases Finset.mem_union.mp hevent with hend | hact
      · have hrows := physical_source_clock_all_rows SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H hnum g az.2.val
        have hpend := hrows.2.2.2.1 hend
        have hpendtag : (⟨g,p⟩ : PhysicalSourcePrime BP) ∈
            physicalActualLiteralPendingBefore SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig mu k N H az.2.val := by
          rw [physical_actual_literal_before_group_mem]
          simpa [c, physicalActualSourceSetClock, hdN, actualPhysicalPendingSet] using hpend
        have hz : physicalLiteralFockResidue BP bigMod cap SP smallMod
            (H.before az.2.val) (⟨g,p⟩ : PhysicalSourcePrime BP) = 0 := by
          by_cases hlt : az.2.val < N
          · apply physical_actual_literal_ended_zero SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig mu k N H az.2.val hdN
            apply (physical_actual_literal_ended_group_mem SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig mu k N H az.2.val g p).mpr
            simpa [c, physicalActualSourceSetClock, hlt] using hend
          · have heN : az.2.val = N := by omega
            exact physical_actual_terminal_literal_fock_zero SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig mu k N H hVac ⟨g,p⟩
              (by simpa only [heN] using hpendtag) |>
                (fun hh => by simpa only [heN] using hh)
        have hr := (hres az.2.val hdN).2.1 hpend
        exact sub_eq_zero.mp (hr.symm.trans hz)
      · exact (hres az.2.val hdN).1 (Finset.mem_sdiff.mp hact).1
    refine ⟨hf.1, ?_, hdeath, ?_⟩
    · intro t ht
      obtain ⟨htN,hact⟩ := (hA t).mp ht
      exact ⟨(hf.2.2.2 t).1 hact |>.1, (hf.2.2.2 t).1 hact |>.2,
        (hres t htN).1 hact⟩
    · intro heq
      exact (hA az.1.val).mpr ⟨Nat.le_of_lt_succ az.1.isLt, hf.2.2.1 heq⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryCanonicalAtomListReadout -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Ordered representatives with unique prime labels and the derived atom
residues are permutations of the exact original canonical list. -/
theorem memory_canonical_atom_list_readout {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (A : P → Finset ℕ) {n : ℕ} (life : P → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (before : Bool) (i : ℕ)
    (xs : List (Green64Fock.Atom P modulus))
    (hn : (xs.map (fun a => a.1)).Nodup)
    (hs : ∀ p, p ∈ xs.map (fun a => a.1) ↔
      if before then memoryScheduleBefore (A p) (life p) i
      else memoryScheduleAfter (A p) (life p) i)
    (hr : ∀ a ∈ xs, a.2 = memoryScheduleResidue (modulus a.1)
      (fun t => (offset t : ZMod (modulus a.1))) (life a.1) i) :
    xs.Perm (memoryCanonicalPendingList modulus A life offset before i) := by
  let atom := fun p : P => (⟨p, memoryScheduleResidue (modulus p)
    (fun t => (offset t : ZMod (modulus p))) (life p) i⟩ :
      Green64Fock.Atom P modulus)
  have hi : Function.Injective atom := by
    intro p q he
    exact congrArg Sigma.fst he
  apply List.mem_ext (List.Nodup.of_map _ hn)
    ((Finset.nodup_toList _).map hi)
  intro a
  constructor
  · intro ha
    have hp := (hs a.1).mp (List.mem_map.mpr ⟨a,ha,rfl⟩)
    apply List.mem_map.mpr
    refine ⟨a.1, ?_, ?_⟩
    · simpa only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    · exact Sigma.ext rfl (heq_of_eq (hr a ha).symm)
  · intro ha
    obtain ⟨p,hp,hpa⟩ := List.mem_map.mp ha
    have hp' : if before then memoryScheduleBefore (A p) (life p) i
        else memoryScheduleAfter (A p) (life p) i := by
      simpa only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    obtain ⟨b,hb,hbp⟩ := List.mem_map.mp ((hs p).mpr hp')
    have he : b = atom p := by
      subst p
      exact Sigma.ext rfl (heq_of_eq (hr b hb))
    have he' : atom p = a := hpa
    exact (he.trans he') ▸ hb
end Green64FullPhysicalE

end

end

/-! ## MemoryActualCanonicalPendingReadout -/

section

open Classical
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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)



/-- For the SAME finite lifespan profile, full ordered physical Fock
representatives (before G, after G, before E) have the canonical atoms. -/
theorem memory_actual_canonical_pending_readout
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (life : BP g → MemoryLifespanChoice (N+1))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life p))) (i : ℕ) (hi : i ≤ N) :
    let A := memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig mu k N H g
    let offset := physicalActualOffset SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig mu k N H
    (Green64Fock.fockToList (((H.before i).2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) A life offset true i) ∧
    (Green64Fock.fockToList (((H.afterG i).2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) A life offset false i) ∧
    (i < N → (Green64Fock.fockToList (((H.beforeE i).2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) A life offset false i)) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let A := memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let offset := physicalActualOffset SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H
  have hA (p : BP g) : i ∈ A p ↔ p ∈ c.active i := by
    simp [A, memorySourceWitnessActiveVisits, hi, c,physicalActualSourceSetClock,
      Finset.mem_image, eq_comm]
  have hB (p : BP g) : p ∈ (Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => a.1) ↔ p ∈ c.pending i := by
    simp [c, physicalActualSourceSetClock, hi, actualPhysicalPendingSet]
  have hb : (Green64Fock.fockToList (((H.before i).2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) A life offset true i) := by
    apply memory_canonical_atom_list_readout
    · exact physical_actual_literal_before_pending_nodup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N H i hi g
    · intro p
      rw [hB]
      have hf := hl p
      cases he : life p with
      | none =>
        simp only [he,memoryFiniteLifeErase,Option.map_none] at hf
        simp only [memoryScheduleBefore,he]
        exact iff_false_intro (hf i).2.1
      | some az =>
        have her : memoryFiniteLifeErase (life p) = some (az.1.val,az.2.val) := by
          simp [memoryFiniteLifeErase,he]
        simp only [her] at hf
        simpa [memoryScheduleBefore,he,hA p] using (hf.2.2.2 i).2.1
    · intro a ha
      have hp : a.1 ∈ c.pending i :=
        (hB a.1).mp (List.mem_map.mpr ⟨a,ha,rfl⟩)
      have hf := hl a.1
      cases he : life a.1 with
      | none =>
        simp only [he,memoryFiniteLifeErase,Option.map_none] at hf
        exact False.elim ((hf i).2.1 hp)
      | some az =>
        have her : memoryFiniteLifeErase (life a.1) = some (az.1.val,az.2.val) := by
          simp [memoryFiniteLifeErase,he]
        have hh := (memory_actual_clock_residue_induction SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H hnum g
          (fun p => memoryFiniteLifeErase (life p)) hl a.1 az.1.val az.2.val her i hi).2.1 hp
        have hr := physical_literal_fock_residue_of_atom BP bigMod cap SP smallMod
          (H.before i) ⟨g,a.1⟩
          (physical_actual_literal_before_pending_nodup SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig mu k N H i hi g) a.2
          (by simpa [Green64Fock.fockMultiset,Green64Fock.fockToList] using ha)
        rw [hr] at hh
        simpa [memoryScheduleResidue,he,offset,physicalSourcePrimeValue] using hh
  have hg : (Green64Fock.fockToList (((H.afterG i).2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) A life offset false i) := by
    by_cases hiN : i < N
    · have hG (p : BP g) : p ∈ (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
          (fun a => a.1) ↔ p ∈ (c.pending i \ c.ended i) ∪ c.ghost i := by
        rw [← physical_actual_literal_afterG_group_mem SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H i g p]
        rw [physical_actual_literal_G_global_support SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H i hi]
        rw [physical_actual_literal_before_group_mem,
          physical_actual_literal_ended_group_mem,physical_actual_literal_ghost_group_mem]
        simp [c,physicalActualSourceSetClock,hi,hiN,actualPhysicalPendingSet,
          physicalGhostGroupBornSet]
      apply memory_canonical_atom_list_readout
      · exact physical_actual_literal_afterG_pending_nodup SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H i hi g
      · intro p
        rw [hG]
        have hf := hl p
        cases he : life p with
        | none =>
          simp only [he,memoryFiniteLifeErase,Option.map_none] at hf
          simp only [memoryScheduleAfter,he]
          apply iff_false_intro
          intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · exact (hf i).2.1 (Finset.mem_sdiff.mp hp).1
          · exact (hf i).2.2 hp
        | some az =>
          have her : memoryFiniteLifeErase (life p) = some (az.1.val,az.2.val) := by
            simp [memoryFiniteLifeErase,he]
          simp only [her] at hf
          simpa [memoryScheduleAfter,he,hA p] using (hf.2.2.2 i).2.2.1
      · intro a ha
        have hp := (hG a.1).mp (List.mem_map.mpr ⟨a,ha,rfl⟩)
        have hf := hl a.1
        cases he : life a.1 with
        | none =>
          simp only [he,memoryFiniteLifeErase,Option.map_none] at hf
          rcases Finset.mem_union.mp hp with hp | hp
          · exact False.elim ((hf i).2.1 (Finset.mem_sdiff.mp hp).1)
          · exact False.elim ((hf i).2.2 hp)
        | some az =>
          have her : memoryFiniteLifeErase (life a.1) = some (az.1.val,az.2.val) := by
            simp [memoryFiniteLifeErase,he]
          have hh := (memory_actual_clock_residue_induction SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig mu k N H hnum g
            (fun p => memoryFiniteLifeErase (life p)) hl a.1 az.1.val az.2.val her i hi).2.2 hp
          have hr := physical_literal_fock_residue_of_atom BP bigMod cap SP smallMod
            (H.afterG i) ⟨g,a.1⟩
            (physical_actual_literal_afterG_pending_nodup SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig mu k N H i hi g) a.2
            (by simpa [Green64Fock.fockMultiset,Green64Fock.fockToList] using ha)
          rw [hr] at hh
          simpa [memoryScheduleResidue,he,offset,physicalSourcePrimeValue] using hh
    · have hiN : i = N := by omega
      subst i
      have hz : ∀ g : BG, Green64Fock.fockMultiset (((H.afterG N).2 g).2) = 0 := by
        by_contra hh
        simp [physicalVacuum,physicalFockProjection,hh] at hVac
      have hx : Green64Fock.fockToList (((H.afterG N).2 g).2) = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        have hh := congrArg Multiset.card (hz g)
        simpa [Green64Fock.fockMultiset,Green64Fock.fockToList] using hh
      rw [hx,(memory_canonical_pending_vacua (bigMod g) A life offset).2]
  refine ⟨hb,hg,?_⟩
  intro hiN
  have heq := congrArg (fun x : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
    (x.2 g).2) (H.E_orbit_input i hiN)
  have hp : (Green64Fock.fockToList (((H.beforeE i).2 g).2)).Perm
      (Green64Fock.fockToList (((H.afterG i).2 g).2)) := by
    exact Multiset.coe_eq_coe.mp heq
  exact hp.trans hg
end Green64FullPhysicalE

end

end

/-! ## MemoryActualGlobalBirthRegisters -/

section

open Classical
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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)



/-- No numerical seen register contains a prime outside the actual source
BIG carrier. This derives the needed global support from initial/update. -/
theorem memory_actual_seen_source_image (i : ℕ) (hi : i ≤ N) (n : ℕ)
    (hn : n ∈ H.seen i) : ∃ g : BG, ∃ p : BP g, bigMod g p = n := by
  induction i with
  | zero =>
    rw [H.initial_seen] at hn
    have hm := List.mem_toFinset.mp hn
    unfold physicalInitialBirths at hm
    obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hm
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hg
    exact ⟨g,((H.before 0).2 g).1 j,hj⟩
  | succ i ih =>
    have hiN : i < N := by omega
    rw [H.seen_update i hiN] at hn
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_union.mp hn with hn | hn
      · exact ih (le_of_lt hiN) hn
      · have hm := List.mem_toFinset.mp hn
        unfold physicalGhostFreshBirths at hm
        obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hm
        obtain ⟨a,_,ha⟩ := List.mem_map.mp hg
        exact ⟨g,a.1,ha⟩
    · have hm := List.mem_toFinset.mp hn
      unfold orientedEFreshBirths at hm
      obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hm
      obtain ⟨j,_,hj⟩ := List.mem_map.mp hg
      exact ⟨g,((H.edge i).2.2.1.bigChoice g).1
        ((H.edge i).2.2.1.tauBig g j),hj⟩

/-- The full GLOBAL numerical before-G register is exact, not just its
one-group tests. Auxiliary draws never appear as births. -/
theorem memory_actual_global_seenG_exact
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (hl : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life g p))) (i : ℕ) (hi : i ≤ N) :
    H.seen i = memorySeenBeforeGValues BP bigMod
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) life i := by
  have hm (g : BG) (p : BP g) : bigMod g p ∈ H.seen i ↔
      match life g p with
      | none => False
      | some az => az.1.val < i ∨ (az.1.val = i ∧
        i ∈ memorySourceWitnessActiveVisits SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H g p) := by
    have hh := memory_actual_group_seen_life_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H hnum g
      (fun p => memoryFiniteLifeErase (life g p)) (hl g) i hi p
    cases he : life g p <;>
      simpa [actualNumericalSeenGroup,memoryFiniteLifeErase,he,
        memorySourceWitnessActiveVisits,hi] using hh
  ext n
  constructor
  · intro hn
    obtain ⟨g,p,he⟩ := memory_actual_seen_source_image SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i hi n hn
    apply Finset.mem_image.mpr
    refine ⟨⟨g,p⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,he⟩
    have hh := (hm g p).mp (he ▸ hn)
    cases hL : life g p <;> simpa [hL] using hh
  · intro hn
    obtain ⟨⟨g,p⟩,hp,he⟩ := Finset.mem_image.mp hn
    have hh := (Finset.mem_filter.mp hp).2
    have hm' : bigMod g p ∈ H.seen i := (hm g p).mpr (by cases hL : life g p <;> simpa [hL] using hh)
    exact he ▸ hm'

/-- After G_i the global register consists of precisely all births before
i+1, including the newly born inactive ghosts and active births at i. -/
theorem memory_actual_global_seenE_exact
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (hl : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life g p))) (i : ℕ) (hi : i < N) :
    H.seen i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
      (J+ell) cap (H.before i) (H.ghost i)).toFinset =
    memoryBornBeforeValues BP bigMod life (i+1) := by
  let S := H.seen i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
    (J+ell) cap (H.before i) (H.ghost i)).toFinset
  have hs (n : ℕ) (hn : n ∈ S) : ∃ g : BG, ∃ p : BP g, bigMod g p = n := by
    rcases Finset.mem_union.mp hn with hn | hn
    · exact memory_actual_seen_source_image SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N H i (le_of_lt hi) n hn
    · have hm := List.mem_toFinset.mp hn
      unfold physicalGhostFreshBirths at hm
      obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hm
      obtain ⟨a,_,ha⟩ := List.mem_map.mp hg
      exact ⟨g,a.1,ha⟩
  have hm (g : BG) (p : BP g) : bigMod g p ∈ S ↔
      match life g p with | none => False | some az => az.1.val < i+1 := by
    let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig mu k N H g
    have hin := physical_source_clock_initial SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H hnum g
    have hrows := physical_source_clock_all_rows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H hnum g
    have hpast := memory_life_fits_past_exact c (N+1)
      (fun p => memoryFiniteLifeErase (life g p)) (hl g) hin.1
      (fun t => (hrows t).1)
      (fun t => (hrows t).2.2.2.2.2.2.2.2.2) p (i+1)
    have hset : actualNumericalSeenGroup BP bigMod S g = c.past (i+1) := by
      dsimp [S]
      rw [actualNumericalSeenGroup_union,actual_G_numeric_birth_group_fibre
        SP smallMod BP bigMod J ell cap (H.before i) (H.ghost i) hnum g]
      rw [physicalGroup_seen_eq_past_union_fresh SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N i H hnum (le_of_lt hi) g]
      have hh := physicalGroupPastVisit_succ SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N i H hnum hi g
      simpa [c,physicalActualSourceSetClock, Nat.succ_le_of_lt hi] using hh.symm
    have hh : bigMod g p ∈ S ↔ p ∈ c.past (i+1) := by
      have := congrArg (fun s : Finset (BP g) => p ∈ s) hset
      simpa [actualNumericalSeenGroup] using this
    rw [hh,hpast]
    cases he : life g p <;> simp [memoryFiniteLifeErase,he]
  ext n
  constructor
  · intro hn
    obtain ⟨g,p,he⟩ := hs n hn
    apply Finset.mem_image.mpr
    refine ⟨⟨g,p⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,he⟩
    have hh := (hm g p).mp (he ▸ hn)
    cases hL : life g p <;> simpa [hL] using hh
  · intro hn
    obtain ⟨⟨g,p⟩,hp,he⟩ := Finset.mem_image.mp hn
    have hh := (Finset.mem_filter.mp hp).2
    have hm' : bigMod g p ∈ S := (hm g p).mpr (by cases hL : life g p <;> simpa [hL] using hh)
    exact he ▸ hm'
end Green64FullPhysicalE

end

end

/-! ## MemoryActualPrimeZeroHit -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Convert the ORIGINAL zeroOld index test to an actual zero atom. -/
theorem memory_original_old_zero_atom_iff {P : Type} [DecidableEq P]
    (modulus : P → ℕ) (xs : List (Green64Fock.Atom P modulus)) (p : P) :
    (∃ j : Fin xs.length, j ∈ Green64MemoryGhostOp.zeroOld xs (fun z => z.2 = 0) ∧
      (xs.get j).1 = p) ↔ (⟨p,0⟩ : Green64Fock.Atom P modulus) ∈ xs := by
  constructor
  · rintro ⟨j,hz,hp⟩
    have hz' : (xs.get j).2 = 0 := by simpa [Green64MemoryGhostOp.zeroOld] using hz
    have he : xs.get j = (⟨p,0⟩ : Green64Fock.Atom P modulus) := by
      apply Sigma.ext hp
      cases hp
      exact heq_of_eq hz'
    exact he ▸ List.get_mem xs j
  · intro hm
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
    refine ⟨j,?_,congrArg Sigma.fst hj⟩
    simp only [Green64MemoryGhostOp.zeroOld,Finset.mem_filter,Finset.mem_univ,true_and]
    change (xs.get j).2 = 0
    rw [hj]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)

/-- The coefficient-critical internal zero-hit test equals the actual frozen
offset collision; no free hit predicate is introduced. -/
theorem memory_actual_internal_prime_zero_hit_iff
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (life : BP g → MemoryLifespanChoice (N+1))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life p)))
    (p : BP g) (az : Fin (N+1) × Fin (N+1)) (he : life p = some az)
    (i : ℕ) (hai : az.1.val < i) (hiz : i < az.2.val)
    (hin : i ∉ memorySourceWitnessActiveVisits SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g p) :
    physicalActualSourceZeroHit SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H g p i ↔
    (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H i : ZMod (bigMod g p)) =
    (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H az.1.val : ZMod (bigMod g p)) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let A := memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  let offset := physicalActualOffset SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H
  have hi : i ≤ N := by have := az.2.isLt; omega
  have hactive : p ∉ c.active i := by
    simpa [c,A,memorySourceWitnessActiveVisits,physicalActualSourceSetClock,hi,
      Finset.mem_image,eq_comm] using hin
  have hf := hl p
  simp only [he,memoryFiniteLifeErase,Option.map_some,Prod.mk.eta] at hf
  have hghost : p ∉ c.ghost i := by
    intro hg
    have hb := (hf.2.2.2 i).2.2.2.1.mp (Finset.mem_union.mpr (Or.inr hg))
    omega
  have hperm := (memory_actual_canonical_pending_readout SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H hnum hVac g life hl i hi).1
  have hmem : (⟨p,0⟩ : Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockToList (((H.before i).2 g).2) ↔
      (offset i : ZMod (bigMod g p)) = (offset az.1.val : ZMod (bigMod g p)) := by
    rw [hperm.mem_iff]
    simp only [memoryCanonicalPendingList,List.mem_map,Finset.mem_toList,
      Finset.mem_filter,Finset.mem_univ,true_and,Bool.true_eq,if_true]
    constructor
    · rintro ⟨p',hp',he'⟩
      have hpp : p'=p := congrArg Sigma.fst he'
      subst p'
      have hr := eq_of_heq (Sigma.mk.inj_iff.mp he').2
      simpa only [he,memoryScheduleResidue,sub_eq_zero] using hr
    · intro hh
      refine ⟨p,?_,?_⟩
      · simp only [he,memoryScheduleBefore]
        exact ⟨hai,le_of_lt hiz,hin⟩
      · have hz : memoryScheduleResidue (bigMod g p)
            (fun t => (offset t : ZMod (bigMod g p))) (life p) i = 0 := by
          simpa only [he,memoryScheduleResidue,sub_eq_zero] using hh
        exact congrArg (fun r => (⟨p,r⟩ : Green64Fock.Atom (BP g) (bigMod g))) hz
  dsimp only [c] at hactive hghost
  unfold physicalActualSourceZeroHit
  dsimp only
  rw [memory_original_old_zero_atom_iff (bigMod g)]
  simpa only [hi,hactive,hghost,false_or,true_and] using hmem
end Green64FullPhysicalE

end

end

/-! ## MemoryActualSourcePrimeFrozenScalar -/

section

open Classical
open scoped BigOperators
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 800000
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)

/-- The already checked TRUE physical prime scalar now equals the literal
frozen prime term, including the absent baseline. Only source path/readout
hypotheses occur; every hit is the original actual source test. -/
theorem memory_actual_source_prime_scalar_frozen_exact
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (life : BP g → MemoryLifespanChoice (N+1))
    (hl : PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life p)))
    (p : BP g) (hr : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    (physicalSourceBaseline BP bigMod q N g p : ℂ) *
      physicalActualSourcePrimeScalar SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g p (memoryFiniteLifeErase (life p)) =
    (1/(Vbig g : ℂ))^(memoryFrozenPrimeRuns
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g p) N) *
    (memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q N)
      (fun t => (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H t : ZMod (bigMod g p)))
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g p) (N+1) (life p) : ℂ) := by
  let A := memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g p
  let offset := physicalActualOffset SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H
  let c := physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig mu k N H g
  have hs := memory_actual_finite_schedule_support SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H hnum hVac g life hl p
  have hA : ∀ i, p ∈ c.active i ↔ i ∈ A := by
    intro i
    by_cases hi : i ≤ N <;>
      simp [c,A,memorySourceWitnessActiveVisits,physicalActualSourceSetClock,
        hi,Nat.lt_succ_iff,Finset.mem_image,eq_comm]
  cases he : life p with
  | none =>
    have hem : A = ∅ := by simpa only [he,MemoryFrozenScheduleSupport] using hs
    dsimp only [A] at hem
    simp [he,memoryFiniteLifeErase,physicalActualSourcePrimeScalar,hem,
      memoryFrozenPrimeRuns,memoryFrozenPrimeTerm,memoryAbsentTerm,physicalSourceBaseline]
  | some az =>
    have her : memoryFiniteLifeErase (life p) = some (az.1.val,az.2.val) := by
      simp [he,memoryFiniteLifeErase]
    have hscalar := physical_actual_one_prime_scalar_no_hit_hypotheses
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig mu k N H hnum hVac
      g (fun p => memoryFiniteLifeErase (life p)) hl p az.1.val az.2.val her hr hV hb
    rw [he] at hscalar her
    rw [hscalar]
    unfold physicalActualTargetPrimeScalar
    rw [her]
    dsimp only
    change (physicalSourceBaseline BP bigMod q N g p : ℂ) *
      ((1/(Vbig g : ℂ))^((Finset.range (N+1)).filter
        (fun i => p ∈ c.active i ∧ (i=0 ∨ p ∉ c.active (i-1)))).card /
        ((bigMod g p : ℂ)*(physicalSourceBaseline BP bigMod q N g p : ℂ)) *
        (if p ∈ c.active az.1.val then 1 else -(sourceVisitEta q N az.1.val : ℂ)) *
        (if p ∈ c.active az.2.val then 1 else -(sourceVisitEta q N az.2.val : ℂ)) *
        (∏ i ∈ Finset.range (N+1),
          if (az.1.val < i ∧ i < az.2.val ∧ p ∉ c.active i) ∧
            physicalActualSourceZeroHit SP smallMod BP bigMod J ell m cap patterns
              q rho Vbig mu k N H g p i then (sourceVisitQ q N i : ℂ) else 1)) = _
    simp_rw [hA]
    have hn := memory_frozen_prime_supported_normal_form (bigMod g p)
      (sourceVisitEta q N) (fun t => (offset t : ZMod (bigMod g p))) A (N+1) az
      (by simpa only [he] using hs)
    change _ = (1/(Vbig g : ℂ))^(memoryFrozenPrimeRuns A N) *
      (memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q N)
        (fun t => (offset t : ZMod (bigMod g p))) A (N+1) (some az) : ℂ)
    rw [hn]
    have hi :
      (∏ i ∈ Finset.range (N+1),
        if (az.1.val < i ∧ i < az.2.val ∧ i ∉ A) ∧
          physicalActualSourceZeroHit SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig mu k N H g p i then (sourceVisitQ q N i : ℂ) else 1) =
      ((∏ i ∈ Finset.range (N+1),
        if az.1.val < i ∧ i < az.2.val ∧ i ∉ A then
          1-sourceVisitEta q N i *
            (if (offset i : ZMod (bigMod g p)) = (offset az.1.val : ZMod (bigMod g p))
              then (1 : ℝ) else 0) else 1 : ℝ) : ℂ) := by
      push_cast
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hc : az.1.val < i ∧ i < az.2.val ∧ i ∉ A
      · have hz := memory_actual_internal_prime_zero_hit_iff SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig mu k N H hnum hVac g life hl p az he
          i hc.1 hc.2.1 hc.2.2
        rw [hz]
        by_cases hh : (offset i : ZMod (bigMod g p)) = (offset az.1.val : ZMod (bigMod g p))
        <;> simp [hc,hh,offset,sourceVisitEta]
      · simp [hc]
    rw [hi]
    push_cast
    have hca : ((if az.1.val ∈ A then 1 else -sourceVisitEta q N az.1.val : ℝ) : ℂ) =
        (if az.1.val ∈ A then 1 else -(sourceVisitEta q N az.1.val : ℂ)) := by
      split_ifs <;> simp
    have hcz : ((if az.2.val ∈ A then 1 else -sourceVisitEta q N az.2.val : ℝ) : ℂ) =
        (if az.2.val ∈ A then 1 else -(sourceVisitEta q N az.2.val : ℂ)) := by
      split_ifs <;> simp
    rw [hca,hcz]
    unfold memoryFrozenPrimeRuns
    have hp : (bigMod g p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (bigMod g p)
    have hb' : (physicalSourceBaseline BP bigMod q N g p : ℂ) ≠ 0 := by exact_mod_cast hb
    field_simp [hp,hb'] <;> ring
end Green64FullPhysicalE

end

end

/-! ## MemorySourceCanonicalRootReadoutProof -/

section

open Classical
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


/-- The original pinned forward readout target, now proved for EVERY
genuine nonzero full indexed source root. No residue, support,
canonical-permutation or birth-register hypotheses are inserted. -/
theorem memory_source_canonical_root_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemorySourceCanonicalRootReadoutTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig k Vsmall Knu zeta theta R := by
  intro hd w
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  obtain ⟨life,hl⟩ := memory_source_root_finite_life_readout SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let offset := physicalActualOffset SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H
  refine ⟨{
    offset := offset
    life := life
    offset_zero := ?_
    offset_step := ?_
    support := ?_
    before := ?_
    afterG := ?_
    beforeE := ?_
    seenG := ?_
    seenE := ?_ }⟩
  · simp [offset,physicalActualOffset]
  · intro i hi
    dsimp [offset]
    rw [physical_actual_offset_succ]
    change _ + physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H i - _ = _
    simp only [add_sub_cancel_left,physicalActualEdgeDelta]
    rfl
  · intro g p
    exact memory_actual_finite_schedule_support SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.big_injective hVac g (life g) (hl g) p
  · intro i hi g
    exact (memory_actual_canonical_pending_readout SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.big_injective hVac g (life g) (hl g) i hi).1
  · intro i hi g
    exact (memory_actual_canonical_pending_readout SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.big_injective hVac g (life g) (hl g) i hi).2.1
  · intro i hi g
    exact (memory_actual_canonical_pending_readout SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.big_injective hVac g (life g) (hl g) i (le_of_lt hi)).2.2 hi
  · intro i hi
    exact memory_actual_global_seenG_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H hd.big_injective life hl i hi
  · intro i hi
    exact memory_actual_global_seenE_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H hd.big_injective life hl i hi

/-- Trusted expected type independently elaborated against the unchanged
target declaration. This confirms the result did not replace its fields. -/
theorem memory_source_canonical_root_readout_expected
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    Nonempty (MemorySourceCanonicalRootReadout SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R)
      (memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
        patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w)) :=
  memory_source_canonical_root_readout SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R hd w
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingTraceRecursion -/

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

/-- A true source G/E branch fits the frozen data, including its full original
E frame, actual post-E Fock state and the ACTUAL chronological seen register.
This is a filter on the existing legal indexed branch, not a new carrier. -/
def memorySourceFittingHead {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (start : ℕ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign start) k y seen) : Prop :=
  ∃ hi : start < N,
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.val.1.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap false ⟨start,Nat.lt_succ_of_lt hi⟩) ∧
    memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns
      ab.val.2.1 ab.val.2.2 = ω.2.2 ⟨start,hi⟩ ∧
    physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign start) k ab.val =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true ⟨start+1,Nat.succ_lt_succ hi⟩) ∧
    physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
      seen ab.val = memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (start+1)
/-- Exact dependent recursive splitting of fitting source traces.
The tail retains the *actual* E output and next seen register. -/
theorem memory_source_fitting_trace_succ_iff {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (r start : ℕ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign start) k y seen)
    (tail : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
        seen ab.val)) :
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap (r+1) start y seen ⟨ab,tail⟩ ↔
    memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap start y seen ab ∧
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
        seen ab.val) tail := by
  constructor
  · rintro ⟨hi,hG,hframe,hout,hseen,ht⟩
    exact ⟨⟨hi,hG,hframe,hout,hseen⟩,ht⟩
  · rintro ⟨⟨hi,hG,hframe,hout,hseen⟩,ht⟩
    exact ⟨hi,hG,hframe,hout,hseen,ht⟩

/-- The sum is over the ORIGINAL recursively indexed physical trace type:
no independent product fibre or artificial uniform orbit is introduced. -/
noncomputable def memorySourceFittingTraceSum {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (r start : ℕ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) : ℂ :=
  letI : Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k r start y seen) :=
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k r start y seen
  ∑ t : physicalOrientedIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns 1 k r start y seen,
    if memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap r start y seen t then
      memorySourceIndexedTraceWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig mu Knu zeta theta k N r start y seen t
    else 0

set_option maxHeartbeats 450000

/-- Full finite source trace disintegration at one genuine dependent edge.
The index family of each tail depends on the ACTUAL oriented-E output and
updated seen register; all G/E scalar factors, including the two conditional
Fock orbit probabilities, are inherited unchanged from the original kernel. -/
theorem memory_source_fitting_trace_sum_succ {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (r start : ℕ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k (r+1) start y seen =
    ∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k y seen,
      if memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap start y seen ab then
        physicalOrientedGEIndexedWeight SP smallMod BP bigMod
          J ell m cap patterns q rho N start Vsmall Vbig mu
          (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start))
          zeta theta (physicalAlternatingSign start) k y ab.val *
        memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
          ω life hcap q rho Vsmall Vbig mu Knu zeta theta k r (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val)
      else 0 := by
  classical
  letI : (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k y seen) →
    Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)) :=
    fun ab => physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)
  change (∑ t : (Σ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
    J ell m cap patterns (physicalAlternatingSign start) k y seen,
    physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)),
    if memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap (r+1) start y seen t then
      memorySourceIndexedTraceWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig mu Knu zeta theta k N (r+1) start y seen t
    else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hh : memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
    ω life k hcap start y seen ab
  · simp only [hh, ite_true]
    simp only [memorySourceFittingTraceSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail htail
    have hiff := memory_source_fitting_trace_succ_iff SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap r start y seen ab tail
    rw [hiff]
    simp only [hh, true_and]
    by_cases ht : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap r (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val) tail
    · simp only [ht, ite_true]
      rfl
    · simp only [ht, ite_false, mul_zero]
  · simp only [hh, ite_false]
    apply Finset.sum_eq_zero
    intro tail htail
    have hno : ¬ memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap (r+1) start y seen ⟨ab,tail⟩ := by
      intro hf
      exact hh ((memory_source_fitting_trace_succ_iff SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap r start y seen ab tail).mp hf).1
    simp only [hno, ite_false]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1SourceCanonicalStep -/

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

/-- The finite ORIGINAL conditional G/E edge sum, filtered by the full
dependent source fitting head, at a literal frozen root visit. Neither
the indexing set nor the original G/E scalar is replaced by a kernel. -/
noncomputable def memorySourceCanonicalFittingHeadMass {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (i : Fin N) : ℂ :=
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap true i.castSucc)
  let seen := memorySeenBeforeGValues BP bigMod
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩) i.val
  ∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k y seen,
    if memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap i.val y seen ab then
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho N i.val Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k y ab.val
    else 0

/-- In a source frozen profile, ANY legal matching head has the precise
canonical next projected state AND actual chronological next seen register.
No assumptions about its scalar being nonzero or about a product measure. -/
theorem memory_source_fitting_head_canonical_next {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (k : ℤ) (i : Fin N)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k y seen)
    (hh : memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap i.val y seen ab) :
    physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k ab.val =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.succ) ∧
    physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
      seen ab.val =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (i.val+1) := by
  obtain ⟨hi, _, _, hout, hseen⟩ := hh
  constructor
  · convert hout using 1
    congr 1
  · exact hseen

/-- Real dependent source trace recursion FACTORS after conditioning on
the genuine frozen omega/life profile. Although the tail type depends on
the actual E output and chronological seen, its value is constant on
every matching head; zero/nonmatching heads remain zero. -/
theorem memory_source_canonical_fitting_trace_step_factor {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (i : Fin N) (r : ℕ) (hr : i.val + (r+1) = N) :
    memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k
      (r+1) i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) =
    memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i *
    memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k
      r (i.val+1)
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.succ))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (i.val+1)) := by
  rw [memory_source_fitting_trace_sum_succ]
  unfold memorySourceCanonicalFittingHeadMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hh : memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) ab
  · have hnext := memory_source_fitting_head_canonical_next SP smallMod BP bigMod
      J ell m cap patterns ω life hcap k i _ _ ab hh
    simp only [hh, ite_true]
    rw [hnext.1, hnext.2]
  · simp only [hh, ite_false, zero_mul]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1FittingTelescope -/

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

/-- The existing original dependent filtered source trace sum from the
canonical physical input at a specified frozen visit. -/
noncomputable def memorySourceCanonicalFittingTail {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (i : Fin (N+1)) : ℂ :=
  memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
    ω life hcap q rho Vsmall Vbig mu Knu zeta theta k (N-i.val) i.val
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true i))
    (memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) i.val)

/-- An exact source kernel step gives the telescope relation on the
ACTUAL dependent source fitting tail, not an assumed finite Markov kernel. -/
theorem memory_source_canonical_fitting_tail_succ {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (i : Fin N) :
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i.castSucc =
    memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i *
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i.succ := by
  have hnat : N - i.val = (N-(i.val+1))+1 := by omega
  unfold memorySourceCanonicalFittingTail
  simp only [Fin.val_castSucc,Fin.val_succ]
  rw [hnat]
  exact memory_source_canonical_fitting_trace_step_factor SP smallMod BP bigMod
    J ell m cap patterns ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i
      (N-(i.val+1)) (by omega)

/-- Finite telescoping for arbitrary complex finite sequences. This
accounts for EVERY visit, including the exact final G_N factor. -/
theorem memory_finite_source_complex_telescope (F G : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i, i < N → F i = G i * F (i+1)) :
    F 0 = (∏ i ∈ Finset.range N, G i) * F N := by
  have hgeneral : ∀ m : ℕ, m ≤ N →
      F (N-m) = (∏ i ∈ Finset.Ico (N-m) N, G i) * F N := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp
    | succ m ih =>
      intro hm
      have hi : N - (m+1) < N := by omega
      have heq : N-m = N-(m+1)+1 := by omega
      calc
        F (N-(m+1)) = G (N-(m+1)) * F (N-(m+1)+1) :=
          hstep _ hi
        _ = G (N-(m+1)) * F (N-m) := by rw [heq]
        _ = G (N-(m+1)) * ((∏ i ∈ Finset.Ico (N-m) N, G i) * F N) := by
          rw [ih (by omega)]
        _ = (∏ i ∈ Finset.Ico (N-(m+1)) N, G i) * F N := by
          rw [Finset.prod_eq_prod_Ico_succ_bot hi]
          rw [← heq]
          ring
  have h := hgeneral N (le_refl N)
  simpa only [Nat.sub_self, Finset.range_eq_Ico] using h
end Green64FullPhysicalE

end

end

/-! ## MemoryB1FullSourceProduct -/

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

set_option maxHeartbeats 600000

/-- Source-specific finite product factorization of the ORIGINAL dependent
G0 E0 ... G_N indexed fitting trace. Neither the conditional input orbit
sums nor any original branch coefficients are replaced or simplified.
The final factor is the genuine original terminal G_N weighted source sum. -/
theorem memory_source_full_canonical_fitting_trace_product {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) :
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k (0 : Fin (N+1)) =
    (∏ i : Fin N,
      memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
        ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i) *
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hcap q rho Vsmall Vbig mu Knu zeta theta k
      (⟨N,Nat.lt_succ_self N⟩ : Fin (N+1)) := by
  let F : ℕ → ℂ := fun i => if hi : i ≤ N then
      memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
        ω life hcap q rho Vsmall Vbig mu Knu zeta theta k
        (⟨i,Nat.lt_succ_of_le hi⟩ : Fin (N+1))
    else 0
  let G : ℕ → ℂ := fun i => if hi : i < N then
      memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
        ω life hcap q rho Vsmall Vbig mu Knu zeta theta k
        (⟨i,hi⟩ : Fin N)
    else 0
  have hs (i : ℕ) (hi : i < N) : F i = G i * F (i+1) := by
    have h0 : i ≤ N := le_of_lt hi
    have h1 : i+1 ≤ N := Nat.succ_le_of_lt hi
    dsimp only [F,G]
    rw [dif_pos h0, dif_pos hi, dif_pos h1]
    exact memory_source_canonical_fitting_tail_succ SP smallMod BP bigMod
      J ell m cap patterns ω life hcap q rho Vsmall Vbig mu Knu zeta theta k ⟨i,hi⟩
  have h := memory_finite_source_complex_telescope F G N hs
  have hprod : (∏ i ∈ Finset.range N, G i) =
      ∏ i : Fin N,
        memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
          ω life hcap q rho Vsmall Vbig mu Knu zeta theta k i := by
    rw [← Fin.prod_univ_eq_prod_range G N]
    apply Finset.prod_congr rfl
    intro i hi
    simp [G, i.isLt]
  dsimp only [F] at h
  rw [dif_pos (Nat.zero_le N), dif_pos (le_refl N)] at h
  rw [hprod] at h
  have hz : (⟨0,Nat.lt_succ_of_le (Nat.zero_le N)⟩ : Fin (N+1)) = 0 := Fin.ext rfl
  simpa only [hz] using h
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingRootBoundary -/

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

/-- Entire original SOURCE ROOT mass restricted to a specified actual initial
Hilbert representative and the exactly fitting dependent frozen suffix.
Original sigma state and every indexed trace weight are retained. -/
noncomputable def memorySourceFixedInitialFittingRootSum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℂ :=
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  ∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
    if xt.1 = x0 ∧
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
    then
      memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R xt
    else 0

/-- The exact initial Hilbert mass, baseline, vacuum and birth gate peel
off WITHOUT altering the recursively conditioned original trace tree.
The remaining object is exactly the filtered true dependent source trace sum. -/
theorem memory_source_fixed_initial_fitting_root_factorization
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    memorySourceFixedInitialFittingRootSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R ω life hcap x0 =
      (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x0 : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)) *
      (if (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).Nodup then
        memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
          ω life hcap q rho Vsmall Vbig
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig) Knu zeta theta k
          (2*R) 0
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
          (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).toFinset
       else 0) := by
  classical
  let X := FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  let T : X → Type := fun x =>
    physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap x).toFinset
  letI : (x : X) → Fintype (T x) := fun x =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns
      1 k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap x).toFinset
  change (∑ xt : (Σ x : X, T x),
    if xt.1 = x0 ∧ memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
    then memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt else 0) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single x0]
  · change (∑ t : T x0,
      if x0 = x0 ∧ memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).toFinset t
      then memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R ⟨x0,t⟩ else 0) = _
    simp only [true_and]
    by_cases hbirth :
        (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).Nodup
    · simp only [hbirth, ite_true, memorySourceFittingTraceSum]
      simp only [memorySourceRootIndexedWeight, hbirth, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap (2*R) 0
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
          (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).toFinset t
      · simp [hf]
      · simp [hf]
    · simp [memorySourceRootIndexedWeight, hbirth]
  · intro x hx hne
    apply Finset.sum_eq_zero
    intro t ht
    simp only [hne, false_and, ite_false]
  · intro hn
    exact (hn (Finset.mem_univ x0)).elim
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFrozenPathReadout -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)

/-- Actual active lists are injective, derived from chronological G/E
legality, initial vacuum and distinct births. -/
def memoryActualWitnessFrozenPath :
    MemoryFrozenSourcePath SP smallMod BP J ell m patterns N :=
  (fun i => (H.before i.val).1,
    fun i g => ⟨((H.before i.val).2 g).1,
      (physical_finite_actual_path_good_every_visit SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k N H i.val
        (Nat.le_of_lt_succ i.isLt) g).1⟩,
    fun i => memoryPrimitiveEFrameOf SP smallMod BP bigMod
      J ell m cap patterns (H.beforeE i.val) (H.edge i.val))

theorem memory_actual_beforeE_original_coordinates (i : ℕ) (hi : i < N) :
    (H.beforeE i).1 = (H.before i).1 ∧
      ∀ g, ((H.beforeE i).2 g).1 = ((H.before i).2 g).1 := by
  have hg := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu
    (H.before i) (H.afterG i) (H.ghost i) (H.G_nonzero i (le_of_lt hi))).1
  have he := H.E_orbit_input i hi
  constructor
  · have hs := congrArg Prod.fst he
    exact hs.trans hg.1.symm
  · intro g
    have ha := congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (out.2 g).1) he
    exact ha.trans (hg.2 g).symm

/-- D uses the original sigma frame and every repeated auxiliary draw;
reading it from the frozen path loses none of its factors. -/
theorem memory_actual_frozen_D_exact (i : Fin N) :
    memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) i =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns (H.edge i.val).1) (H.edge i.val).2.1 (H.beforeE i.val)
      (H.edge i.val).2.2.1.sigmaBig (H.edge i.val).2.2.2.1 := by
  have hc := memory_actual_beforeE_original_coordinates SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H i.val i.isLt
  simp only [memoryFrozenSourceD, memoryActualWitnessFrozenPath,
    memoryPrimitiveEFrameOf, sourceOrientedPhysicalD, Fin.val_castSucc, hc.1, hc.2]
  rfl

/-- The signed offset in the terminal frozen sum obeys the ACTUAL source
edge displacement, with fixed visit orientation. -/
theorem memory_actual_frozen_offset_step (i : Fin N) :
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) k (i.val+1) -
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) k i.val =
    sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns (H.edge i.val).1) (H.edge i.val).2.1 (H.beforeE i.val)
      (H.edge i.val).2.2.1.sigmaBig (H.edge i.val).2.2.2.1
      (physicalAlternatingSign i.val) k := by
  rw [memory_frozen_source_offset_step SP smallMod BP bigMod J ell m patterns
    _ k i.val i.isLt]
  rw [memory_actual_frozen_D_exact]
  rfl

/-- Original frozen compatibility is a conclusion for EVERY actual
contributing path. This is forward readout only, not a weighted inverse. -/
theorem memory_actual_frozen_edge_allowed (i : Fin N) :
    memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) k i := by
  have hc := memory_actual_beforeE_original_coordinates SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H i.val i.isLt
  have hn (g : BG) : ((H.before (i.val+1)).2 g).1 =
      ((H.edge i.val).2.2.1.bigChoice g).1 :=
    congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (out.2 g).1) (H.E_output i.val i.isLt)
  have hl := H.E_legal i.val i.isLt
  rcases hl with ⟨ho, hk, ha, hb, hs⟩
  unfold memoryFrozenSourceEdgeAllowed memoryActualWitnessFrozenPath memoryPrimitiveEFrameOf
  simp only [Fin.val_castSucc, Fin.val_succ]
  refine ⟨ho, hk, ?_, ?_⟩
  · intro g j a
    rw [← hc.2 g, hn g]
    exact ha g j a
  · intro g j hj
    rw [← hc.2 g, hn g]
    exact (hb g).shared_copy j hj
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceOmegaRecovery -/

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

/-- The existing forward omega readout recovers the literal frozen source
coordinates of a contributing fitting root; no coefficient premise is added. -/
theorem memory_frozen_source_contributing_fitting_root_omega
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R)
    (hx : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩)
    (hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2)
    (hn : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0) :
    let w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hn⟩
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H = ω := by
  dsimp only
  let w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hn⟩
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have hy : physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true ⟨0,by omega⟩) := congrArg _ hx
  have hseen : (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) 0 := by
    rw [hx]
    exact memory_frozen_source_initial_seen SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated hs
  have hG (i : Fin (2*R+1)) := memory_frozen_source_fitting_trace_G_readout SP smallMod BP
    bigMod J ell m cap patterns ω life k hd.cap_saturated (2*R) 0 (by omega)
    _ _ xt.2 hy hseen hf i
  have hE (i : Fin (2*R)) := memory_frozen_source_fitting_trace_E_readout SP smallMod BP
    bigMod J ell m cap patterns ω life k hd.cap_saturated (2*R) 0 (by omega)
    _ _ xt.2 hf i
  have hbefore (i : Fin (2*R+1)) : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (H.before i.val) = physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated true i) := by
    simpa only [H,w,memory_source_root_to_actual_witness_path,Nat.mod_eq_of_lt i.isLt,
      Nat.zero_add] using (hG i).1
  have hframe (i : Fin (2*R)) : memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap
      patterns (H.beforeE i.val) (H.edge i.val) = ω.2.2 i := by
    let je : Fin (2*R) := ⟨i.val % (2*R), Nat.mod_lt _ (by have := hd.R_pos; omega)⟩
    have hje : je = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns
      (physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
        k (2*R) 0 _ _ xt.2 je).1
      (physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
        k (2*R) 0 _ _ xt.2 je).2 = ω.2.2 i
    rw [hje]
    simpa only [Nat.zero_add] using hE i
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (hbefore i)
  · apply Prod.ext
    · funext i g
      apply Subtype.ext
      exact congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (out.2 g).1) (hbefore i)
    · funext i
      exact hframe i
end Green64FullPhysicalE

end

end

/-! ## MemoryGlobalWeightedRootTarget -/

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
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

variable (cap : BG → ℕ)
/-- PINNED ACTUAL GLOBAL TERMINAL EQUALITY, NOT A THEOREM. The left side
is the full source-correct dependent physical root sum; the right side
contains exactly the original frozen source coefficients and all lifespan
terms. No occurrence-bijection or reconstruction premise is inserted. -/
def MemoryGlobalWeightedRootTarget
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : Prop :=
  MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R →
    memorySourceFullRootIndexedSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R =
    memoryFrozenSourceLifespanRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R

/-- Checked FORWARD source-coordinate readout for every contributing
actual root. No missing-congruence, canonical-residue, surjectivity or
weighted inverse field is claimed. Those remain required by the target. -/
theorem memory_source_root_frozen_forward_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    ∃ ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R),
    ∃ life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1),
      (∀ i, ω.1 i = (H.before i.val).1 ∧
        ∀ g j, (ω.2.1 i g).val j = ((H.before i.val).2 g).1 j) ∧
      (∀ i, ω.2.2 i = memoryPrimitiveEFrameOf SP smallMod BP bigMod
        J ell m cap patterns (H.beforeE i.val) (H.edge i.val)) ∧
      (∀ i, memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i) ∧
      (∀ i : Fin (2*R),
        memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k (i.val+1) -
        memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k i.val =
        sourceOrientedStep SP smallMod BP bigMod J ell m cap
          (patterns (H.edge i.val).1) (H.edge i.val).2.1 (H.beforeE i.val)
          (H.edge i.val).2.2.1.sigmaBig (H.edge i.val).2.2.2.1
          (physicalAlternatingSign i.val) k) ∧
      (∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        k (2*R) H g) (2*R+1) (fun p => memoryFiniteLifeErase (life ⟨g,p⟩))) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  obtain ⟨life, hf⟩ := memory_source_root_finite_life_readout
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd.R_pos hd.big_injective w
  refine ⟨memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H,
    (fun p => life p.1 p.2), ?_, ?_, ?_, ?_, hf⟩
  · intro i
    exact ⟨rfl, fun _ _ => rfl⟩
  · intro i
    rfl
  · intro i
    exact memory_actual_frozen_edge_allowed SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H i
  · intro i
    exact memory_actual_frozen_offset_step SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H i

/-- The finite root-derived profile also gives the exact chronological
seen test in every numerical BIG-prime fibre, including visit 0 and N. -/
theorem memory_source_root_finite_seen_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    ∃ life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1),
      (∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        k (2*R) H g) (2*R+1) (fun p => memoryFiniteLifeErase (life ⟨g,p⟩))) ∧
      (∀ (g : BG) (p : BP g) (i : ℕ), i ≤ 2*R →
        (p ∈ actualNumericalSeenGroup BP bigMod (H.seen i) g ↔
          match life ⟨g,p⟩ with
          | none => False
          | some az => az.1.val < i ∨ (az.1.val = i ∧
            ∃ j : Fin (J+ell), ((H.before i).2 g).1 j = p))) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  obtain ⟨life, hf⟩ := memory_source_root_finite_life_readout
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd.R_pos hd.big_injective w
  refine ⟨fun p => life p.1 p.2, hf, ?_⟩
  intro g p i hi
  have hh := memory_actual_group_seen_life_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    k (2*R) H hd.big_injective g (fun p => memoryFiniteLifeErase (life g p)) (hf g) i hi p
  cases he : life g p <;> simpa [memoryFiniteLifeErase, he] using hh
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFrozenCanonicalAlignment -/

section

open Classical
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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)


/-- The frozen coordinate used by the exact weighted terminal has the
same signed offset as the contributing physical path at EVERY real visit. -/
theorem memory_actual_frozen_offset_exact (i : ℕ) (hi : i ≤ N) :
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) k i =
    physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H i := by
  induction i with
  | zero => simp [memoryFrozenSourceOffset,physicalActualOffset]
  | succ i ih =>
    have hiN : i < N := by omega
    have hh := memory_actual_frozen_offset_step SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H ⟨i,hiN⟩
    have hp := physical_actual_offset_succ SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i
    change _ - _ = physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H i at hh
    simp only [Fin.val_mk] at hh
    rw [ih (le_of_lt hiN)] at hh
    omega

/-- Original frozen prime visits are exactly the actual active visits;
the finite coordinate change does not forget visit zero or N. -/
theorem memory_actual_frozen_visits_exact (g : BG) (p : BP g) :
    memoryFrozenSourceVisits SP smallMod BP J ell m patterns
      (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) ⟨g,p⟩ =
    memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H g p := by
  ext i
  simp only [memoryFrozenSourceVisits,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and,memoryActualWitnessFrozenPath,
    memorySourceWitnessActiveVisits,Finset.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j.isLt,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨hi,hj⟩
    exact ⟨⟨i,hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩

/-- Full list residue transport changes only the anchor function,
on its actual finite birth carrier and current visit. -/
theorem memory_canonical_pending_offset_congr {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (A : P → Finset ℕ) {n : ℕ} (life : P → MemoryLifespanChoice n)
    (x y : ℕ → ℤ) (he : ∀ t < n, x t = y t)
    (before : Bool) (i : ℕ) (hi : i < n) :
    memoryCanonicalPendingList modulus A life x before i =
    memoryCanonicalPendingList modulus A life y before i := by
  unfold memoryCanonicalPendingList
  apply List.map_congr_left
  intro p hp
  cases hl : life p with
  | none => rfl
  | some az => simp only [memoryScheduleResidue,he i hi,he az.1.val az.1.isLt]
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFrozenReadoutProof -/

section

open Classical
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

/-- Stronger source-facing readout: all canonical residue/Fock/register
fields are proved, and its offset is exactly the terminal's original
frozen offset at every real visit. This is still FORWARD, not weighted
surjectivity or a global occurrence bijection. -/
theorem memory_source_frozen_canonical_root_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    ∃ L : MemorySourceCanonicalRootReadout SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H,
      ∀ t ≤ 2*R, L.offset t =
        memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
          (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H) k t := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  obtain ⟨L⟩ := memory_source_canonical_root_readout SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd w
  refine ⟨L,?_⟩
  intro t ht
  rw [memory_actual_frozen_offset_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H t ht]
  induction t with
  | zero => simpa [physicalActualOffset] using L.offset_zero
  | succ t ih =>
    have hi : t < 2*R := by omega
    have hs := L.offset_step t hi
    change L.offset (t+1)-L.offset t =
      physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig mu k (2*R) H t at hs
    have hp := physical_actual_offset_succ SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H t
    have hh := ih (le_of_lt hi)
    omega
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFrozenFibrePartition -/

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


/-- The exact frozen terminal profile, with original full omega coordinates
and ONE finite lifespan for every source BIG prime. -/
abbrev MemorySourceFrozenRootProfile (R : ℕ) :=
  MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R) ×
  (PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))

/-- Forward profile of a raw indexed root. Zero-weight roots are kept as
none. Nonzero roots use the proved exact finite source lifespan readout, not an
assumed occurrence bijection or an arbitrary augmented pattern. -/
def memorySourceRootFrozenProfile
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :
    Option (MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R) :=
  if hn : memorySourceRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0 then
    let w : MemorySourceContributingRootTrace SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hn⟩
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let life := Classical.choose (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
    some (memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H,
      fun gp => life gp.1 gp.2)
  else none

/-- Exact disintegration of ALL original physical root weights over their
actual omega/life fibres. No fibre cardinality or factorization is assumed.
The remaining load-bearing theorem is evaluation of EACH inner fibre. -/
theorem memory_source_full_root_frozen_fibre_partition
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
        J ell m cap patterns k R
    memorySourceFullRootIndexedSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R =
    ∑ a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R,
      ∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R,
        if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
          memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
            q rho Vsmall Vbig Knu zeta theta k R xt else 0 := by
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  unfold memorySourceFullRootIndexedSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xt hxt
  by_cases hn : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
  · simp [memorySourceRootFrozenProfile,hn]
  · simp [memorySourceRootFrozenProfile,hn,not_ne_iff.mp hn]
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceLifeDetermined -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Lifespan endpoints are determined by active and the two genuine pending
occupancy schedules. This includes absent primes and singleton active lives. -/
theorem memory_schedule_life_determined {n : ℕ} (p : ℕ)
    (h1 h2 : ℕ → ZMod p) (A : Finset ℕ) (l1 l2 : MemoryLifespanChoice n)
    (hs1 : MemoryFrozenScheduleSupport p h1 A l1)
    (hs2 : MemoryFrozenScheduleSupport p h2 A l2)
    (hb : ∀ i < n, memoryScheduleBefore A l1 i ↔ memoryScheduleBefore A l2 i)
    (ha : ∀ i < n, memoryScheduleAfter A l1 i ↔ memoryScheduleAfter A l2 i) :
    l1 = l2 := by
  have presence (az : Fin n × Fin n) (h : ℕ → ZMod p)
      (hs : MemoryFrozenScheduleSupport p h A (some az)) (i : ℕ) :
      (i ∈ A ∨ memoryScheduleBefore A (some az) i ∨
        memoryScheduleAfter A (some az) i) ↔ az.1.val ≤ i ∧ i ≤ az.2.val := by
    simp only [MemoryFrozenScheduleSupport] at hs
    simp only [memoryScheduleBefore,memoryScheduleAfter]
    constructor
    · rintro (hi | hi | hi)
      · exact ⟨(hs.2.1 i hi).1,(hs.2.1 i hi).2.1⟩
      · omega
      · omega
    · rintro ⟨hi,hz⟩
      by_cases hA : i ∈ A
      · exact Or.inl hA
      · apply Or.inr
        by_cases he : az.1.val = az.2.val
        · have hie : i = az.1.val := by omega
          exact False.elim (hA (hie ▸ hs.2.2.2 he))
        · by_cases hb : az.1.val < i
          · exact Or.inl ⟨hb,hz,hA⟩
          · exact Or.inr ⟨hi,by omega,hA⟩
  have hpres (i : ℕ) (hi : i < n) :
      (i ∈ A ∨ memoryScheduleBefore A l1 i ∨ memoryScheduleAfter A l1 i) ↔
      (i ∈ A ∨ memoryScheduleBefore A l2 i ∨ memoryScheduleAfter A l2 i) := by
    rw [hb i hi,ha i hi]
  cases he1 : l1 with
  | none =>
    cases he2 : l2 with
    | none => rfl
    | some az =>
      have hsaz : MemoryFrozenScheduleSupport p h2 A (some az) := by simpa [he2] using hs2
      simp only [he1,MemoryFrozenScheduleSupport] at hs1
      have hp := (presence az h2 (by simpa [he2] using hs2) az.1.val).mpr
        ⟨le_rfl,hsaz.1⟩
      have hh := (hpres az.1.val az.1.isLt).mpr (by simpa [he2] using hp)
      simp [he1,hs1,memoryScheduleBefore,memoryScheduleAfter] at hh
  | some az =>
    have hsaz : MemoryFrozenScheduleSupport p h1 A (some az) := by simpa [he1] using hs1
    cases he2 : l2 with
    | none =>
      simp only [he2,MemoryFrozenScheduleSupport] at hs2
      have hp := (presence az h1 (by simpa [he1] using hs1) az.1.val).mpr
        ⟨le_rfl,hsaz.1⟩
      have hh := (hpres az.1.val az.1.isLt).mp (by simpa [he1] using hp)
      simp [he2,hs2,memoryScheduleBefore,memoryScheduleAfter] at hh
    | some bz =>
      have hsbz : MemoryFrozenScheduleSupport p h2 A (some bz) := by simpa [he2] using hs2
      have hA := presence az h1 (by simpa [he1] using hs1)
      have hB := presence bz h2 (by simpa [he2] using hs2)
      have hab : az.1.val ≤ az.2.val := hsaz.1
      have hba : bz.1.val ≤ bz.2.val := hsbz.1
      have intervals (i : ℕ) (hi : i < n) :
          (az.1.val ≤ i ∧ i ≤ az.2.val) ↔ (bz.1.val ≤ i ∧ i ≤ bz.2.val) := by
        rw [← hA i,← hB i]
        simpa [he1,he2] using hpres i hi
      have ha1 := (intervals az.1.val az.1.isLt).mp ⟨le_rfl,hab⟩
      have ha2 := (intervals bz.1.val bz.1.isLt).mpr ⟨le_rfl,hba⟩
      have hz1 := (intervals az.2.val az.2.isLt).mp ⟨hab,le_rfl⟩
      have hz2 := (intervals bz.2.val bz.2.isLt).mpr ⟨hba,le_rfl⟩
      exact congrArg some (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
end Green64FullPhysicalE

end

end

