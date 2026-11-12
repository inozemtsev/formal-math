module

public import Green64.Library.Correlation.Part010
public import Green64.Library.Weights.Part005
public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part007
public import Green64.Library.Correlation.Part006
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Correlation / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSourceLifespanWeightBridge -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]

/-- An exact actual SOURCE one-prime lifespan scalar, not generic
q_i/eta_i: the endpoints have q_0=q_N=sqrt(q), and the baseline
is 1 - (sum_i eta_i)/p from the source physical root. Each
pending hit consumes its real rho factors. The active run charges
V_g^{-r}/(p b_p) with the ghost endpoints and internal damping.
The nonzero baseline and rho conditions are explicit. -/
theorem physical_source_one_prime_lifespan_weight
    (q rho : ℝ) (N a z : ℕ) (Vbig : BG → ℝ)
    (g : BG) (p : BP g)
    (A hit : ℕ → Prop) [DecidablePred A] [DecidablePred hit]
    (haz : a ≤ z) (hzN : z ≤ N)
    (hsupp : ∀ i, A i → a ≤ i ∧ i ≤ z)
    (hsingle : a = z → A a) (hitA : hit a) (hitZ : hit z)
    (hρ : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    let Rho : ℂ := rho
    let V : ℂ := Vbig g
    let P : ℂ := bigMod g p
    let b : ℂ := physicalSourceBaseline BP bigMod q N g p
    let Qi (i : ℕ) : ℂ := (sourceVisitQ q N i : ℝ)
    let eta (i : ℕ) : ℂ := (sourceVisitEta q N i : ℝ)
    let runs := (Finset.range (N+1)).filter
      (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
    let promotions := (Finset.range (N+1)).filter
      (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
    let localRow (i : ℕ) :=
      (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then Rho else 1) *
      (if (z = i ∧ ¬ A i) ∧ hit i then -eta i / Rho
       else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then
          Qi i / Rho^2 else 1) *
      (if (a = i ∧ ¬ A i) ∧ hit i then
        -eta i * V / Rho else 1) *
      (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then Rho else 1)
    (1 / (V * P * b)) * (1/V)^promotions.card *
        (∏ i ∈ Finset.range (N+1), localRow i) =
      (1/V)^runs.card / (P*b) *
        (if A a then 1 else -eta a) *
        (if A z then 1 else -eta z) *
        (∏ i ∈ Finset.range (N+1),
          if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then Qi i else 1) := by
  have hρ' : (rho : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hV' : (Vbig g : ℂ) ≠ 0 := by exact_mod_cast hV
  have hp' : (bigMod g p : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (bigMod g p))
  have hb' : (physicalSourceBaseline BP bigMod q N g p : ℂ) ≠ 0 := by
    exact_mod_cast hb
  exact Green64MemoryJoin.lifespan_row_weight N a z A hit
    (rho : ℂ) (Vbig g : ℂ) (bigMod g p : ℂ)
    (physicalSourceBaseline BP bigMod q N g p : ℂ)
    (fun i => (sourceVisitQ q N i : ℂ))
    (fun i => (sourceVisitEta q N i : ℂ))
    haz hzN hsupp hsingle hitA hitZ hρ' hV' hp' hb'

end Green64FullPhysicalE

end

/-! ## MemoryFrozenPrimeOperationalScalar -/

section

open Classical
open scoped BigOperators
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 800000
namespace Green64FullPhysicalE
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Original active-run counter on the complete discrete visit carrier. -/
def memoryFrozenPrimeRuns (A : Finset ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N+1)).filter (fun i => i ∈ A ∧ (i=0 ∨ i-1 ∉ A))).card

/-- The one-prime original G/E row scalar after the already checked ghost
batch factorial sum, retaining its first mu-tilde, OLD promotions and all
four visit factors. No fibre cardinality or terminal equality is assumed. -/
def memoryFrozenPrimeOperationalScalar (q rho : ℝ) (N : ℕ)
    (Vbig : BG → ℝ) (g : BG) (p : BP g)
    (h : ℕ → ZMod (bigMod g p)) (A : Finset ℕ) :
    MemoryLifespanChoice (N+1) → ℂ
  | none => 1
  | some az =>
    let a := az.1.val
    let z := az.2.val
    let Rho : ℂ := rho
    let V : ℂ := Vbig g
    let P : ℂ := bigMod g p
    let b : ℂ := physicalSourceBaseline BP bigMod q N g p
    let Qi := fun i => (sourceVisitQ q N i : ℂ)
    let eta := fun i => (sourceVisitEta q N i : ℂ)
    let promotions := (Finset.range (N+1)).filter
      (fun i => i ∈ A ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ i-1 ∉ A)
    let localRow := fun i =>
      (if (a < i ∧ i ≤ z ∧ i ∉ A) ∧ h i = h a then Rho else 1) *
      (if (z = i ∧ i ∉ A) ∧ h i = h a then -eta i / Rho
        else if (a < i ∧ i ≤ z ∧ i ∉ A) ∧ h i = h a then Qi i / Rho^2 else 1) *
      (if (a = i ∧ i ∉ A) ∧ h i = h a then -eta i * V / Rho else 1) *
      (if (a ≤ i ∧ i < z ∧ i ∉ A) ∧ h i = h a then Rho else 1)
    (1/(V*P*b)) * (1/V)^promotions.card *
      ∏ i ∈ Finset.range (N+1), localRow i

/-- All rho and baseline factors telescope to the LITERAL frozen density;
none contributes b, and orphans carry zero active runs. -/
theorem memory_frozen_prime_operational_scalar_exact (q rho : ℝ) (N : ℕ)
    (Vbig : BG → ℝ) (g : BG) (p : BP g)
    (h : ℕ → ZMod (bigMod g p)) (A : Finset ℕ)
    (life : MemoryLifespanChoice (N+1))
    (hs : MemoryFrozenScheduleSupport (bigMod g p) h A life)
    (hr : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    (physicalSourceBaseline BP bigMod q N g p : ℂ) *
      memoryFrozenPrimeOperationalScalar BP bigMod q rho N Vbig g p h A life =
    (1/(Vbig g : ℂ))^(memoryFrozenPrimeRuns A N) *
      (memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q N) h A (N+1) life : ℂ) := by
  cases life with
  | none =>
    have he : A = ∅ := hs
    simp [he,memoryFrozenPrimeOperationalScalar,memoryFrozenPrimeRuns,
      memoryFrozenPrimeTerm,memoryAbsentTerm,physicalSourceBaseline]
  | some az =>
    have hn := memory_frozen_prime_supported_normal_form (bigMod g p)
      (sourceVisitEta q N) h A (N+1) az hs
    have ht := physical_source_one_prime_lifespan_weight BP bigMod q rho N
      az.1.val az.2.val Vbig g p (fun i => i ∈ A) (fun i => h i = h az.1.val)
      hs.1 (Nat.le_of_lt_succ az.2.isLt)
      (fun i hi => ⟨(hs.2.1 i hi).1,(hs.2.1 i hi).2.1⟩)
      hs.2.2.2 rfl hs.2.2.1 hr hV hb
    dsimp only at ht
    change memoryFrozenPrimeOperationalScalar BP bigMod q rho N Vbig g p h A (some az) = _ at ht
    rw [ht,hn]
    have hp : (bigMod g p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (bigMod g p)
    have hb' : (physicalSourceBaseline BP bigMod q N g p : ℂ) ≠ 0 := by exact_mod_cast hb
    have hi :
      (∏ i ∈ Finset.range (N+1),
        if (az.1.val < i ∧ i < az.2.val ∧ i ∉ A) ∧ h i = h az.1.val then
          (sourceVisitQ q N i : ℂ) else 1) =
      ((∏ i ∈ Finset.range (N+1),
        if az.1.val < i ∧ i < az.2.val ∧ i ∉ A then
          1 - sourceVisitEta q N i * (if h i = h az.1.val then (1 : ℝ) else 0)
        else 1 : ℝ) : ℂ) := by
      push_cast
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hc : az.1.val < i ∧ i < az.2.val ∧ i ∉ A
      · by_cases hh : h i = h az.1.val <;> simp [hc,hh,sourceVisitEta]
      · simp [hc]
    rw [hi]
    push_cast
    change _ = (1/(Vbig g : ℂ))^(memoryFrozenPrimeRuns A N) * _
    unfold memoryFrozenPrimeRuns
    have hca : ((if az.1.val ∈ A then 1 else -sourceVisitEta q N az.1.val : ℝ) : ℂ) =
        (if az.1.val ∈ A then 1 else -(sourceVisitEta q N az.1.val : ℂ)) := by
      split_ifs <;> simp
    have hcz : ((if az.2.val ∈ A then 1 else -sourceVisitEta q N az.2.val : ℝ) : ℂ) =
        (if az.2.val ∈ A then 1 else -(sourceVisitEta q N az.2.val : ℂ)) := by
      split_ifs <;> simp
    rw [hca,hcz]
    field_simp [hp,hb'] <;> ring
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenRunCounting -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Double-count maximal active-run starts, including the first visit. -/
theorem memory_frozen_runs_sum {P : Type} [Fintype P] [DecidableEq P]
    (A : P → Finset ℕ) (B : ℕ → Finset P) (N : ℕ)
    (hAB : ∀ p i, i ≤ N → (i ∈ A p ↔ p ∈ B i)) :
    (∑ p, memoryFrozenPrimeRuns (A p) N) =
      (B 0).card + ∑ i ∈ Finset.range N, (B (i+1) \ B i).card := by
  conv_lhs => simp only [memoryFrozenPrimeRuns, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh : ∀ i ∈ Finset.range (N+1),
      (∑ p : P, if i ∈ A p ∧ (i = 0 ∨ i-1 ∉ A p) then 1 else 0) =
        (if i = 0 then (B 0).card else (B i \ B (i-1)).card) := by
    intro i hi
    have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hz : i = 0
    · subst i
      simp only [true_or, and_true, hAB _ 0 hiN, if_true]
      rw [Finset.sum_boole]
      simp
    · have hpN : i-1 ≤ N := (Nat.sub_le i 1).trans hiN
      simp only [hz, false_or, hAB _ i hiN, hAB _ (i-1) hpN]
      rw [Finset.sum_boole]
      simp only [↓reduceIte, Nat.cast_id]
      apply congrArg Finset.card
      ext p
      simp [Finset.mem_sdiff]
  rw [Finset.sum_congr rfl hh]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel]
  rw [Nat.add_comm]

/-- The source's unshared ordered target slots are exactly new active labels.
This is purely finite counting; source specialization derives hcopy arithmetically. -/
theorem memory_new_active_card {P : Type} [DecidableEq P] (M : ℕ)
    (x y : Fin M → P) (hy : Function.Injective y) (shared : Finset (Fin M))
    (hcopy : ∀ j l, x j = y l ↔ j ∈ shared ∧ j = l) :
    ((Finset.univ.image y) \ (Finset.univ.image x)).card =
      Green64SmallHaar.unsharedSlots M shared := by
  have he : (Finset.univ.image y) \ (Finset.univ.image x) =
      (Finset.univ \ shared).image y := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨l, rfl⟩, hn⟩
      refine ⟨l, ?_, rfl⟩
      intro hl
      exact hn ⟨l, (hcopy l l).mpr ⟨hl,rfl⟩⟩
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l,rfl⟩, ?_⟩
      rintro ⟨j,hj⟩
      obtain ⟨hs,heq⟩ := (hcopy j l).mp hj
      exact hl (heq ▸ hs)
  rw [he, Finset.card_image_of_injective _ hy]
  simp [Green64SmallHaar.unsharedSlots, Finset.card_sdiff]
end Green64FullPhysicalE

end

end

/-! ## PhysicalActualLifespanScalar -/

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

/-- Every genuinely physical source BIG lifespan obeys the exact
one-prime q_i/rho/V/p/b_p scalar normalization once its original
source zero-residue hit predicate is supplied at both endpoints.
This does NOT identify the full physical path coefficient yet. -/
theorem physical_actual_lifespan_one_prime_scalar
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (hit : ℕ → Prop) [DecidablePred hit]
    (hρ : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : ∀ p : BP g, physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    ∃ life : BP g → Option (ℕ × ℕ),
      PhysicalLifeFits c (N+1) life ∧
      ∀ (p : BP g) (a z : ℕ), life p = some (a,z) →
        hit a → hit z →
        let A (i : ℕ) : Prop := p ∈ c.active i
        let Rho : ℂ := rho
        let V : ℂ := Vbig g
        let P : ℂ := bigMod g p
        let b : ℂ := physicalSourceBaseline BP bigMod q N g p
        let Qi (i : ℕ) : ℂ := (sourceVisitQ q N i : ℝ)
        let eta (i : ℕ) : ℂ := (sourceVisitEta q N i : ℝ)
        let runs := (Finset.range (N+1)).filter
          (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
        let promotions := (Finset.range (N+1)).filter
          (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
        let localRow (i : ℕ) :=
          (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then Rho else 1) *
          (if (z = i ∧ ¬ A i) ∧ hit i then -eta i / Rho
           else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then
              Qi i / Rho^2 else 1) *
          (if (a = i ∧ ¬ A i) ∧ hit i then
             -eta i * V / Rho else 1) *
          (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then Rho else 1)
        (1 / (V*P*b)) * (1/V)^promotions.card *
          (∏ i ∈ Finset.range (N+1), localRow i) =
        (1/V)^runs.card / (P*b) *
          (if A a then 1 else -eta a) *
          (if A z then 1 else -eta z) *
          (∏ i ∈ Finset.range (N+1),
            if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then Qi i else 1) := by
  dsimp only
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H g
  obtain ⟨life, hlife⟩ := physical_actual_BIG_lifespans
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum hVac g
  refine ⟨life, ?_, ?_⟩
  · exact hlife
  · intro p a z hp hitA hitZ
    have h := hlife p
    simp only [hp] at h
    have hAZ : a ≤ z := h.1
    have hzN : z ≤ N := Nat.lt_succ_iff.mp h.2.1
    have hSingle : a = z → p ∈ c.active a := h.2.2.1
    have hSupport : ∀ i, (p ∈ c.active i) →
        a ≤ i ∧ i ≤ z := by
      intro i
      exact (h.2.2.2 i).1
    exact physical_source_one_prime_lifespan_weight
      BP bigMod q rho N a z Vbig g p
      (fun i => p ∈ c.active i) hit
      hAZ hzN hSupport hSingle hitA hitZ
      hρ hV (hb p)

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceZeroHits -/

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

/-- TRUE visit-zero test: active primes are at their current anchor,
fresh G ghosts are born at zero, and OLD pending zero hits are tested
at their actual incoming physical Fock residues. This is not a free
predicate or a user-supplied list of hits. -/
noncomputable def physicalActualSourceZeroHit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (p : BP g) (i : ℕ) : Prop :=
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H g
  let old := Green64Fock.fockToList (((H.before i).2 g).2)
  i ≤ N ∧ (p ∈ c.active i ∨ p ∈ c.ghost i ∨
    ∃ j : Fin old.length,
      j ∈ Green64MemoryGhostOp.zeroOld old
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0) ∧
      (old.get j).1 = p)

/-- A physically selected OLD deletion was necessarily a genuine
zero-residue hit, because the primitive G witness chooses a
SUBSET of zeroOld, not an arbitrary OLD subset. -/
theorem physical_actual_selected_G_is_zero_hit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (p : BP g) (hi : i ≤ N)
    (hp : p ∈ ((H.ghost i g).1.1).image (fun j =>
      ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1)) :
    physicalActualSourceZeroHit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p i := by
  rcases Finset.mem_image.mp hp with ⟨j, hj, hjp⟩
  have hzero :
      j ∈ Green64MemoryGhostOp.zeroOld
        (Green64Fock.fockToList (((H.before i).2 g).2))
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0) :=
    (Finset.mem_powerset.mp (H.ghost i g).1.2) hj
  exact ⟨hi, Or.inr (Or.inr ⟨j, hzero, hjp⟩)⟩

/-- Actual endpoint termination, including the LAST G_N which
deletes every OLD zero when the final physical vacuum is imposed. -/
theorem physical_actual_ended_is_zero_hit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (p : BP g) (hi : i ≤ N)
    (hp : p ∈ (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g).ended i) :
    physicalActualSourceZeroHit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p i := by
  by_cases hlt : i < N
  · have hs : p ∈ ((H.ghost i g).1.1).image (fun j =>
        ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1) := by
      simpa [physicalActualSourceSetClock, hlt] using hp
    exact physical_actual_selected_G_is_zero_hit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H g p hi hs
  · have heq : i = N := by omega
    subst i
    have hterm := (physical_actual_terminal_vacuum_excludes_ghost_births
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hVac g).1
    let old := Green64Fock.fockToList (((H.before N).2 g).2)
    have hmem : p ∈ (old.map fun z => z.1).toFinset := by
      simpa [physicalActualSourceSetClock, actualPhysicalPendingSet, old]
        using hp
    rcases List.mem_map.mp (List.mem_toFinset.mp hmem) with
      ⟨z, hz, hzp⟩
    rcases List.mem_iff_get.mp hz with ⟨j, hj⟩
    have hselected : p ∈ ((H.ghost N g).1.1).image
        (fun t => (old.get t).1) := by
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, ?_⟩
      · simp [hterm]
      · simpa only [← hj] using hzp
    exact physical_actual_selected_G_is_zero_hit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N N H g p (Nat.le_refl N)
      (by simpa [old] using hselected)

/-- No independent endpoint-hit hypotheses: a real source lifespan
starts in a genuine active/fresh G hit and ends in a genuine active
or zero-OLD G hit. Its in-between hits are the physical residues. -/
theorem physical_actual_lifespan_endpoint_hits
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (g : BG)
    (life : BP g → Option (ℕ × ℕ))
    (hlife : PhysicalLifeFits
      (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g)
      (N+1) life)
    (p : BP g) (a z : ℕ) (hp : life p = some (a,z)) :
    physicalActualSourceZeroHit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p a ∧
    physicalActualSourceZeroHit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p z := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H g
  have h := hlife p
  simp only [hp] at h
  have hzN : z ≤ N := Nat.lt_succ_iff.mp h.2.1
  have haN : a ≤ N := le_trans h.1 hzN
  obtain ⟨_, _, _, hbirthA, _⟩ := h.2.2.2 a
  obtain ⟨_, _, _, _, hendZ⟩ := h.2.2.2 z
  have hFresh := (physical_source_clock_all_rows
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum g a).1
  constructor
  · rcases Finset.mem_union.mp (hbirthA.mpr rfl) with hf | hg
    · exact ⟨haN, Or.inl (hFresh hf)⟩
    · exact ⟨haN, Or.inr (Or.inl hg)⟩
  · rcases Finset.mem_union.mp (hendZ.mpr rfl) with he | ha
    · exact physical_actual_ended_is_zero_hit
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N z H hVac g p hzN he
    · exact ⟨hzN, Or.inl (Finset.mem_sdiff.mp ha).1⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualGlobalLifespanScalar -/

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

/-- The actual SOURCE one-prime rho/G/E normalization on a REAL
oriented physical witness clock. This is the lifespan scalar piece,
not the whole physical operator path weight: K, auxiliary D, SMALL
Haar, Fourier return, permutations and factorials are separate. -/
noncomputable def physicalActualSourcePrimeScalar
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (p : BP g) (az : Option (ℕ × ℕ)) : ℂ :=
  match az with
  | none => 1
  | some (a,z) =>
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    let A (i : ℕ) : Prop := p ∈ c.active i
    let hit (i : ℕ) : Prop := physicalActualSourceZeroHit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H g p i
    let Rho : ℂ := rho
    let V : ℂ := Vbig g
    let P : ℂ := bigMod g p
    let b : ℂ := physicalSourceBaseline BP bigMod q N g p
    let Qi (i : ℕ) : ℂ := (sourceVisitQ q N i : ℝ)
    let eta (i : ℕ) : ℂ := (sourceVisitEta q N i : ℝ)
    let promotions := (Finset.range (N+1)).filter
      (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
    let localRow (i : ℕ) :=
      (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then Rho else 1) *
      (if (z = i ∧ ¬ A i) ∧ hit i then -eta i / Rho
       else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then
         Qi i / Rho^2 else 1) *
      (if (a = i ∧ ¬ A i) ∧ hit i then
        -eta i * V / Rho else 1) *
      (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then Rho else 1)
    (1 / (V*P*b)) * (1/V)^promotions.card *
      (∏ i ∈ Finset.range (N+1), localRow i)

/-- The genuine source lifespan density factor for the SAME concrete
physical set and zero-residue clock. No free hit predicate appears. -/
noncomputable def physicalActualTargetPrimeScalar
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (p : BP g) (az : Option (ℕ × ℕ)) : ℂ :=
  match az with
  | none => 1
  | some (a,z) =>
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    let A (i : ℕ) : Prop := p ∈ c.active i
    let hit (i : ℕ) : Prop := physicalActualSourceZeroHit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H g p i
    let V : ℂ := Vbig g
    let P : ℂ := bigMod g p
    let b : ℂ := physicalSourceBaseline BP bigMod q N g p
    let Qi (i : ℕ) : ℂ := (sourceVisitQ q N i : ℝ)
    let eta (i : ℕ) : ℂ := (sourceVisitEta q N i : ℝ)
    let runs := (Finset.range (N+1)).filter
      (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
    (1/V)^runs.card / (P*b) *
      (if A a then 1 else -eta a) *
      (if A z then 1 else -eta z) *
      (∏ i ∈ Finset.range (N+1),
        if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then Qi i else 1)

/-- Full actual source 1-prime scalar, with BOTH endpoint zero hits
PROVED from the physically legal G witnesses and terminal vacuum,
not supplied as independent assumptions. -/
theorem physical_actual_one_prime_scalar_no_hit_hypotheses
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (g : BG) (life : BP g → Option (ℕ × ℕ))
    (hlife : PhysicalLifeFits
      (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g)
      (N+1) life)
    (p : BP g) (a z : ℕ) (hp : life p = some (a,z))
    (hρ : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    physicalActualSourcePrimeScalar SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p (life p) =
    physicalActualTargetPrimeScalar SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g p (life p) := by
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H g
  have h := hlife p
  simp only [hp] at h
  have hAZ : a ≤ z := h.1
  have hzN : z ≤ N := Nat.lt_succ_iff.mp h.2.1
  have hSingle : a = z → p ∈ c.active a := h.2.2.1
  have hSupport : ∀ i, p ∈ c.active i → a ≤ i ∧ i ≤ z := by
    intro i
    exact (h.2.2.2 i).1
  obtain ⟨hHitA, hHitZ⟩ := physical_actual_lifespan_endpoint_hits
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum hVac g life hlife p a z hp
  have hScalar := physical_source_one_prime_lifespan_weight
    BP bigMod q rho N a z Vbig g p
    (fun i => p ∈ c.active i)
    (fun i => physicalActualSourceZeroHit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H g p i)
    hAZ hzN hSupport hSingle hHitA hHitZ hρ hV hb
  simpa only [hp, physicalActualSourcePrimeScalar,
    physicalActualTargetPrimeScalar] using hScalar

/-- A SINGLE GLOBAL physical-source scalar normalization over
ALL big groups and ALL prime labels, using their ACTUAL
path-derived lifespans and TRUE Fock zero-residue hits.
The operator-to-literal-history bijection and Fourier identity
remain separate obligations; this statement does not assume them. -/
theorem physical_actual_global_big_prime_lifespan_product
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hρ : rho ≠ 0) (hV : ∀ g, Vbig g ≠ 0)
    (hb : ∀ g p, physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    ∃ life : (g : BG) → BP g → Option (ℕ × ℕ),
      (∀ g, PhysicalLifeFits
        (physicalActualSourceSetClock SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H g)
        (N+1) (life g)) ∧
      (∏ g : BG, ∏ p : BP g,
        physicalActualSourcePrimeScalar SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          g p (life g p)) =
      (∏ g : BG, ∏ p : BP g,
        physicalActualTargetPrimeScalar SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          g p (life g p)) := by
  classical
  let life : (g : BG) → BP g → Option (ℕ × ℕ) := fun g =>
    Classical.choose (physical_actual_BIG_lifespans
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hnum hVac g)
  have hfits : ∀ g, PhysicalLifeFits
      (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g)
      (N+1) (life g) := by
    intro g
    exact Classical.choose_spec (physical_actual_BIG_lifespans
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hnum hVac g)
  refine ⟨life, hfits, ?_⟩
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro p hp
  cases hv : life g p with
  | none =>
      simp [physicalActualSourcePrimeScalar,
        physicalActualTargetPrimeScalar, hv]
  | some az =>
      rcases az with ⟨a,z⟩
      simpa only [hv] using
        (physical_actual_one_prime_scalar_no_hit_hypotheses
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H hnum hVac
          g (life g) (hfits g) p a z hv hρ (hV g) (hb g p))

/-- Same global physical BIG-lifespan normalization with the natural
source positivity assumptions, not arbitrary nonzero baseline axioms.
The large-prime inequality is the finite explicit hypothesis behind
source b_p > 0 (and is satisfied in its asymptotic large-prime regime). -/
theorem physical_actual_global_big_prime_lifespan_product_source_conditions
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrho : 0 < rho) (hV : ∀ g, 0 < Vbig g)
    (hp : ∀ g p, N + 1 < bigMod g p) :
    ∃ life : (g : BG) → BP g → Option (ℕ × ℕ),
      (∀ g, PhysicalLifeFits
        (physicalActualSourceSetClock SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H g)
        (N+1) (life g)) ∧
      (∏ g : BG, ∏ p : BP g,
        physicalActualSourcePrimeScalar SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          g p (life g p)) =
      (∏ g : BG, ∏ p : BP g,
        physicalActualTargetPrimeScalar SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          g p (life g p)) := by
  apply physical_actual_global_big_prime_lifespan_product
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum hVac
  · exact ne_of_gt hrho
  · intro g
    exact ne_of_gt (hV g)
  · intro g p
    exact ne_of_gt (physicalSourceBaseline_positive_above_visits
      BP bigMod q N g p hq0 hq1 (hp g p))

end Green64FullPhysicalE

end

/-! ## PhysicalActualFullGEWeight -/

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

/-- ALL real BIG ghost factors multiplied on an actual physical G
witness, without a postulated transition probability. Every fresh
particle is physically constrained to residue zero by nonzero G. -/
theorem physical_actual_G_full_scalar_exact
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig x y c ≠ 0) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig x y c =
      ∏ g : BG, physicalActualGhostFactor
        SP smallMod BP bigMod (J+ell) cap q rho N i
        Vbig muBig x c g := by
  have hstage := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap
    q rho N i Vbig muBig x y c hterm).1
  unfold physicalGBranchTerm
  rw [if_pos hstage]
  exact Finset.prod_congr rfl (fun g _ =>
    physical_actual_G_group_weight_exact
      SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig x y c hterm g)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralTermZero -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Every actual OLD term index selected by G_i is at physical
residue ZERO, using the real Fock atom rather than an independent
residue assigned to be zero artificially. -/
theorem physical_actual_literal_ended_zero
    (i : ℕ) (hi : i ≤ N)
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod (H.before i) p = 0 := by
  obtain ⟨g, _, hpG⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp hpG
  let old := Green64Fock.fockToList (((H.before i).2 g).2)
  have hzeroIndex : j ∈ Green64MemoryGhostOp.zeroOld old
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0) := by
    have hz := (Finset.mem_powerset.mp (H.ghost i g).1.2) hj
    simpa [old] using hz
  have hzero : (old.get j).2 = 0 := by
    simpa [Green64MemoryGhostOp.zeroOld] using hzeroIndex
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi) g
  have hN : (old.map fun a => a.1).Nodup := by
    have h := hGood.2.1
    rw [physicalProjectionPendingValues_exact] at h
    exact Multiset.coe_nodup.mp h
  have hmem : (⟨(old.get j).1, 0⟩ :
      Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.before i).2 g).2) := by
    have hm := List.get_mem old j
    have hc : (⟨(old.get j).1, (old.get j).2⟩ :
        Green64Fock.Atom (BP g) (bigMod g)) ∈ old := by
      simpa using hm
    rw [hzero] at hc
    simpa [old, Green64Fock.fockMultiset, Green64Fock.fockToList] using hc
  have hres := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.before i)
    (⟨g, (old.get j).1⟩ : PhysicalSourcePrime BP)
    (by simpa [old] using hN) (0 : ZMod (bigMod g (old.get j).1)) hmem
  rw [← hjp]
  exact hres

/-- EXACT RowValid.term_zero predicate for the real flattened
pendingBefore list, selected OLD indices and true Fock residues. -/
theorem physical_actual_literal_term_zero
    (i : ℕ) (hi : i ≤ N)
    (j : Fin (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).length)
    (hj : j ∈ physicalActualLiteralTermIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before i)
      ((physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).get j) = 0 := by
  apply physical_actual_literal_ended_zero
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  exact (literal_indices_for_exact _ _ j).mp hj

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralGhostZero -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Every source ghost selected from the actual joint G_i branch
has physical residue zero in AFTER-G memory. The zero is forced
by the nonzero original COMPLEX ghost coefficient. -/
theorem physical_actual_literal_ghost_birth_zero
    (i : ℕ) (hi : i ≤ N)
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) p = 0 := by
  unfold physicalActualLiteralGhostBatch at hp
  obtain ⟨g, _, hpGroup⟩ := List.mem_flatMap.mp hp
  unfold physicalActualLiteralGhostGroup at hpGroup
  obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hpGroup
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp ha
  have hZ := physical_actual_nonzero_G_ghost_birth_zero
    SP smallMod BP bigMod (J+ell) cap
    q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i hi) g j
  have hAtom :
      (H.ghost i g).2.2 j ∈
      Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
    exact (physical_actual_G_pending_atoms_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g
      ((H.ghost i g).2.2 j)).mpr (Or.inr ⟨j,rfl⟩)

  have hAtom0 :
      (⟨((H.ghost i g).2.2 j).1, 0⟩ :
        Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
    have hm := hAtom
    change (⟨((H.ghost i g).2.2 j).1, ((H.ghost i g).2.2 j).2⟩ :
      Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.afterG i).2 g).2) at hm
    simpa only [hZ] using hm
  have hBefore := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  have hAfter := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
    (H.seen i) hBefore (H.G_nonzero i hi)
    (H.G_birth_eligible i hi)
  have hN : ((Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)).Nodup := by
    have hn := (hAfter g).2.1
    rw [physicalProjectionPendingValues_exact] at hn
    exact Multiset.coe_nodup.mp hn
  have hres := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.afterG i)
    (⟨g, ((H.ghost i g).2.2 j).1⟩ : PhysicalSourcePrime BP)
    hN (0 : ZMod (bigMod g ((H.ghost i g).2.2 j).1)) hAtom0
  rw [← hpa, ← hj]
  exact hres

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralSurvivingResidues -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Groupwise prime uniqueness in actual source Fock BEFORE G_i. -/
theorem physical_actual_literal_before_pending_nodup
    (i : ℕ) (hi : i ≤ N) (g : BG) :
    ((Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => a.1)).Nodup := by
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi) g
  have h := hGood.2.1
  rw [physicalProjectionPendingValues_exact] at h
  exact Multiset.coe_nodup.mp h

/-- Groupwise prime uniqueness AFTER exact original G_i branch. -/
theorem physical_actual_literal_afterG_pending_nodup
    (i : ℕ) (hi : i ≤ N) (g : BG) :
    ((Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)).Nodup := by
  have hBefore := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  have hAfter := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap
    q rho N i Vbig muBig (H.before i) (H.afterG i)
    (H.ghost i) (H.seen i) hBefore
    (H.G_nonzero i hi) (H.G_birth_eligible i hi)
  have h := (hAfter g).2.1
  rw [physicalProjectionPendingValues_exact] at h
  exact Multiset.coe_nodup.mp h

/-- A genuinely unselected OLD atom retains its residue, even
across the original G before/after Fock representative permutation. -/
theorem physical_actual_literal_surviving_old_residue_unchanged
    (i : ℕ) (hi : i ≤ N) (p : PhysicalSourcePrime BP)
    (hmem : p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (hnot : p ∉ physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before i) p := by
  unfold physicalActualLiteralPendingBefore at hmem
  obtain ⟨g, _, hpG⟩ := List.mem_flatMap.mp hmem
  obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hpG
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
  have hnotJ : j ∉ (H.ghost i g).1.1 := by
    intro hjSel
    have hpEnded : (⟨g,a.1⟩ : PhysicalSourcePrime BP) ∈
        physicalActualLiteralEndedValues SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i := by
      apply Finset.mem_biUnion.mpr
      refine ⟨g, Finset.mem_univ g, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨j,hjSel,?_⟩
      simpa only [hj]
    exact hnot (hpa ▸ hpEnded)
  have hpreAtom : a ∈
      Green64Fock.fockMultiset (((H.before i).2 g).2) := by
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using ha
  have hpostAtom : a ∈
      Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
    apply (physical_actual_G_pending_atoms_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g a).mpr
    exact Or.inl ⟨j,hnotJ,hj⟩

  have hNpre := physical_actual_literal_before_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g
  have hNpost := physical_actual_literal_afterG_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g
  have hResPre := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.before i)
    (⟨g,a.1⟩ : PhysicalSourcePrime BP) hNpre a.2
    (by simpa using hpreAtom)
  have hResPost := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.afterG i)
    (⟨g,a.1⟩ : PhysicalSourcePrime BP) hNpost a.2
    (by simpa using hpostAtom)
  rw [← hpa]
  exact hResPost.trans hResPre.symm

/-- Exact old_pending_unchanged on the original flattened OLD
list, with literal term indices and actual residue functions. -/
theorem physical_actual_literal_old_pending_unchanged
    (i : ℕ) (hi : i ≤ N)
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (hnot : p ∉
      (physicalActualLiteralTermIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).image
      (physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).get) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before i) p := by
  exact physical_actual_literal_surviving_old_residue_unchanged
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi p hp
    (by rwa [physical_actual_literal_term_index_image] at hnot)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralPromotionResidue -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Original physical E OLD promotion carries the exact after-G
Fock residue (not an independent Markov residue). -/
theorem physical_actual_literal_promotion_zero_canonical
    (i : ℕ) (hi : i < N) (g : BG)
    (j : Fin (J+ell))
    (hj : j ∈ (((H.edge i).2.2.1.bigChoice g).2).2.1) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i)
      (actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g j) +
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (physicalSourcePrimeValue BP bigMod
        (actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i g j))) = 0 := by
  let x := (H.beforeE i).2 g
  let c := ((H.edge i).2.2.1.bigChoice g).2
  let a := (x.2.2 (c.2.2 ⟨j,hj⟩))
  have hlegal := (H.E_legal i hi).2.2.2.1 g
  have hmatch := hlegal.promoted_matches ⟨j,hj⟩
  have hz := hlegal.promoted_zero ⟨j,hj⟩

  have hE : a ∈ Green64Fock.fockMultiset (((H.beforeE i).2 g).2) := by
    simp [a, x, Green64Fock.fockMultiset, Green64Fock.fockToList]
  have hG : a ∈ Green64Fock.fockMultiset (((H.afterG i).2 g).2) :=
    (physical_actual_GE_orbit_preserves_atoms
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g a).mp hE
  have hn := physical_actual_literal_afterG_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi) g
  have hres : physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) (⟨g,a.1⟩ : PhysicalSourcePrime BP) = a.2 :=
    physical_literal_fock_residue_of_atom
      BP bigMod cap SP smallMod (H.afterG i)
      (⟨g,a.1⟩ : PhysicalSourcePrime BP) hn a.2
      (by simpa using hG)
  have hz' : a.2 +
      (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (bigMod g a.1)) = 0 := by
    simpa only [a, x, c, physicalActualEdgeDelta] using hz
  have hh : physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) (⟨g,a.1⟩ : PhysicalSourcePrime BP) +
      (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (physicalSourcePrimeValue BP bigMod
          (⟨g,a.1⟩ : PhysicalSourcePrime BP))) = 0 := by
    rw [hres]
    change a.2 + (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g a.1)) = 0
    exact hz'
  have htarget :
      actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g j =
      (⟨g,a.1⟩ : PhysicalSourcePrime BP) := by
    exact congrArg (fun pp => (⟨g,pp⟩ : PhysicalSourcePrime BP)) hmatch
  rw [htarget]
  simpa only [physicalSourcePrimeValue] using hh

/-- RowValid.promotion_zero, on the genuine globally flattened target
promotion-index image and exact after-G residue function. -/
theorem physical_actual_literal_promotion_zero
    (i : ℕ) (hi : i < N) (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) p +
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (physicalSourcePrimeValue BP bigMod p)) = 0 := by
  obtain ⟨⟨g,j⟩, hj, htarget⟩ := Finset.mem_image.mp hp
  rw [← htarget]
  exact physical_actual_literal_promotion_zero_canonical
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g j (Finset.mem_filter.mp hj).2

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralStoreReset -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Physical next-row residue of an actual E_i store is EXACTLY
the oriented global signed displacement Δ. -/
theorem physical_actual_literal_store_reset_canonical
    (i : ℕ) (hi : i < N) (g : BG)
    (j : Fin (J+ell))
    (hj : j ∈ (((H.edge i).2.2.1.bigChoice g).2).1) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before (i+1))
      (actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g j) =
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (physicalSourcePrimeValue BP bigMod
        (actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i g j))) := by
  let x := (H.beforeE i).2 g
  let b := (H.edge i).2.2.1
  have hn := physical_actual_literal_before_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi) g
  have hm := physical_actual_literal_store_residue_delta
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g j hj

  let pp : BP g := x.1 (b.sigmaBig g j)
  have hStored :
      (⟨pp, (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (bigMod g pp))⟩ :
        Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) := by
    simpa only [pp, x, b, physicalActualEdgeDelta] using hm
  have hres := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.before (i+1))
    (⟨g,pp⟩ : PhysicalSourcePrime BP) hn
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g pp)) hStored
  change physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before (i+1)) (⟨g,pp⟩ : PhysicalSourcePrime BP) =
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (physicalSourcePrimeValue BP bigMod
        (⟨g,pp⟩ : PhysicalSourcePrime BP)))
  exact hres

/-- The literal global STORE selection obeys the source residueNext
reset, with true next-visit Fock residues. -/
theorem physical_actual_literal_store_reset
    (i : ℕ) (hi : i < N) (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralStoreValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before (i+1)) p =
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (physicalSourcePrimeValue BP bigMod p)) := by
  obtain ⟨⟨g,j⟩, hj, htarget⟩ := Finset.mem_image.mp hp
  rw [← htarget]
  exact physical_actual_literal_store_reset_canonical
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g j (Finset.mem_filter.mp hj).2

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralEndpointPerm -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Canonical source activeSlots j = x(sigma j), so original
sourcePerm = sigma^{-1} reconstructs raw unsampled endpoint order. -/
noncomputable def physicalActualLiteralCanonicalSourceList (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
    (fun a => actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2)

/-- Canonical target activeSlots j = target(tau j), hence targetPerm
is tau^{-1} and INDEPENDENT of the sampled sigma. -/
noncomputable def physicalActualLiteralCanonicalTargetList (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
    (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2)

/-- This is RowValid.source_order as an actual definitional identity. -/
theorem physical_actual_literal_source_order (i : ℕ) :
    physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1
        (((H.edge i).2.2.1.sigmaBig a.1).symm a.2)) := rfl

theorem physical_actual_literal_target_order (i : ℕ) :
    physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1
        (((H.edge i).2.2.1.tauBig a.1).symm a.2)) := rfl

theorem physical_actual_literal_source_order_membership
    (i : ℕ) (p : PhysicalSourcePrime BP) :
    p ∈ physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ↔
    p ∈ physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  constructor
  · intro hp
    unfold physicalActualLiteralRawSourceList at hp
    obtain ⟨⟨g,j⟩, _, h⟩ := List.mem_map.mp hp
    apply List.mem_map.mpr
    exact ⟨⟨g, (((H.edge i).2.2.1.sigmaBig g).symm j)⟩,
      by simp, h⟩
  · intro hp
    unfold physicalActualLiteralCanonicalSourceList at hp
    obtain ⟨⟨g,j⟩, _, h⟩ := List.mem_map.mp hp
    unfold physicalActualLiteralRawSourceList
    apply List.mem_map.mpr
    refine ⟨⟨g, (((H.edge i).2.2.1.sigmaBig g) j)⟩, by simp, ?_⟩
    simpa using h

theorem physical_actual_literal_target_order_membership
    (i : ℕ) (p : PhysicalSourcePrime BP) :
    p ∈ physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ↔
    p ∈ physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  constructor
  · intro hp
    unfold physicalActualLiteralRawTargetList at hp
    obtain ⟨⟨g,j⟩, _, h⟩ := List.mem_map.mp hp
    apply List.mem_map.mpr
    exact ⟨⟨g, (((H.edge i).2.2.1.tauBig g).symm j)⟩,
      by simp, h⟩
  · intro hp
    unfold physicalActualLiteralCanonicalTargetList at hp
    obtain ⟨⟨g,j⟩, _, h⟩ := List.mem_map.mp hp
    unfold physicalActualLiteralRawTargetList
    apply List.mem_map.mpr
    refine ⟨⟨g, (((H.edge i).2.2.1.tauBig g) j)⟩, by simp, ?_⟩
    simpa using h

theorem physical_actual_literal_canonical_source_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralCanonicalSourceList
  apply List.Nodup.map
    (physical_actual_literal_source_slot_injective
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
  exact Finset.nodup_toList _

theorem physical_actual_literal_canonical_target_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralCanonicalTargetList
  apply List.Nodup.map
    (physical_actual_literal_target_slot_injective
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
  exact Finset.nodup_toList _

/-- The exact RowValid.source_perm between sampled canonical
activeSlots and raw source order: sigma^{-1} is not tau^{-1}. -/
theorem physical_actual_literal_source_perm
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
    (physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply (List.perm_ext_iff_of_nodup
    (physical_actual_literal_raw_source_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_canonical_source_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)).mpr
  exact physical_actual_literal_source_order_membership
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i

/-- The independent target tau^{-1} likewise gives the exact
RowValid.target_perm without identifying the two Haar frames. -/
theorem physical_actual_literal_target_perm
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
    (physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply (List.perm_ext_iff_of_nodup
    (physical_actual_literal_raw_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_canonical_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)).mpr
  exact physical_actual_literal_target_order_membership
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralChronologicalG -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Recover EXACT group membership in a globally flattened dependent
Sigma-prime list. Cross-group labels cannot collide. -/
theorem physical_literal_sigma_flatten_mem_iff
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    (xs : (g : BG) → List (BP g)) (g : BG) (p : BP g) :
    (⟨g,p⟩ : PhysicalSourcePrime BP) ∈
      (Finset.univ.toList : List BG).flatMap (fun h =>
        (xs h).map (fun a => (⟨h,a⟩ : PhysicalSourcePrime BP))) ↔
    p ∈ xs g := by
  constructor
  · intro hp
    obtain ⟨h, _, ht⟩ := List.mem_flatMap.mp hp
    obtain ⟨a, ha, haEq⟩ := List.mem_map.mp ht
    have hgroup : h = g := congrArg Sigma.fst haEq
    subst h
    have heq : a = p := eq_of_heq (Sigma.mk.inj_iff.mp haEq).2
    exact heq ▸ ha
  · intro hp
    apply List.mem_flatMap.mpr
    refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), ?_⟩
    exact List.mem_map.mpr ⟨p,hp,rfl⟩

/-- On distinct prime labels, the original source OLD deletion by
INDEX is equivalent to removing precisely the selected prime
VALUES. This is not true without Nodup, so the hypothesis is kept. -/
theorem physical_literal_unselected_support_exact
    {P : Type} [DecidableEq P]
    (old : List P) (A : Finset (Fin old.length))
    (hN : old.Nodup) (p : P) :
    p ∈ (Finset.univ \ A).image old.get ↔
      p ∈ old.toFinset ∧ p ∉ A.image old.get := by
  constructor
  · intro hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp
    have hnot : j ∉ A := (Finset.mem_sdiff.mp hj).2
    constructor
    · exact List.mem_toFinset.mpr (hjp ▸ List.get_mem old j)
    · intro hpEnd
      obtain ⟨k,hk,hkp⟩ := Finset.mem_image.mp hpEnd
      have hEq : old.get j = old.get k := hjp.trans hkp.symm
      have hJ : j = k := (List.nodup_iff_injective_get.mp hN) hEq
      exact hnot (hJ ▸ hk)
  · rintro ⟨hpOld, hpNot⟩
    obtain ⟨j,hjp⟩ := List.mem_iff_get.mp
      (List.mem_toFinset.mp hpOld)
    have hjnot : j ∉ A := by
      intro hj
      exact hpNot (Finset.mem_image.mpr ⟨j,hj,hjp⟩)
    exact Finset.mem_image.mpr ⟨j,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩, hjp⟩

/-- Group Fock prime SUPPORT after indexed OLD deletion, with full
atom order retained. The uniqueness hypothesis applies to PRIME
labels, not to arbitrarily deduplicated old atoms. -/
theorem physical_literal_unselected_fock_support_exact
    {P : Type} [DecidableEq P] (modulus : P → ℕ)
    (old : List (Green64Fock.Atom P modulus))
    (A : Finset (Fin old.length))
    (hN : (old.map fun a => a.1).Nodup) (p : P) :
    p ∈ (Finset.univ \ A).image (fun j => (old.get j).1) ↔
      p ∈ (old.map fun a => a.1).toFinset ∧
      p ∉ A.image (fun j => (old.get j).1) := by
  constructor
  · intro hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp
    have hnot : j ∉ A := (Finset.mem_sdiff.mp hj).2
    constructor
    · exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨old.get j, List.get_mem old j, hjp⟩)
    · intro hpEnd
      obtain ⟨l,hl,hlp⟩ := Finset.mem_image.mp hpEnd
      have hElem : old.get j = old.get l := by
        apply List.inj_on_of_nodup_map hN
          (List.get_mem old j) (List.get_mem old l)
        exact hjp.trans hlp.symm
      have hJ : j = l :=
        (List.nodup_iff_injective_get.mp
          (List.Nodup.of_map (fun a => a.1) hN)) hElem
      exact hnot (hJ ▸ hl)
  · rintro ⟨hpOld,hnot⟩
    obtain ⟨a,ha,hap⟩ := List.mem_map.mp
      (List.mem_toFinset.mp hpOld)
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp ha
    have hjp : (old.get j).1 = p := by
      rw [hj]
      exact hap
    have hjnot : j ∉ A := by
      intro hjSel
      exact hnot (Finset.mem_image.mpr ⟨j,hjSel,hjp⟩)
    exact Finset.mem_image.mpr ⟨j,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hjnot⟩, hjp⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralChronologicalGSupport -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

theorem physical_actual_literal_G_local_support
    (i : ℕ) (hi : i ≤ N) (g : BG) (v : BP g) :
    v ∈ (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
       (fun a => a.1) ↔
    (v ∈ (Green64Fock.fockToList (((H.before i).2 g).2)).map
       (fun a => a.1) ∧
     v ∉ ((H.ghost i g).1.1).image
       (fun j => ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1)) ∨
     v ∈ (List.ofFn ((H.ghost i g).2.2)).map (fun a => a.1) := by
  let old := Green64Fock.fockToList (((H.before i).2 g).2)
  have hN := physical_actual_literal_before_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g
  have hG := actual_physical_path_big_G_value_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
  change ((Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)).toFinset =
      (Finset.univ \ ((H.ghost i g).1.1)).image
        (fun j => (old.get j).1) ∪
      (Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => ((H.ghost i g).2.2 j).1) at hG
  rw [← List.mem_toFinset, hG, Finset.mem_union,
    physical_literal_unselected_fock_support_exact
      (bigMod g) old ((H.ghost i g).1.1) hN v]
  simp [old, List.mem_map, List.mem_ofFn, Finset.mem_image]

theorem physical_actual_literal_before_group_mem
    (i : ℕ) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ (Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => a.1) := by
  let xs : (g : BG) → List (BP g) :=
    fun g => (Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => a.1)
  have h := physical_literal_sigma_flatten_mem_iff BP xs g v
  simpa only [physicalActualLiteralPendingBefore, xs, List.map_map,
    Function.comp_def] using h

theorem physical_actual_literal_afterG_group_mem
    (i : ℕ) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1) := by
  let xs : (g : BG) → List (BP g) :=
    fun g => (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)
  have h := physical_literal_sigma_flatten_mem_iff BP xs g v
  simpa only [physicalActualLiteralPendingAfterG, xs, List.map_map,
    Function.comp_def] using h

theorem physical_actual_literal_ghost_group_mem
    (i : ℕ) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ (List.ofFn ((H.ghost i g).2.2)).map (fun a => a.1) := by
  let xs : (g : BG) → List (BP g) :=
    fun g => (List.ofFn ((H.ghost i g).2.2)).map (fun a => a.1)
  have h := physical_literal_sigma_flatten_mem_iff BP xs g v
  change (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      (Finset.univ.toList : List BG).flatMap (fun z =>
        (List.ofFn ((H.ghost i z).2.2)).map
          (fun a => (⟨z,a.1⟩ : PhysicalSourcePrime BP))) ↔
      v ∈ (List.ofFn ((H.ghost i g).2.2)).map (fun a => a.1)
  simpa only [xs, List.map_map, Function.comp_def] using h

theorem physical_actual_literal_ended_group_mem
    (i : ℕ) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralEndedValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ ((H.ghost i g).1.1).image
      (fun j => ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1) := by
  constructor
  · intro hp
    obtain ⟨h, _, hh⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j,hj,hEq⟩ := Finset.mem_image.mp hh
    have hgroup : h = g := congrArg Sigma.fst hEq
    subst h
    have hpEq : ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1 = v :=
      eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
    exact Finset.mem_image.mpr ⟨j,hj,hpEq⟩
  · intro hp
    obtain ⟨j,hj,hEq⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr
      ⟨g, Finset.mem_univ g,
        Finset.mem_image.mpr ⟨j,hj,
          congrArg (fun z => (⟨g,z⟩ : PhysicalSourcePrime BP)) hEq⟩⟩

/-- Exact GLOBAL value-support bridge from actual G-output Fock
to literal OLD-term deletion plus the true ordered ghost batch. -/
theorem physical_actual_literal_G_global_support
    (i : ℕ) (hi : i ≤ N) (p : PhysicalSourcePrime BP) :
    p ∈ physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ↔
    (p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ∧
      p ∉ physicalActualLiteralEndedValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) ∨
    p ∈ physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  cases p with
  | mk g v =>
    rw [physical_actual_literal_afterG_group_mem,
      physical_actual_literal_before_group_mem,
      physical_actual_literal_ended_group_mem,
      physical_actual_literal_ghost_group_mem]
    exact physical_actual_literal_G_local_support
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g v

/-- Original chronological RowValid.pendingAfter LIST: first
all surviving OLD particles in their pre-G order, then every
fresh ghost in the original ordered global G batch. -/
noncomputable def physicalActualLiteralChronologicalAfterG (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (physicalActualLiteralPendingBefore SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i).filter
      (fun p => p ∉ physicalActualLiteralEndedValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) ++
  physicalActualLiteralGhostBatch SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i

/-- True G-output Fock values coincide with chronological
RowValid.ghost_operation values, WITHOUT asserting equal list order. -/
theorem physical_actual_literal_chrono_afterG_support
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  ext p
  rw [List.mem_toFinset, List.mem_toFinset]
  unfold physicalActualLiteralChronologicalAfterG
  simp only [List.mem_append, List.mem_filter]
  rw [physical_actual_literal_G_global_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi]
  simp

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralChronologicalPromotion -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

theorem physical_actual_literal_promoted_in_chrono_afterG
    (i : ℕ) (hi : i < N) :
    physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  rw [physical_actual_literal_chrono_afterG_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)]
  exact physical_actual_literal_promoted_in_afterG
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi hp

/-- Exact RowValid.promotionOld injection into the CHRONOLOGICAL
pendingAfter list, not merely into Fock afterG group order.
Its range is indexed by literal target-permutation slots. -/
noncomputable def physicalActualLiteralChronologicalPromotionOld
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) ↪
    Fin (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).length := by
  apply literalSelectedOldInjection _ _ _
    (physical_actual_literal_raw_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
  intro j
  have hj := (literal_indices_for_exact _ _ j.1).mp j.2
  have hp := physical_actual_literal_promoted_in_chrono_afterG
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi hj
  exact List.mem_toFinset.mp hp

/-- Exact original RowValid.promotion_matches at every indexed
target slot, with the literal chronological G pending list. -/
theorem physical_actual_literal_chronological_promotion_matches
    (i : ℕ) (hi : i < N)
    (j : physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).get j.1 =
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).get
      (physicalActualLiteralChronologicalPromotionOld SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i hi j) := by
  symm
  exact literal_selected_old_injection_matches _ _ _ _ _ _

/-- Literal RowValid.ghost_operation, with real OLD selection
and genuinely ordered G births; no multiset substitutions. -/
theorem physical_actual_literal_chronological_ghost_operation (i : ℕ) :
    physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).filter
        (fun p => p ∉ (physicalActualLiteralTermIndices SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).image
          (physicalActualLiteralPendingBefore SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i).get) ++
    physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  rw [physical_actual_literal_term_index_image]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralChronologicalNodup -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- A dependent Sigma-prime flattened list retains global Nodup
when each group list is Nodup: two different tags never coincide. -/
theorem physical_literal_sigma_flatten_nodup
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    (xs : (g : BG) → List (BP g))
    (hn : ∀ g, (xs g).Nodup) :
    ((Finset.univ.toList : List BG).flatMap (fun h =>
      (xs h).map (fun p => (⟨h,p⟩ : PhysicalSourcePrime BP)))).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro g hg
    apply List.Nodup.map (fun a b hab => by
      exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2)
    exact hn g
  · have hpw : List.Pairwise (fun g h : BG => g ≠ h)
        (Finset.univ.toList : List BG) :=
      List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList _)
    apply hpw.imp
    intro g h hne
    apply List.disjoint_left.mpr
    intro p hpG hpH
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hpG
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hpH
    exact hne (congrArg Sigma.fst (ha.trans hb.symm))

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

theorem physical_actual_literal_pending_before_nodup
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  let xs : (g : BG) → List (BP g) :=
    fun g => (Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => a.1)
  have h := physical_literal_sigma_flatten_nodup BP xs (fun g =>
    physical_actual_literal_before_pending_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g)
  simpa only [physicalActualLiteralPendingBefore, xs,
    List.map_map, Function.comp_def] using h

theorem physical_actual_literal_pending_afterG_nodup
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  let xs : (g : BG) → List (BP g) :=
    fun g => (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => a.1)
  have h := physical_literal_sigma_flatten_nodup BP xs (fun g =>
    physical_actual_literal_afterG_pending_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g)
  simpa only [physicalActualLiteralPendingAfterG, xs,
    List.map_map, Function.comp_def] using h

theorem physical_actual_literal_ghost_disjoint_pending
    (i : ℕ) (hi : i ≤ N) :
    List.Disjoint
      (physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply List.disjoint_left.mpr
  intro p hpBefore hpGhost
  cases p with
  | mk g v =>
    have hv := (physical_actual_literal_before_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g v).mp hpBefore
    have hGood := (physical_finite_actual_path_good_every_visit
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi) g
    have hSeen : bigMod g v ∈ H.seen i := by
      apply hGood.2.2.2.2
      rw [physicalProjectionPendingValues_exact]
      exact Multiset.mem_coe.mpr hv
    have hBorn :
        bigMod g v ∈
          (physicalGhostFreshBirths SP smallMod BP bigMod
            (J+ell) cap (H.before i) (H.ghost i)).toFinset := by
      apply List.mem_toFinset.mpr
      rw [← physical_actual_literal_ghost_numeric_order
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i]
      exact List.mem_map.mpr
        ⟨(⟨g,v⟩ : PhysicalSourcePrime BP), hpGhost,
          by rfl⟩
    exact (Finset.disjoint_left.mp (H.G_birth_eligible i hi).2
      hSeen) hBorn

theorem physical_actual_literal_chrono_afterG_nodup
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralChronologicalAfterG
  apply List.Nodup.append
  · exact (physical_actual_literal_pending_before_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi).filter _
  · exact physical_actual_literal_ghost_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · apply List.disjoint_left.mpr
    intro p hpOld hpGhost
    exact List.disjoint_left.mp
      (physical_actual_literal_ghost_disjoint_pending
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi)
      (List.mem_filter.mp hpOld).1 hpGhost

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralEGroupSupport -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Membership in the GLOBAL store tag set is exactly the original
group-local E store prime support, for every actual witness. -/
theorem physical_actual_literal_store_group_mem
    (i : ℕ) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralStoreValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ trueBigStoredValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
      (((H.edge i).2.2.1.bigChoice g).2) := by
  unfold physicalActualLiteralStoreValues trueBigStoredValues
  constructor
  · intro hp
    obtain ⟨⟨h,j⟩, hj, hpEq⟩ := Finset.mem_image.mp hp
    have hEq : h = g := congrArg Sigma.fst hpEq
    subst h
    have hv : ((H.beforeE i).2 g).1
        (((H.edge i).2.2.1.sigmaBig g) j) = v :=
      eq_of_heq (Sigma.mk.inj_iff.mp hpEq).2
    exact Finset.mem_image.mpr ⟨j,
      (Finset.mem_filter.mp hj).2, hv⟩
  · intro hp
    obtain ⟨j,hj,hv⟩ := Finset.mem_image.mp hp
    apply Finset.mem_image.mpr
    refine ⟨⟨g,j⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    · exact congrArg (fun a => (⟨g,a⟩ : PhysicalSourcePrime BP)) hv

/-- The corrected E edge's OLD promotion index maps to the actual
target slot, preserving the independent tau sampling. -/
theorem physical_actual_literal_promotion_group_mem
    (i : ℕ) (hi : i < N) (g : BG) (v : BP g) :
    (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPromotionValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ↔
    v ∈ trueBigPromotedValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g) (((H.edge i).2.2.1.bigChoice g).2) := by
  have hleg := (H.E_legal i hi).2.2.2.1 g
  unfold physicalActualLiteralPromotionValues trueBigPromotedValues
  constructor
  · intro hp
    obtain ⟨⟨h,j⟩,hj,hEq⟩ := Finset.mem_image.mp hp
    have hh : h = g := congrArg Sigma.fst hEq
    subst h
    have hv : (((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j)) = v :=
      eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
    have hjP := (Finset.mem_filter.mp hj).2
    exact Finset.mem_image.mpr
      ⟨⟨j,hjP⟩, Finset.mem_attach _ _, (hleg.promoted_matches ⟨j,hjP⟩).symm.trans hv⟩
  · intro hp
    obtain ⟨j,hj,hv⟩ := Finset.mem_image.mp hp
    apply Finset.mem_image.mpr
    refine ⟨⟨g,j.1⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.2⟩
    · change (⟨g, ((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j.1)⟩ :
          PhysicalSourcePrime BP) = ⟨g,v⟩
      exact congrArg (fun a => (⟨g,a⟩ : PhysicalSourcePrime BP))
        ((hleg.promoted_matches j).trans hv)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralENextSupport -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Exactly the original E_i pending update transported from
group Fock to the globally tagged literal prime support. -/
theorem physical_actual_literal_E_global_pending_support
    (i : ℕ) (hi : i < N) (p : PhysicalSourcePrime BP) :
    p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) ↔
    (p ∈ physicalActualLiteralPendingAfterG SP smallMod BP bigMod
         J ell m cap patterns q rho Vbig muBig k N H i ∧
     p ∉ physicalActualLiteralPromotionValues SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H i) ∨
    p ∈ physicalActualLiteralStoreValues SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H i := by
  cases p with
  | mk g v =>
    rw [physical_actual_literal_before_group_mem,
      physical_actual_literal_afterG_group_mem,
      physical_actual_literal_promotion_group_mem
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi g v,
      physical_actual_literal_store_group_mem]
    have hE := actual_physical_path_E_pending_difference
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g
    have hOrbit := actualPhysicalPendingSet_orbit_eq
      SP smallMod BP bigMod J ell cap
      (H.beforeE i) (H.afterG i) (H.E_orbit_input i hi) g
    rw [hOrbit] at hE
    have hiff : v ∈ actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.before (i+1)) g ↔
      (v ∈ actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.afterG i) g ∧
        v ∉ trueBigPromotedValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) (((H.edge i).2.2.1.bigChoice g).2)) ∨
        v ∈ trueBigStoredValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
          (((H.edge i).2.2.1.bigChoice g).2) := by
      rw [hE, Finset.mem_union, Finset.mem_sdiff]
    simpa only [actualPhysicalPendingSet, List.mem_toFinset] using hiff

/-- Literally ordered RowValid.pendingNext: survivors retain their
G-chronological order, newly stored active labels are selected by
the original SOURCE flattened endpoint indices. -/
noncomputable def physicalActualLiteralChronologicalNext (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i).filter
      (fun p => p ∉ physicalActualLiteralPromotionValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i) ++
  Green64Literal.pick
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (physicalActualLiteralStoreIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)

theorem physical_actual_literal_chrono_next_pending_operation (i : ℕ) :
    physicalActualLiteralChronologicalNext SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).filter
      (fun p => p ∉
        (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get) ++
    Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralStoreIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) := by
  rw [physical_actual_literal_promotion_index_image]
  rfl

/-- The chronological next-list is supported by PRECISELY the
actual E_i output Fock labels, no extra/disappearing primes. -/
theorem physical_actual_literal_chrono_next_support
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralChronologicalNext SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1)).toFinset := by
  ext p
  unfold physicalActualLiteralChronologicalNext
  simp only [List.mem_toFinset]
  simp only [List.mem_append, List.mem_filter, Green64Literal.pick_mem,
    decide_eq_true_eq]
  rw [physical_actual_literal_E_global_pending_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi p]
  have hAfter := congrArg (fun s : Finset (PhysicalSourcePrime BP) => p ∈ s)
    (physical_actual_literal_chrono_afterG_support
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi))
  simp only [List.mem_toFinset] at hAfter
  rw [← hAfter]
  rw [← physical_actual_literal_store_index_image]
  simp only [Finset.mem_image]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralChronologicalNextNodup -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)
/-- The real E_i stored source labels are active before E and
cannot appear in G_i output pending memory. No set-based
deduplication or equality of ordered Fock representatives. -/
theorem physical_actual_literal_stores_disjoint_chrono_afterG
    (i : ℕ) (hi : i < N) :
    Disjoint
      (physicalActualLiteralStoreValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  apply Finset.disjoint_left.mpr
  intro p hpStore hpAfter
  rw [physical_actual_literal_chrono_afterG_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)] at hpAfter
  cases p with
  | mk g v =>
    have hStored := (physical_actual_literal_store_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g v).mp hpStore
    have hActive := trueBigStoredValues_subset_active
      (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
      ((H.edge i).2.2.1.sigmaBig g)
      ((H.edge i).2.2.1.bigChoice g).2 hStored
    rcases Finset.mem_image.mp hActive with ⟨j, _, hj⟩
    have hAfterGood := actual_G_preserves_physical_good_orbit
      SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig (H.before i) (H.afterG i)
      (H.ghost i) (H.seen i)
      (physical_finite_actual_path_good_every_visit
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i (Nat.le_of_lt hi))
      (H.G_nonzero i (Nat.le_of_lt hi))
      (H.G_birth_eligible i (Nat.le_of_lt hi))
    have hEquiv := congrArg
      (fun y : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        ((y.2 g).1)) (H.E_orbit_input i hi)
    change ((H.beforeE i).2 g).1 =
      ((H.afterG i).2 g).1 at hEquiv
    have hPending : v ∈ physicalOutputPendingValues SP smallMod
      BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG i)) g := by
      rw [physicalProjectionPendingValues_exact]
      exact Multiset.mem_coe.mpr
        ((physical_actual_literal_afterG_group_mem
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H i g v).mp
          (List.mem_toFinset.mp hpAfter))
    have hNot := (hAfterGood g).2.2.1 j v hPending
    apply hNot
    change ((H.afterG i).2 g).1 j = v
    rw [← hEquiv]
    exact hj
/-- Chronological E-next uses literal concatenation without any
repeated prime; this proves a RowValid list, not merely set support. -/
theorem physical_actual_literal_chrono_next_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralChronologicalNext SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralChronologicalNext
  apply List.Nodup.append
  · exact (physical_actual_literal_chrono_afterG_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi)).filter _
  · unfold Green64Literal.pick
    apply List.Nodup.map
      (List.nodup_iff_injective_get.mp
        (physical_actual_literal_raw_source_nodup
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H i hi))
    exact Finset.nodup_toList _
  · apply List.disjoint_left.mpr
    intro p hpOld hpStore
    have hdis := physical_actual_literal_stores_disjoint_chrono_afterG
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
    have hStore : p ∈ physicalActualLiteralStoreValues SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i := by
      rw [← physical_actual_literal_store_index_image]
      rw [← Green64Literal.pick_toFinset]
      exact List.mem_toFinset.mpr hpStore
    exact Finset.disjoint_left.mp hdis hStore
      (List.mem_toFinset.mpr (List.mem_filter.mp hpOld).1)

end Green64FullPhysicalE

end

/-! ## PhysicalActualOrientedGEStepCoefficient -/

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

/-- Full ACTUAL source G_i E_i per-witness coefficient, with BOTH
independent BIG/SMALL endpoint permutation families; true source D
from permuted shared slots and free auxiliaries; old-zero G factors
and ghost batches; OLD promotions, fresh active mass, exact rho,
SMALL Haar, exactly one Kν D^(iζ) Fourier phase, and independent
Fock-ordered states. This is an equality of original coefficients,
not a guessed Markov transition or the final lifespan identity. -/
theorem physical_actual_oriented_GE_step_weight_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (i : ℕ) (hi : i < N) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig (H.before i) (H.afterG i) (H.ghost i) *
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
      (H.beforeE i) (H.edge i) =
    let z := H.edge i
    let pat := patterns z.1
    let aux := z.2.1
    let b := z.2.2.1
    let ss := z.2.2.2.1
    let tt := z.2.2.2.2
    let D := sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap pat aux (H.beforeE i) b.sigmaBig ss
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap pat aux (H.beforeE i) b.sigmaBig ss
      (physicalAlternatingSign i) k
    (∏ g : BG, physicalActualGhostFactor
      SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig (H.before i) (H.ghost i) g) *
    (sourceAuxMass BP bigMod J m Vbig pat aux : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass
      (G := SG) (J+ell) : ℂ) *
    (∏ g : BG, orientedBigBranchCoefficient
      (bigMod g) (J+ell) (cap g) (muBig g) (Vbig g) rho
      ((H.beforeE i).2 g) (b.bigChoice g).1
      (sourceBigShared J ell m pat g)
      (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) *
    Green64SmallHaar.groupPermutedKernel
      SP smallMod (J+ell) q Vsmall (sourceSmallShared J ell)
      step (fun _ _ => 1) ss tt (H.beforeE i).1 b.smallTarget *
    originalEdgeScalar
      (Knu z.1 aux
        (fun g j => ((H.beforeE i).2 g).1 (b.sigmaBig g j))
        (fun g j => (b.bigChoice g).1 (b.tauBig g j)))
      ((i : ℝ) * zeta) theta D (physicalAlternatingSign i) k := by
  have hG := physical_actual_G_full_scalar_exact
    SP smallMod BP bigMod J ell cap
    q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i (Nat.le_of_lt hi))
  have hE := physical_source_E_branch_phase_once
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig muBig Knu
    ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
    (H.beforeE i) (H.edge i)
  rw [hG, hE]
  dsimp only
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalActualTerminalGhostCoefficient -/

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

/-- At final G_N the actual physical vacuum forces EVERY OLD
zero-residue index to terminate and forbids ghost births.
Consequently the original raw G_N coefficient is exactly the
literal terminal factor (-eta_N/rho)^#pending, group by group.
No transition or terminal factor is postulated. -/
theorem physical_actual_terminal_G_vacuum_coefficient
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N N Vbig muBig
      (H.before N) (H.afterG N) (H.ghost N) =
    ∏ g : BG, (-(sourceVisitEta q N N : ℂ) / (rho : ℂ)) ^
      (Green64Fock.fockToList (((H.before N).2 g).2)).length := by
  rw [physical_actual_G_full_scalar_exact
    SP smallMod BP bigMod J ell cap
    q rho N N Vbig muBig
    (H.before N) (H.afterG N) (H.ghost N)
    (H.G_nonzero N (Nat.le_refl N))]
  apply Finset.prod_congr rfl
  intro g _
  have hlast := physical_actual_terminal_vacuum_excludes_ghost_births
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hVac g
  let old := Green64Fock.fockToList (((H.before N).2 g).2)
  have hsub :
    (H.ghost N g).1.1 ⊆
      Green64MemoryGhostOp.zeroOld old
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0) :=
    Finset.mem_powerset.mp (H.ghost N g).1.2
  have hzero :
      Green64MemoryGhostOp.zeroOld old
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    exact hsub (by simpa only [hlast.1] using (Finset.mem_univ j))
  have hprod :
      (∏ j : Fin ((H.ghost N g).2.1.val),
        (muBig g ((H.ghost N g).2.2 j).1 : ℂ)) = 1 := by
    have hempty :
        (Finset.univ : Finset (Fin ((H.ghost N g).2.1.val))) =
        ∅ := by
      ext j
      have hj : j.val < 0 := by simpa [hlast.2] using j.isLt
      omega
    rw [hempty]
    simp
  unfold physicalActualGhostFactor
  dsimp only
  simp [hlast.1, hlast.2, hzero, old]

end Green64FullPhysicalE

end

/-! ## PhysicalActualFullPathHilbertCoefficient -/

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

/-- The FULL product of actual original raw G/E witness coefficients
and TRUE Hilbert conditional-expectation factors along a physical
path: initial SMALL Haar/BIG active/Fock mass, intermediate
G-to-E and next-visit orbit masses, terminal G_N and global
source baseline. This is one explicit path summand, NOT a new operator.
The source path-sum equality is still a separate obligation. -/
noncomputable def physicalActualRawPathHilbertWeight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N) : ℂ :=
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
  (fullPhysicalMass SP smallMod BP bigMod
    (J+ell) cap Vsmall muBig (H.before 0) : ℂ) *
  (∏ i ∈ Finset.range N,
    (physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig
      (H.before i) (H.afterG i) (H.ghost i) *
     sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu ((i : ℝ) * zeta) theta
      (physicalAlternatingSign i) k (H.beforeE i) (H.edge i)) *
    ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
       Vsmall muBig (H.beforeE i) : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap
       Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.afterG i)) : ℂ)) *
    ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
       Vsmall muBig (H.before (i+1)) : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap
       Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.before (i+1))) : ℂ))) *
  physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
    q rho N N Vbig muBig
    (H.before N) (H.afterG N) (H.ghost N)

/-- Identical genuine raw witness factors, with both orbit-mass
ratios rewritten to ACTUAL ordered Fock fibre cardinalities and
terminal G_N rewritten to its true vacuum coefficient. -/
noncomputable def physicalActualFibrePathHilbertWeight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N) : ℂ :=
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
  (fullPhysicalMass SP smallMod BP bigMod
    (J+ell) cap Vsmall muBig (H.before 0) : ℂ) *
  (∏ i ∈ Finset.range N,
    (physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig
      (H.before i) (H.afterG i) (H.ghost i) *
     sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu ((i : ℝ) * zeta) theta
      (physicalAlternatingSign i) k (H.beforeE i) (H.edge i)) *
    (1 / ((actualPhysicalInputFibre SP smallMod BP bigMod
        (J+ell) cap
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.beforeE i))).card : ℂ)) *
    (1 / ((actualPhysicalInputFibre SP smallMod BP bigMod
        (J+ell) cap
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.before (i+1)))).card : ℂ))) *
  (∏ g : BG, (-(sourceVisitEta q N N : ℂ) / (rho : ℂ)) ^
      (Green64Fock.fockToList (((H.before N).2 g).2)).length)

end Green64FullPhysicalE

end

/-! ## PhysicalActualHilbertOrbitRatios -/

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

/-- The EXACT G_i-to-E_i Fock-orbit probability for the ORIGINAL
raw two-representative source witness: mass(beforeE)/mass(afterG
symmetric orbit) = 1/#true ordered input fibre. The intermediate
Fock permutation does not create a new factorial or probability
kernel. All repeated prime-residue atoms remain in the fibre. -/
theorem physical_actual_G_to_E_orbit_fibre_ratio
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) :
    ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
      Vsmall muBig (H.beforeE i) : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap
        Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.afterG i)) : ℂ)) =
    1 / ((actualPhysicalInputFibre SP smallMod BP bigMod
      (J+ell) cap (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.beforeE i))).card : ℂ) := by
  have hOrbit := congrArg
    (physicalOrbitMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig) (H.E_orbit_input i hi)
  rw [← hOrbit]
  simpa only using (physical_oriented_full_input_fibre_uniform_weight
    SP smallMod BP bigMod (J+ell) cap Vsmall muBig hV hmu
    (H.beforeE i))

end Green64FullPhysicalE

end

/-! ## PhysicalActualFullPathHilbertPushforward -/

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

/-- For EVERY genuine source-oriented physical path satisfying its
actual global-birth witness conditions, the complete raw G/E
Hilbert-weighted *path scalar* equals the explicit orbit-fibre
cardinality normalization and literal terminal G_N factor.
This retains the original b_p, small Haar and active/Fock masses.
The independent-residue literal-history correspondence is not
assumed or claimed here. -/
theorem physical_actual_full_path_Hilbert_fibre_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    physicalActualRawPathHilbertWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N H =
    physicalActualFibrePathHilbertWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N H := by
  unfold physicalActualRawPathHilbertWeight
    physicalActualFibrePathHilbertWeight
  rw [physical_actual_terminal_G_vacuum_coefficient
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hVac]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_actual_G_to_E_orbit_fibre_ratio
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig muBig hV hmu k N i H
    (Finset.mem_range.mp hi)]
  have hNext := physical_oriented_full_input_fibre_uniform_weight
    SP smallMod BP bigMod (J+ell) cap Vsmall muBig
    hV hmu (H.before (i+1))
  dsimp only at hNext
  rw [hNext]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralSourceRow -/

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
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)
/-- Original oriented E_i fresh target labels, not the complement
of a deduplicated endpoint set. Target tau remains independent. -/
noncomputable def physicalActualLiteralFreshTarget (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap (fun g =>
    (orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      (((H.edge i).2.2.1.bigChoice g).2.2.1)).toList.map
      (fun j => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g j))

/-- The independent original BIG auxiliary D draws can repeat and
are not treated as active or ghost births. -/
noncomputable def physicalActualLiteralAuxiliaryPrimes (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap (fun g =>
    (Finset.univ.toList :
      List (↥((patterns (H.edge i).1).free g))).map
        (fun j => (⟨g, (H.edge i).2.1 g j⟩ : PhysicalSourcePrime BP)))

/-- Source SMALL Haar shared primes in the real independent
SMALL sigma frame. There are no SMALL auxiliary free draws. -/
noncomputable def physicalActualLiteralSmallSharedPrimes (i : ℕ) :
    List ℕ :=
  (Finset.univ.toList : List SG).flatMap (fun g =>
    (sourceSmallShared J ell g).toList.map (fun j =>
      smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell)
        ((H.beforeE i).1 g) ((H.edge i).2.2.2.1 g j))))

/-- Precisely the first-birth active labels F_i of the original
chronological source witness, not all currently active labels. -/
noncomputable def physicalActualLiteralFreshBefore (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap (fun g =>
    (physicalGroupFreshVisit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g i).toList.map
        (fun v => (⟨g,v⟩ : PhysicalSourcePrime BP)))
/-- The true birth-history U_i is indexed by tagged original
BIG primes. No replacement of the numerical seen-birth rule. -/
noncomputable def physicalActualLiteralEverBornBefore (i : ℕ) :
    Finset (PhysicalSourcePrime BP) :=
  Finset.univ.filter (fun p =>
    p.2 ∈ physicalGroupPastVisit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H p.1 i)

/-- Membership in an actual ordered Fock memory determines the
physical residue; outside that memory the independent original
anchor a_p is retained, never silently set to zero. -/
noncomputable def physicalActualLiteralAnchoredResidue
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (p : PhysicalSourcePrime BP) :
    ZMod (physicalSourcePrimeValue BP bigMod p) :=
  if p.2 ∈ (Green64Fock.fockToList (((x.2 p.1).2))).map
      (fun a => a.1) then
    physicalLiteralFockResidue BP bigMod cap SP smallMod x p
  else
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H anchor i p.1 p.2

/-- Real signed source divisor, including SMALL sigma, BIG sigma,
shared coordinates and every independent auxiliary prime draw. -/
noncomputable def physicalActualLiteralDivisor (i : ℕ) : ℕ :=
  sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
    (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1
/-- Real source row at i < N. No fabricated transition predicate:
all lists are true physical witness frames or explicit original
chronological normalizations, and all scalar weights are source
expressions. This definition by itself does not certify RowValid. -/
noncomputable def physicalActualLiteralSourceRow
    (Vsmall : SG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP)
      BG (fun _ => J+ell) where
  value := physicalSourcePrimeValue BP bigMod
  labelGroup := physicalSourcePrimeGroup BP
  activeSlots := actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  nextSlots := actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  sourcePerm := fun g => ((H.edge i).2.2.1.sigmaBig g).symm
  targetPerm := fun g => ((H.edge i).2.2.1.tauBig g).symm
  active := physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  nextActive := physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  sourceEndpoint := physicalActualLiteralRawSourceList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  targetEndpoint := physicalActualLiteralRawTargetList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  pendingBefore := physicalActualLiteralPendingBefore SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  pendingAfter := physicalActualLiteralChronologicalAfterG SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  pendingNext := physicalActualLiteralChronologicalNext SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  ghostBatch := physicalActualLiteralGhostBatch SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  ghostBatches := physicalActualLiteralGhostGroup SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  patternShared := sourceBigShared J ell m (patterns (H.edge i).1)
  freshTarget := physicalActualLiteralFreshTarget SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  termIndices := physicalActualLiteralTermIndices SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  sharedIndices := physicalActualLiteralSharedIndices SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  storeIndices := physicalActualLiteralStoreIndices SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  promotionSlots := physicalActualLiteralPromotionIndices SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  promotionOld := physicalActualLiteralChronologicalPromotionOld SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i hi
  auxiliaryPrimes := physicalActualLiteralAuxiliaryPrimes SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  smallSharedPrimes := physicalActualLiteralSmallSharedPrimes SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  smallAuxiliaryPrimes := []
  everBornBefore := physicalActualLiteralEverBornBefore SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  everBornAfter :=
    (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ∪
      (physicalActualLiteralFreshBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset) ∪
      (physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset
  freshBefore := physicalActualLiteralFreshBefore SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  residueBefore := physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H anchor i (H.before i)
  residueAfter := physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H anchor i (H.afterG i)
  residueNext := physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H anchor (i+1) (H.before (i+1))
  offsetBefore := physicalActualOffset SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  offsetAfter := physicalActualOffset SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H (i+1)
  k := k
  orientation := physicalAlternatingSign i
  divisorD := physicalActualLiteralDivisor SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  theta := theta
  zeta := (i : ℝ) * zeta
  kernelK := Knu (H.edge i).1 (H.edge i).2.1
    (fun g j => ((H.beforeE i).2 g).1 ((H.edge i).2.2.1.sigmaBig g j))
    (fun g j => ((H.edge i).2.2.1.bigChoice g).1
      ((H.edge i).2.2.1.tauBig g j))
  rho := rho
  q := q
  eta := sourceVisitEta q N i
  groupV := Vbig
  baseline := fun p => physicalSourceBaseline BP bigMod q N p.1 p.2
  auxiliaryMeasure := fun p =>
    1 / (Vbig p.1 * (bigMod p.1 p.2 : ℝ))
  smallFactor := Green64SmallHaar.groupPermutedKernel
    SP smallMod (J+ell) q Vsmall (sourceSmallShared J ell)
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (fun _ _ => (1:ℂ)) (H.edge i).2.2.2.1
    (H.edge i).2.2.2.2 (H.beforeE i).1
    ((H.edge i).2.2.1.smallTarget)

end Green64FullPhysicalE

end

