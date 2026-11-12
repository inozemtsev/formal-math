module

public import Green64.Library.Correlation.MemoryFullChainRhoInvariant

@[expose] public section

/-!
# Correlation / MemoryBirthParityGauge

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryBirthParityGauge -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Parity of the actual chronological numerical birth set. This is an
observable on history, not an assertion about arithmetic endpoint parity. -/
def sourceOriginalMemorySeenParity434 (seen : Finset ℕ) : ℂ :=
  (-1 : ℂ)^seen.card

private theorem neg_one_pow_square434 (n : ℕ) :
    (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by
  rw [← mul_pow]
  norm_num

/-- The exact parity increment under the ORIGINAL chronological birth rule. -/
theorem source_original_memory_SEEN_birth_parity434
    (seen : Finset ℕ) (births : List ℕ) (hn : births.Nodup)
    (hd : Disjoint seen births.toFinset) :
    sourceOriginalMemorySeenParity434 seen *
      sourceOriginalMemorySeenParity434 (seen ∪ births.toFinset) =
    (-1 : ℂ)^births.length := by
  have hc : (seen ∪ births.toFinset).card = seen.card + births.length := by
    rw [Finset.card_union_of_disjoint hd, List.toFinset_card_of_nodup hn]
  unfold sourceOriginalMemorySeenParity434
  rw [hc, pow_add, ← mul_assoc, neg_one_pow_square434, one_mul]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact conjugation of the full ORIGINAL E by the true history parity.
Every source coefficient is unchanged on the left. On the right each real
branch receives (-1)^(number of fresh target births), including DIRTY
branches with their actual promotion-dependent fresh set. -/
theorem source_original_memory_E_BIRTH_PARITY_conjugation434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemorySeenParity434 seen *
      physicalOrientedBirthMarkedE SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu K zeta theta o k x seen
        (fun y nextSeen => sourceOriginalMemorySeenParity434 nextSeen * F y nextSeen) =
    ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
        J ell m cap patterns x o k,
      if orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns seen z then
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu K zeta theta o k x z *
        ((-1 : ℂ)^(orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns z).length *
        F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns x o k z)
          (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod
            J ell m cap patterns z).toFinset))
      else 0 := by
  unfold physicalOrientedBirthMarkedE
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns seen z
  · simp only [if_pos h]
    have hp := source_original_memory_SEEN_birth_parity434 seen
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) h.1 h.2
    calc
      _ = sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu K zeta theta o k x z *
        ((sourceOriginalMemorySeenParity434 seen *
          sourceOriginalMemorySeenParity434 (seen ∪ (orientedEFreshBirths
            SP smallMod BP bigMod J ell m cap patterns z).toFinset)) *
          F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z)
            (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset)) := by ring
      _ = _ := by rw [hp]
  · simp only [if_neg h, mul_zero]

/-- The number of original ghost births is the sum of the real per-group
batch sizes. Neither deletions nor OLD continuations are births. -/
theorem source_original_memory_G_birth_length434
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) :
    (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x c).length =
      ∑ g : BG, (c g).2.1.val := by
  simp [physicalGhostFreshBirths, List.length_flatMap]

/-- The SAME history conjugation necessarily changes G as well: every
actual b-birth witness receives (-1)^b. The genuine 1/b!, OLD subset,
source eta/q/rho/V coefficients and chronological marker remain explicit. -/
theorem source_original_memory_G_BIRTH_PARITY_conjugation434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemorySeenParity434 seen *
      physicalGBirthMarkedRow SP smallMod BP bigMod (J+ell) cap
        q rho N i Vb mu x seen
        (fun y nextSeen => sourceOriginalMemorySeenParity434 nextSeen * F y nextSeen) =
    ∑ y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      ∑ c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x,
        if physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap x seen c then
          physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
            q rho N i Vb mu x y c *
          ((-1 : ℂ)^(∑ g : BG, (c g).2.1.val) *
          F (physicalFockProjection SP smallMod BP bigMod (J+ell) cap y)
            (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x c).toFinset))
        else 0 := by
  unfold physicalGBirthMarkedRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap x seen c
  · simp only [if_pos h]
    have hp := source_original_memory_SEEN_birth_parity434 seen
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x c) h.1 h.2
    rw [source_original_memory_G_birth_length434 SP smallMod BP bigMod J ell cap x c] at hp
    calc
      _ = physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vb mu x y c *
        ((sourceOriginalMemorySeenParity434 seen * sourceOriginalMemorySeenParity434
          (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x c).toFinset)) *
        F (physicalFockProjection SP smallMod BP bigMod (J+ell) cap y)
          (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x c).toFinset)) := by ring
      _ = _ := by rw [hp]
  · simp only [if_neg h, mul_zero]

/-- On an actual CLEAN branch, fresh births and copied shared marks partition
all target BIG slots. This is derived from the original source choice, not
from a replacement independent history parameter. -/
theorem source_original_memory_CLEAN_birth_shared_complement434
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hc : memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z) :
    (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length +
      (∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card) =
    (J+ell) * Fintype.card BG := by
  have hlen : (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length =
      ∑ g : BG, (orientedFresh (J+ell) (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1)).card := by
    simp [orientedEFreshBirths, List.length_flatMap]
  rw [hlen, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _g : BG, (J+ell) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [(hc g).2]
      simp only [orientedFresh, orientedUnshared, Finset.sdiff_empty]
      simpa using (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (sourceBigShared J ell m (patterns z.1) g)))
    _ = _ := by simp [Nat.mul_comm]

/-- Exact source realization of the shared-parity counterweight on CLEAN:
it is a fixed global sign times the ACTUAL seen-parity boundary ratio.
This does NOT identify the boundary observable with arithmetic epsilon(n).
Together with G_BIRTH_PARITY_conjugation it records the unavoidable ghost
birth modification if this conjugation is used on the original evolution. -/
theorem source_original_memory_CLEAN_shared_counterweight_as_seen_boundary434
    (rSmall : ℕ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (seen : Finset ℕ)
    (hc : memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z)
    (hb : orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns seen z) :
    (-1 : ℂ)^(rSmall + ∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card) =
    (-1 : ℂ)^(rSmall + (J+ell)*Fintype.card BG) *
      (sourceOriginalMemorySeenParity434 seen * sourceOriginalMemorySeenParity434
        (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset)) := by
  rw [source_original_memory_SEEN_birth_parity434 seen
    (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) hb.1 hb.2]
  have hcomp := source_original_memory_CLEAN_birth_shared_complement434
    SP smallMod BP bigMod J ell m cap patterns x z hc
  let b := (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length
  let s := ∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card
  have hs : rSmall + (J+ell)*Fintype.card BG = (rSmall+s)+b := by
    dsimp only [s,b]
    omega
  change (-1 : ℂ)^(rSmall+s) =
    (-1 : ℂ)^(rSmall+(J+ell)*Fintype.card BG) * (-1 : ℂ)^b
  rw [hs, pow_add (-1 : ℂ) (rSmall+s) b, mul_assoc,
    neg_one_pow_square434 b, mul_one]

/-- For EVERY legal original E branch, including DIRTY, the target slots
are partitioned into copied shared marks, promoted OLD marks and fresh
births. The correction outside CLEAN therefore has a real promotion term. -/
theorem source_original_memory_LEGAL_birth_promotion_shared_partition434
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hz : z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x o k) :
    (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length +
      (∑ g : BG, ((z.2.2.1.bigChoice g).2.2.1).card) +
      (∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card) =
    (J+ell) * Fintype.card BG := by
  have hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x o k z := (Finset.mem_filter.mp hz).2
  have hlen : (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length =
      ∑ g : BG, (orientedFresh (J+ell) (sourceBigShared J ell m (patterns z.1) g)
        ((z.2.2.1.bigChoice g).2.2.1)).card := by
    simp [orientedEFreshBirths, List.length_flatMap]
  rw [hlen, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _g : BG, (J+ell) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hp := (hl.2.2.2.1 g).promotes_unshared
      have ha := Finset.card_sdiff_add_card_eq_card hp
      have hb := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (sourceBigShared J ell m (patterns z.1) g))
      simp only [Finset.card_univ, Fintype.card_fin] at hb
      change (orientedUnshared (J+ell) (sourceBigShared J ell m (patterns z.1) g) \
          ((z.2.2.1.bigChoice g).2.2.1)).card + _ + _ = _
      rw [ha]
      exact hb
    _ = _ := by simp [Nat.mul_comm]

/-- Exact all-four-channel counterweight on the ORIGINAL legal birth carrier.
In mixed channels it equals the fixed total-slot sign, the actual seen
boundary ratio, AND the actual OLD-promotion parity. It is not permissible
to insert only the CLEAN counterweight while leaving G/DIRTY/endpoints
unchanged. No assertion that the boundary ratio is arithmetic epsilon is made. -/
theorem source_original_memory_FOUR_CHANNEL_counterweight_full_history434
    (rSmall : ℕ) (bS bT : Bool)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (seen : Finset ℕ)
    (hz : z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns x o k)
    (hb : orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns seen z) :
    (if bS = bT then (1 : ℂ) else
      (-1 : ℂ)^(rSmall + ∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card)) =
    (if bS = bT then (1 : ℂ) else (-1 : ℂ)^(rSmall+(J+ell)*Fintype.card BG)) *
    (if bS = bT then (1 : ℂ) else
      sourceOriginalMemorySeenParity434 seen * sourceOriginalMemorySeenParity434
        (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset)) *
    (if bS = bT then (1 : ℂ) else
      (-1 : ℂ)^(∑ g : BG, ((z.2.2.1.bigChoice g).2.2.1).card)) := by
  by_cases he : bS = bT
  · simp only [if_pos he, one_mul]
  · simp only [if_neg he]
    rw [source_original_memory_SEEN_birth_parity434 seen
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z) hb.1 hb.2]
    have hp := source_original_memory_LEGAL_birth_promotion_shared_partition434
      SP smallMod BP bigMod J ell m cap patterns x o k z hz
    let b := (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).length
    let p := ∑ g : BG, ((z.2.2.1.bigChoice g).2.2.1).card
    let s := ∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card
    have ht : rSmall+(J+ell)*Fintype.card BG = (rSmall+s)+b+p := by
      dsimp only [b,p,s]
      omega
    change (-1 : ℂ)^(rSmall+s) =
      ((-1 : ℂ)^(rSmall+(J+ell)*Fintype.card BG) * (-1 : ℂ)^b) * (-1 : ℂ)^p
    rw [ht, pow_add (-1 : ℂ) ((rSmall+s)+b) p,
      pow_add (-1 : ℂ) (rSmall+s) b]
    symm
    calc
      _ = (-1 : ℂ)^(rSmall+s) * ((-1 : ℂ)^b * (-1 : ℂ)^b) *
        ((-1 : ℂ)^p * (-1 : ℂ)^p) := by ring
      _ = _ := by rw [neg_one_pow_square434 b, neg_one_pow_square434 p]; ring

private theorem seen_parity_square434 (seen : Finset ℕ) :
    sourceOriginalMemorySeenParity434 seen * sourceOriginalMemorySeenParity434 seen = 1 :=
  neg_one_pow_square434 seen.card

/-- The precisely CONJUGATED source evolution. This is deliberately named as
a transformed expression, not silently substituted for memorySourceGEChain.
The local E/G theorems above identify its coefficients: true fresh-birth signs
on E and true ghost-batch signs on G. The original fixed zeta, reverse-K
schedule and actual chronological birth filter are retained. -/
def sourceOriginalMemoryBirthParityChain434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
  | 0, start, F => fun y seen =>
      sourceOriginalMemorySeenParity434 seen *
      physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
        q rho N start Vs Vb mu y seen
        (fun z nextSeen => sourceOriginalMemorySeenParity434 nextSeen * F z nextSeen)
  | n+1, start, F => fun y seen =>
      sourceOriginalMemorySeenParity434 seen *
      physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
        q rho N start Vs Vb mu y seen
        (fun yg seenG => sourceOriginalMemorySeenParity434 seenG *
          (sourceOriginalMemorySeenParity434 seenG *
            physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
              J ell m cap patterns q rho Vs Vb mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k yg seenG
              (fun z nextSeen => sourceOriginalMemorySeenParity434 nextSeen *
                sourceOriginalMemoryBirthParityChain434 q rho Vs Vb mu K
                  zeta theta k N n (start+1) F z nextSeen)))

/-- Exact cancellation of INTERNAL seen-parities through the WHOLE genuine
G/E chain. The initial and terminal history factors remain. This is the
reviewable boundary cost of the proposed birth-parity counterweight. -/
theorem source_original_memory_FULL_BIRTH_PARITY_CHAIN_boundary434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N n start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryBirthParityChain434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta k N n start F y seen =
    sourceOriginalMemorySeenParity434 seen *
      memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
        q rho Vs Vb mu K zeta theta k N n start
        (fun z nextSeen => sourceOriginalMemorySeenParity434 nextSeen * F z nextSeen) y seen := by
  induction n generalizing start y seen with
  | zero => rfl
  | succ n ih =>
      simp only [sourceOriginalMemoryBirthParityChain434, memorySourceGEChain]
      simp_rw [ih]
      simp only [← mul_assoc, seen_parity_square434, one_mul]

private theorem initial_seen_parity434
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (hy : (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup) :
    sourceOriginalMemorySeenParity434
      (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset =
    (-1 : ℂ)^((J+ell)*Fintype.card BG) := by
  unfold sourceOriginalMemorySeenParity434
  rw [List.toFinset_card_of_nodup hy]
  congr 1
  simp [physicalOutputInitialBirths, List.length_flatMap, Nat.mul_comm]

/-- EXACT transformed vacuum-root pairing. The initial birth parity is the
known total active-slot sign, but the terminal parity of ALL actual births
stays INSIDE the original chain. The ordinary source root has terminal
observable vacuum alone; equality to it is NOT asserted or assumed. -/
theorem source_original_memory_BIRTH_PARITY_ROOT_terminal_observable434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    let N := 2*R
    let mu := physicalSourceMuTilde BP bigMod q N Vb
    (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
      (∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y : ℂ) *
        star (physicalVacuum SP smallMod BP bigMod J ell y) *
        (if (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup then
          sourceOriginalMemoryBirthParityChain434 SP smallMod BP bigMod
            J ell m cap patterns q rho Vs Vb mu K zeta theta k N N 0
            (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out)
            y (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
        else 0)) =
    (-1 : ℂ)^((J+ell)*Fintype.card BG) *
      ((physicalSourceBaselineProduct BP bigMod q N : ℂ) *
      (∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y : ℂ) *
        star (physicalVacuum SP smallMod BP bigMod J ell y) *
        (if (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup then
          memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
            q rho Vs Vb mu K zeta theta k N N 0
            (fun out finalSeen => sourceOriginalMemorySeenParity434 finalSeen *
              physicalVacuum SP smallMod BP bigMod J ell out)
            y (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
        else 0))) := by
  dsimp only
  rw [mul_left_comm ((-1 : ℂ)^((J+ell)*Fintype.card BG))
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup
  · simp only [if_pos hn]
    rw [source_original_memory_FULL_BIRTH_PARITY_CHAIN_boundary434,
      initial_seen_parity434 SP smallMod BP bigMod J ell y hn]
    ring
  · simp only [if_neg hn, mul_zero]
end Green64FullPhysicalE

end

end

