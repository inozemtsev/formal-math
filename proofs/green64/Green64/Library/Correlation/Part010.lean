module

public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part009
public import Green64.Library.Weights.Part005
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

/-!
# Correlation / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalRootInitialDisintegration -/

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

/-- Exact pushforward from actual ordered pending-particle Fock
representatives with their 1/j! mass to symmetric multisets.
Repeated atoms are retained, and no hypothetical measure is added. -/
theorem physicalOrbitMass_global_pushforward
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (phi : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    (∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod
        (J + ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig y : ℂ) * phi y) =
    ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
      (fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) *
      phi (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x) := by
  classical
  rw [Green64Fock.finite_sum_by_image
    (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
    (physicalFockProjection SP smallMod BP bigMod
      (J + ell) cap)
    (fun x => (fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) *
      phi (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x))]
  apply Finset.sum_congr rfl
  intro y hy
  rw [show
    (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ) =
    ∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap)) with
        physicalFockProjection SP smallMod BP bigMod (J + ell) cap x = y,
      (fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) from by
          simp [physicalOrbitMass]]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootInitialSum -/

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

/-- Push the REPAIRED 1/j! finite Hilbert vacuum mass to RAW
physical initial representatives. The initial global birth test
is preserved exactly: initial ordered active prime lists, not
auxiliary D draws or memory atoms, define the initial seen-set. -/
theorem physicalOrientedFiniteMarkedRoot_initial_state_sum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig
      Knu zeta theta k R =
    let N := 2 * R
    let mu := physicalSourceMuTilde BP bigMod q N Vbig
    (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
      ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
        (fullPhysicalMass SP smallMod BP bigMod
          (J + ell) cap Vsmall mu x : ℂ) *
        star (physicalVacuum SP smallMod BP bigMod J ell
          (physicalFockProjection SP smallMod BP bigMod
            (J + ell) cap x)) *
        (if (physicalInitialBirths SP smallMod BP bigMod
             J ell cap x).Nodup then
          physicalOrientedMarkedGEChain SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig mu
            Knu zeta theta k N N 0
            (fun out _seen =>
              physicalVacuum SP smallMod BP bigMod J ell out)
            (physicalFockProjection SP smallMod BP bigMod
              (J + ell) cap x)
            (physicalInitialBirths SP smallMod BP bigMod
              J ell cap x).toFinset
         else 0) := by
  classical
  unfold physicalOrientedFiniteMarkedRoot
  dsimp only
  simp only [mul_assoc]
  rw [physicalOrbitMass_global_pushforward
    SP smallMod BP bigMod J ell cap Vsmall
    (physicalSourceMuTilde BP bigMod q (2 * R) Vbig)
    (fun y =>
      star (physicalVacuum SP smallMod BP bigMod J ell y) *
        (if (physicalOutputInitialBirths SP smallMod BP bigMod
             J ell y).Nodup then
           physicalOrientedMarkedGEChain SP smallMod BP bigMod
             J ell m cap patterns q rho Vsmall Vbig
             (physicalSourceMuTilde BP bigMod q (2 * R) Vbig)
             Knu zeta theta k (2 * R) (2 * R) 0
             (fun out _seen =>
               physicalVacuum SP smallMod BP bigMod J ell out)
             y (physicalOutputInitialBirths SP smallMod BP bigMod
               J ell y).toFinset
         else 0))]
  simp only [physicalOutputInitialBirths_source_exact]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullRawRoot -/

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

/-- Complete finite PERMUTATION-CORRECT ORIGINAL PHYSICAL witness root product:
b_p baseline, true µtilde active/Fock masses including 1/j!,
Haar, every source ν and free D choice, both endpoint
permutation families, real OLD/store/fresh G/E witnesses,
and exactly the chronological global distinct-birth filter.
This proves source-operator-to-physical-witness counting at
finite cutoff, not the remaining lifespan weighted pushforward. -/
theorem physicalOrientedFiniteMarkedRoot_eq_rawWitnessRoot
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig
      Knu zeta theta k R =
    let N := 2 * R
    let mu := physicalSourceMuTilde BP bigMod q N Vbig
    (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
      ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
        (fullPhysicalMass SP smallMod BP bigMod
          (J + ell) cap Vsmall mu x : ℂ) *
        star (physicalVacuum SP smallMod BP bigMod J ell
          (physicalFockProjection SP smallMod BP bigMod
            (J + ell) cap x)) *
        (if (physicalInitialBirths SP smallMod BP bigMod
             J ell cap x).Nodup then
          physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig mu
            Knu zeta theta k N N 0
            (fun out _seen =>
              physicalVacuum SP smallMod BP bigMod J ell out)
            (physicalFockProjection SP smallMod BP bigMod
              (J + ell) cap x)
            (physicalInitialBirths SP smallMod BP bigMod
              J ell cap x).toFinset
         else 0) := by
  rw [physicalOrientedFiniteMarkedRoot_initial_state_sum]
  dsimp only
  simp only [physicalOrientedMarkedGEChain_eq_raw]

end Green64FullPhysicalE

end

/-! ## PhysicalLifespanSourceWeight -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]

/-- The original BIG active/Fock one-prime birth density, in complex
coefficients, is exactly the first-live-birth factor appearing in
the checked generic lifespan weight theorem. -/
theorem physicalMuTilde_cast_source
    (q : ℝ) (N : ℕ) (Vbig : BG → ℝ) (g : BG) (p : BP g) :
    (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ) =
      1 / ((Vbig g : ℂ) * (bigMod g p : ℂ) *
        (physicalSourceBaseline BP bigMod q N g p : ℂ)) := by
  simp [physicalSourceMuTilde]

/-- For a literal one-prime lifespan the ACTUAL source mu-tilde
birth measure, promotion charges and split G/E rho factors combine
to exactly one 1/(p b_p) and one 1/V per active run. The q_i and
eta_i here are the physical source visit coefficients, including
the two sqrt(q) boundary visits. This is a concrete parameter
instantiation of the independently kernel-checked row-weight proof,
not a proof that every G/E path admits such a lifespan. -/
theorem physical_lifespan_weight_from_source
    (q rho : ℝ) (N a z : ℕ)
    (Vbig : BG → ℝ) (g : BG) (p : BP g)
    (A hit : ℕ → Prop) [DecidablePred A] [DecidablePred hit]
    (haz : a ≤ z) (hz : z ≤ N)
    (hactive : ∀ i, A i → a ≤ i ∧ i ≤ z)
    (hsingle : a = z → A a)
    (hha : hit a) (hhz : hit z)
    (hrho : rho ≠ 0) (hV : Vbig g ≠ 0)
    (hb : physicalSourceBaseline BP bigMod q N g p ≠ 0) :
    let V : ℂ := Vbig g
    let rhoC : ℂ := rho
    let pC : ℂ := bigMod g p
    let b : ℂ := physicalSourceBaseline BP bigMod q N g p
    let qAt (i : ℕ) : ℂ := sourceVisitQ q N i
    let etaAt (i : ℕ) : ℂ := sourceVisitEta q N i
    let runs := (Finset.range (N+1)).filter
      (fun i => A i ∧ (i = 0 ∨ ¬ A (i-1)))
    let promotions := (Finset.range (N+1)).filter
      (fun i => A i ∧ 0 < i ∧ a ≤ i-1 ∧ i-1 < z ∧ ¬ A (i-1))
    let localRow (i : ℕ) :=
      (if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i then rhoC else 1) *
      (if (z = i ∧ ¬ A i) ∧ hit i then -etaAt i / rhoC
       else if (a < i ∧ i ≤ z ∧ ¬ A i) ∧ hit i
         then qAt i / rhoC^2 else 1) *
      (if (a = i ∧ ¬ A i) ∧ hit i then -etaAt i * V / rhoC else 1) *
      (if (a ≤ i ∧ i < z ∧ ¬ A i) ∧ hit i then rhoC else 1)
    (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ) *
      (1 / V)^promotions.card *
      (∏ i ∈ Finset.range (N+1), localRow i) =
    (1/V)^runs.card / (pC*b) *
      (if A a then 1 else -etaAt a) *
      (if A z then 1 else -etaAt z) *
      (∏ i ∈ Finset.range (N+1),
        if (a < i ∧ i < z ∧ ¬ A i) ∧ hit i then qAt i else 1) := by
  dsimp only
  rw [physicalMuTilde_cast_source]
  have hR : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho
  have hV' : (Vbig g : ℂ) ≠ 0 := by exact_mod_cast hV
  have hp : (bigMod g p : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (bigMod g p))
  have hb' : (physicalSourceBaseline BP bigMod q N g p : ℂ) ≠ 0 := by
    exact_mod_cast hb
  exact Green64MemoryJoin.lifespan_row_weight N a z A hit
    (rho : ℂ) (Vbig g : ℂ) (bigMod g p : ℂ)
    (physicalSourceBaseline BP bigMod q N g p : ℂ)
    (fun i => (sourceVisitQ q N i : ℂ))
    (fun i => (sourceVisitEta q N i : ℂ))
    haz hz hactive hsingle hha hhz hR hV' hp hb'

end Green64FullPhysicalE

end

/-! ## PhysicalBaselinePositivity -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]

/-- The exact ORIGINAL visit discount 1-q_i belongs to [0,1]
at boundary sqrt(q) and every interior visit, including N=0. -/
theorem source_eta_nonneg_le_one
    (q : ℝ) (N i : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ sourceVisitEta q N i ∧ sourceVisitEta q N i ≤ 1 := by
  unfold sourceVisitEta sourceVisitQ
  split_ifs
  · have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    have hs1 : Real.sqrt q ≤ 1 := by
      simpa using (Real.sqrt_le_sqrt hq1)
    constructor <;> linarith
  · constructor <;> linarith

/-- The baseline b_p is genuinely positive when the numerical
big prime exceeds the count of N+1 source visits. -/
theorem physicalSourceBaseline_positive_above_visits
    (q : ℝ) (N : ℕ) (g : BG) (p : BP g)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp : N + 1 < bigMod g p) :
    0 < physicalSourceBaseline BP bigMod q N g p := by
  have hs :
      (∑ i ∈ Finset.range (N + 1), sourceVisitEta q N i) ≤
      (N + 1 : ℝ) := by
    calc
      (∑ i ∈ Finset.range (N + 1), sourceVisitEta q N i) ≤
          ∑ i ∈ Finset.range (N + 1), (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact (source_eta_nonneg_le_one q N i hq0 hq1).2
      _ = (N + 1 : ℝ) := by simp
  have hpn : (0 : ℝ) < (bigMod g p : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hlt : (∑ i ∈ Finset.range (N + 1), sourceVisitEta q N i) <
      (bigMod g p : ℝ) :=
    lt_of_le_of_lt hs (by exact_mod_cast hp)
  have hd :
      (∑ i ∈ Finset.range (N + 1), sourceVisitEta q N i) /
      (bigMod g p : ℝ) < 1 :=
    (div_lt_iff₀ hpn).2 (by simpa using hlt)
  unfold physicalSourceBaseline
  linarith

/-- Physically normalized µ-tilde has strictly positive mass
under the source big-prime condition, not a formal placeholder
for a nonnegative Markov measure. -/
theorem physicalSourceMuTilde_pos_above_visits
    (q : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (g : BG) (p : BP g)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hV : 0 < Vbig g)
    (hp : N + 1 < bigMod g p) :
    0 < physicalSourceMuTilde BP bigMod q N Vbig g p := by
  unfold physicalSourceMuTilde
  have hb := physicalSourceBaseline_positive_above_visits
    BP bigMod q N g p hq0 hq1 hp
  have hp0 : (0 : ℝ) < (bigMod g p : ℝ) :=
    by exact_mod_cast (Nat.zero_lt_of_lt hp)
  positivity

end Green64FullPhysicalE

end

/-! ## MemoryFrozenBigExpansion -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Both active and orphan sectors use the same finite lifespan carrier.
The first/last active visits are derived from the original finite set. -/
def memoryFrozenPrimeTerm (p : ℕ) (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ) :
    MemoryLifespanChoice n → ℝ :=
  if hA : A.Nonempty then
    memoryRepresentedTerm p eta h A n (A.min' hA) (A.max' hA)
  else memoryAbsentTerm p eta h n

theorem memory_frozen_prime_all_lifespans
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ)
    (hA : A ⊆ Finset.range n) :
    memoryPrimeHaar p eta h A n =
      ∑ l : MemoryLifespanChoice n, memoryFrozenPrimeTerm p eta h A n l := by
  by_cases hn : A.Nonempty
  · simp only [memoryFrozenPrimeTerm, dif_pos hn]
    exact memory_represented_all_lifespans p eta h A n
      (A.min' hn) (A.max' hn) (A.min'_le_max' hn)
      (Finset.mem_range.mp (hA (A.max'_mem hn)))
      (A.min'_mem hn) (A.max'_mem hn)
      (fun t ht => ⟨A.min'_le t ht, A.le_max' t ht⟩)
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst A
    simp only [memoryFrozenPrimeTerm, dif_neg (Finset.not_nonempty_empty)]
    exact memory_absent_all_lifespans p eta h n

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- Full independent product-Haar factor, for fixed original active labels
and signed integer offsets. All numerical primes receive their own anchor,
including those absent from every active list. -/
def memoryFrozenHaarExpectation (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (A : P → Finset ℕ) (n : ℕ) : ℝ :=
  (∑ c : (p : P) → ZMod (modulus p),
    ∏ p : P,
      if ∀ i ∈ A p, (offset i : ZMod (modulus p)) = c p then
        ∏ t ∈ Finset.range n,
          if t ∈ A p then 1 else
            1 - eta t *
              (if (offset t : ZMod (modulus p)) = c p then (1 : ℝ) else 0)
      else 0) / (∏ p : P, (modulus p : ℝ))

/-- Haar disintegration is an equality of finite sums, not independence
assumed for offsets or labels. The fixed offsets may have any collisions. -/
theorem memory_frozen_Haar_product (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (A : P → Finset ℕ) (n : ℕ) :
    memoryFrozenHaarExpectation modulus eta offset A n =
      ∏ p : P, memoryPrimeHaar (modulus p) eta
        (fun i => (offset i : ZMod (modulus p))) (A p) n := by
  unfold memoryFrozenHaarExpectation memoryPrimeHaar
  rw [Finset.prod_div_distrib]
  congr 1
  exact (Fintype.prod_sum (fun p (c : ZMod (modulus p)) =>
    if ∀ i ∈ A p, (offset i : ZMod (modulus p)) = c then
      ∏ t ∈ Finset.range n,
        if t ∈ A p then (1 : ℝ) else 1-eta t *
          (if (offset t : ZMod (modulus p)) = c then (1 : ℝ) else 0)
    else 0)).symm

/-- Complete global frozen BIG prime expansion. Each function assigns at
most one lifespan per numerical prime label. Neither multiplicity nor
surjectivity of a physical root map is a premise. -/
theorem memory_frozen_Haar_all_lifespans (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (A : P → Finset ℕ) (n : ℕ)
    (hA : ∀ p, A p ⊆ Finset.range n) :
    memoryFrozenHaarExpectation modulus eta offset A n =
      ∑ life : P → MemoryLifespanChoice n,
        ∏ p : P, memoryFrozenPrimeTerm (modulus p) eta
          (fun i => (offset i : ZMod (modulus p))) (A p) n (life p) := by
  rw [memory_frozen_Haar_product]
  calc
    _ = ∏ p : P, ∑ l : MemoryLifespanChoice n,
        memoryFrozenPrimeTerm (modulus p) eta
          (fun i => (offset i : ZMod (modulus p))) (A p) n l := by
      apply Finset.prod_congr rfl
      intro p hp
      exact memory_frozen_prime_all_lifespans (modulus p) eta
        (fun i => (offset i : ZMod (modulus p))) (A p) n (hA p)
    _ = _ := Fintype.prod_sum _

/-- Original single extracted baseline and every baseline-relative lifespan
cost. Nonzero b is required only to divide; source positivity is instantiated
below from q and the actual BIG prime range. -/
theorem memory_frozen_Haar_baseline_factored (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (A : P → Finset ℕ) (n : ℕ)
    (hA : ∀ p, A p ⊆ Finset.range n)
    (b : P → ℝ) (hb : ∀ p, b p ≠ 0) :
    memoryFrozenHaarExpectation modulus eta offset A n =
      (∏ p : P, b p) *
      (∑ life : P → MemoryLifespanChoice n,
        ∏ p : P,
          memoryFrozenPrimeTerm (modulus p) eta
            (fun i => (offset i : ZMod (modulus p))) (A p) n (life p) / b p) := by
  rw [memory_frozen_Haar_all_lifespans modulus eta offset A n hA]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro life hlife
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  field_simp [hb p]

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

local instance memory_source_prime_nezero (p : PhysicalSourcePrime BP) :
    NeZero (physicalSourcePrimeValue BP bigMod p) :=
  inferInstanceAs (NeZero (bigMod p.1 p.2))

/-- Actual original active-prime visits from the ordered labels.
It ignores every Fock/store/ghost choice: there is none in this input. -/
def memoryFrozenActiveVisits (M N : ℕ)
    (marks : ℕ → (g : BG) → Fin M → BP g)
    (p : PhysicalSourcePrime BP) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun i => ∃ j : Fin M, marks i p.1 j = p.2)

/-- Source-specialized whole BIG independent residue factor after all
active lists and signed displacements are frozen. This is the original
b_p product and the full finite lifespan/orphan sum, not a per-witness
scalar equality. -/
theorem memory_source_frozen_BIG_expansion
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M N : ℕ) (marks : ℕ → (g : BG) → Fin M → BP g)
    (offset : ℕ → ℤ)
    (hlarge : ∀ g p, N+1 < bigMod g p) :
    memoryFrozenHaarExpectation (physicalSourcePrimeValue BP bigMod)
      (sourceVisitEta q N) offset (memoryFrozenActiveVisits BP M N marks) (N+1) =
    physicalSourceBaselineProduct BP bigMod q N *
      (∑ life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1),
        ∏ p : PhysicalSourcePrime BP,
          memoryFrozenPrimeTerm (bigMod p.1 p.2) (sourceVisitEta q N)
            (fun i => (offset i : ZMod (bigMod p.1 p.2)))
            (memoryFrozenActiveVisits BP M N marks p) (N+1) (life p) /
          physicalSourceBaseline BP bigMod q N p.1 p.2) := by
  have hA (p : PhysicalSourcePrime BP) :
      memoryFrozenActiveVisits BP M N marks p ⊆ Finset.range (N+1) :=
    Finset.filter_subset _ _
  have hb (p : PhysicalSourcePrime BP) :
      physicalSourceBaseline BP bigMod q N p.1 p.2 ≠ 0 :=
    ne_of_gt (physicalSourceBaseline_positive_above_visits
      BP bigMod q N p.1 p.2 hq0 hq1 (hlarge p.1 p.2))
  have hh := memory_frozen_Haar_baseline_factored
    (physicalSourcePrimeValue BP bigMod) (sourceVisitEta q N) offset
    (memoryFrozenActiveVisits BP M N marks) (N+1) hA
    (fun p => physicalSourceBaseline BP bigMod q N p.1 p.2) hb
  have hbase : (∏ p : PhysicalSourcePrime BP,
      physicalSourceBaseline BP bigMod q N p.1 p.2) =
      physicalSourceBaselineProduct BP bigMod q N := by
    rw [Fintype.prod_sigma]
    rfl
  rw [hbase] at hh
  exact hh
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGHaarDenominator -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- An ORIGINAL single BIG group's full independent numerical prime
residue torus has EXACT cardinality ∏_{p in BP(g)} p.
No moduli are dropped for inactive or orphan primes. -/
theorem memory_ind_BIG_group_torus_card (g : BG) :
    Fintype.card (Green64SmallHaar.SmallTorus (bigMod g)) =
      ∏ p : BP g, bigMod g p := by
  unfold Green64SmallHaar.SmallTorus
  rw [Fintype.card_pi]
  simp only [ZMod.card]

/-- Full ORIGINAL BIG product torus cardinality is the product of
every actual BIG numerical prime modulus (including inactive labels).
This is the explicit divisor/anchor denominator of the frozen
`memoryFrozenHaarExpectation`, not an assumed independent product. -/
theorem memory_ind_BIG_full_torus_card :
    Fintype.card (MemoryIndependentBIGTorus BP bigMod) =
    ∏ gp : PhysicalSourcePrime BP, bigMod gp.1 gp.2 := by
  calc
    Fintype.card (MemoryIndependentBIGTorus BP bigMod) =
      ∏ g : BG, Fintype.card (Green64SmallHaar.SmallTorus (bigMod g)) := by
        exact Fintype.card_pi
    _ = ∏ g : BG, ∏ p : BP g, bigMod g p := by
      apply Finset.prod_congr rfl
      intro g hg
      exact memory_ind_BIG_group_torus_card BP bigMod g
    _ = _ := (Fintype.prod_sigma
      (fun gp : PhysicalSourcePrime BP => bigMod gp.1 gp.2)).symm

/-- The product of ORIGINAL BIG group Haar atom masses is EXACTLY
1/(∏_{g,p} p), the denominator in the UNMODIFIED frozen source BIG
Haar expectation. No extra 1/p, 1/phi(p), or Fock factorial. -/
theorem memory_ind_BIG_Haar_mass_exact :
    (∏ g : BG,
      (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)) =
    (1 : ℂ) /
      (∏ gp : PhysicalSourcePrime BP, (bigMod gp.1 gp.2 : ℂ)) := by
  have hcard : (∏ g : BG,
      (Fintype.card (Green64SmallHaar.SmallTorus (bigMod g)) : ℂ)) =
      (∏ gp : PhysicalSourcePrime BP, (bigMod gp.1 gp.2 : ℂ)) := by
    simp_rw [memory_ind_BIG_group_torus_card BP bigMod]
    simp only [Nat.cast_prod]
    exact (Fintype.prod_sigma
      (fun gp : PhysicalSourcePrime BP => (bigMod gp.1 gp.2 : ℂ))).symm
  calc
    _ = (∏ g : BG,
        (1 : ℂ) /
          (Fintype.card (Green64SmallHaar.SmallTorus (bigMod g)) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro g hg
        simp [Green64SmallHaar.haarAtomMass]
    _ = (1 : ℂ) / ∏ g : BG,
        (Fintype.card (Green64SmallHaar.SmallTorus (bigMod g)) : ℂ) := by
        rw [Finset.prod_div_distrib]
        simp
    _ = _ := by rw [hcard]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGFrozenAnchor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Original independent BIG Haar anchor convention: the actual
initial BIG residue C_0 is the NEGATIVE of source frozen anchor h_p.
This is essential because physical residues evolve by +Δ while
frozen source checks offset_i = h_p at active zero positions. -/
def memoryIndBIGFrozenAnchor
    (c : MemoryIndependentBIGTorus BP bigMod) :
    MemoryIndependentBIGTorus BP bigMod :=
  fun g p => -(c g p)

/-- Source BIG anchor sign change is a BIJECTION of the full
product torus, not a change of the original Haar law. -/
def memoryIndBIGFrozenAnchorEquiv :
    MemoryIndependentBIGTorus BP bigMod ≃
    MemoryIndependentBIGTorus BP bigMod where
  toFun := memoryIndBIGFrozenAnchor BP bigMod
  invFun := memoryIndBIGFrozenAnchor BP bigMod
  left_inv := by
    intro c
    funext g p
    simp [memoryIndBIGFrozenAnchor]
  right_inv := by
    intro c
    funext g p
    simp [memoryIndBIGFrozenAnchor]

/-- TRUE physical zero at any BIG prime coordinate after integer
displacement Δ is EXACTLY the ORIGINAL frozen source condition
Δ ≡ h_p (mod p) with h_p = -initial_residue_p.
It is not the opposite sign; that would change original hitting
probabilities and silently break the rooted memory identity. -/
theorem memory_ind_BIG_zero_iff_frozen_anchor
    (c : MemoryIndependentBIGTorus BP bigMod)
    (delta : ℤ) (g : BG) (p : BP g) :
    (memoryIndBIGTorusTranslate BP bigMod delta c g p = 0) ↔
    ((delta : ZMod (bigMod g p)) =
      memoryIndBIGFrozenAnchor BP bigMod c g p) := by
  change (c g p + (delta : ZMod (bigMod g p)) = 0) ↔
    ((delta : ZMod (bigMod g p)) = -(c g p))
  constructor
  · intro h
    have hh : (delta : ZMod (bigMod g p)) + c g p = 0 := by
      simpa only [add_comm] using h
    exact eq_neg_of_add_eq_zero_left hh
  · intro h
    rw [h]
    exact add_neg_cancel _
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGHaarAnchorNumerator -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- TRUE full BIG torus Haar anchor reflection, with no lost or new
numerical prime coordinate. Inverting every coordinate changes the
Haar summation variable bijectively, not the Haar distribution. -/
theorem memory_ind_BIG_Haar_anchor_neg_sum (F : MemoryIndependentBIGTorus BP bigMod → ℝ) :
    (∑ c : MemoryIndependentBIGTorus BP bigMod,
      F (memoryIndBIGFrozenAnchor BP bigMod c)) =
    (∑ h : MemoryIndependentBIGTorus BP bigMod, F h) := by
  exact Equiv.sum_comp (memoryIndBIGFrozenAnchorEquiv BP bigMod) F

/-- Literal source prime-zero condition at a physical BIG residue
after integer offset, as read directly from original source BIG
group permuted kernels. No independent residue is resampled at
each visit: a single initial BIG Haar torus c is transported. -/
def memoryIndBIGPhysicalAnchorIntegrand
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ)
    (n : ℕ) (c : MemoryIndependentBIGTorus BP bigMod) : ℝ :=
  ∏ gp : PhysicalSourcePrime BP,
    if ∀ i ∈ A gp,
      c gp.1 gp.2 + (offset i : ZMod (bigMod gp.1 gp.2)) = 0
    then ∏ t ∈ Finset.range n,
      if t ∈ A gp then 1 else
        1-eta t *
          (if c gp.1 gp.2 + (offset t : ZMod (bigMod gp.1 gp.2))=0
           then (1:ℝ) else 0)
    else 0

/-- Literal original frozen source BIG Haar integrand, not a new
probability kernel. This is the exact numerator of the unchanged
memoryFrozenHaarExpectation, before dividing by ∏_{g,p}p. -/
def memoryIndBIGFrozenOriginalIntegrand
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ)
    (n : ℕ) (h : MemoryIndependentBIGTorus BP bigMod) : ℝ :=
  ∏ gp : PhysicalSourcePrime BP,
    if ∀ i ∈ A gp,
      (offset i : ZMod (bigMod gp.1 gp.2)) = h gp.1 gp.2
    then ∏ t ∈ Finset.range n,
      if t ∈ A gp then 1 else
        1-eta t *
          (if (offset t : ZMod (bigMod gp.1 gp.2)) = h gp.1 gp.2
           then (1:ℝ) else 0)
    else 0

/-- Source-LITERAL physical zero-coordinate BIG clock integrand is
pointwise EXACTLY the unchanged frozen BIG integrand at h=-c.
The sign is essential: physical c_i=c_0+offset_i, so actual zero
is offset_i=-c_0. This proof does not assume primewise independent
clocks, active mark multiplicities or a Haar sampling law. -/
theorem memory_ind_BIG_anchor_integrand_exact
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ)
    (n : ℕ) (c : MemoryIndependentBIGTorus BP bigMod) :
    memoryIndBIGPhysicalAnchorIntegrand BP bigMod eta offset A n c =
    memoryIndBIGFrozenOriginalIntegrand BP bigMod eta offset A n
      (memoryIndBIGFrozenAnchor BP bigMod c) := by
  unfold memoryIndBIGPhysicalAnchorIntegrand
    memoryIndBIGFrozenOriginalIntegrand
  apply Finset.prod_congr rfl
  intro gp hgp
  have heq (t : ℕ) :
      (c gp.1 gp.2 + (offset t : ZMod (bigMod gp.1 gp.2)) = 0) ↔
      ((offset t : ZMod (bigMod gp.1 gp.2)) =
        memoryIndBIGFrozenAnchor BP bigMod c gp.1 gp.2) :=
    memory_ind_BIG_zero_iff_frozen_anchor BP bigMod c (offset t) gp.1 gp.2
  have hA :
      (∀ i ∈ A gp,
        c gp.1 gp.2 + (offset i : ZMod (bigMod gp.1 gp.2))=0) ↔
      (∀ i ∈ A gp,
        (offset i : ZMod (bigMod gp.1 gp.2)) =
          memoryIndBIGFrozenAnchor BP bigMod c gp.1 gp.2) := by
    simp only [heq]
  by_cases ha : ∀ i ∈ A gp,
      c gp.1 gp.2 + (offset i : ZMod (bigMod gp.1 gp.2)) = 0
  · have hb := hA.mp ha
    rw [if_pos ha, if_pos hb]
    apply Finset.prod_congr rfl
    intro t ht
    by_cases hact : t ∈ A gp
    · simp only [hact,if_true]
    · simp only [hact,if_false]
      rw [if_congr (heq t) rfl rfl]
  · have hb : ¬ (∀ i ∈ A gp,
        (offset i : ZMod (bigMod gp.1 gp.2)) =
          memoryIndBIGFrozenAnchor BP bigMod c gp.1 gp.2) :=
      fun hh => ha (hA.mpr hh)
    simp only [ha,hb,if_false]

/-- EXACT full BIG-Haar change of variables to the ORIGINAL frozen
numerator, for any genuine finite original active visits/offsets.
No mark factorial, missing prime denominator or changed original
eta/offset. The V mark normalization is disintegrated separately. -/
theorem memory_ind_BIG_Haar_physical_numerator_eq_frozen
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ) (n : ℕ) :
    (∑ c : MemoryIndependentBIGTorus BP bigMod,
      memoryIndBIGPhysicalAnchorIntegrand BP bigMod eta offset A n c) =
    (∑ h : MemoryIndependentBIGTorus BP bigMod,
      memoryIndBIGFrozenOriginalIntegrand BP bigMod eta offset A n h) := by
  have hh := memory_ind_BIG_Haar_anchor_neg_sum BP bigMod
    (memoryIndBIGFrozenOriginalIntegrand BP bigMod eta offset A n)
  calc
    _ = (∑ c : MemoryIndependentBIGTorus BP bigMod,
        memoryIndBIGFrozenOriginalIntegrand BP bigMod eta offset A n
          (memoryIndBIGFrozenAnchor BP bigMod c)) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact memory_ind_BIG_anchor_integrand_exact BP bigMod eta offset A n c
    _ = _ := hh
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGPiSigmaAnchor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- EXACT reindexing between the ORIGINAL independent BIG
group-by-prime residue torus and the unchanged frozen source
single-index full prime torus. Every original prime coordinate
is preserved, with no active-subset projection or quotient. -/
def memoryIndBIGGroupPrimeSigmaEquiv :
    MemoryIndependentBIGTorus BP bigMod ≃
      ((gp : PhysicalSourcePrime BP) → ZMod (bigMod gp.1 gp.2)) where
  toFun c := fun gp => c gp.1 gp.2
  invFun h := fun g p => h ⟨g,p⟩
  left_inv := by
    intro c
    funext g p
    rfl
  right_inv := by
    intro h
    funext gp
    cases gp
    rfl

/-- The unchanged source full-prime torus has exactly the same
cardinality as the independent product-of-group torus. Its Haar
numerator can therefore be reindexed without factors. -/
theorem memory_ind_BIG_group_prime_sigma_card :
    Fintype.card (MemoryIndependentBIGTorus BP bigMod) =
      Fintype.card
        ((gp : PhysicalSourcePrime BP) → ZMod (bigMod gp.1 gp.2)) := by
  exact Fintype.card_congr (memoryIndBIGGroupPrimeSigmaEquiv BP bigMod)

/-- Source EXACT full-residue finite Haar sum can be reindexed
between independent BIG group torus and unchanged source Sigma-prime
Haar coordinates, without any extra prime/Haar normalization. -/
theorem memory_ind_BIG_group_prime_sigma_sum
    (F : ((gp : PhysicalSourcePrime BP) →
      ZMod (bigMod gp.1 gp.2)) → ℝ) :
    (∑ c : MemoryIndependentBIGTorus BP bigMod,
      F (memoryIndBIGGroupPrimeSigmaEquiv BP bigMod c)) =
    ∑ h : (gp : PhysicalSourcePrime BP) → ZMod (bigMod gp.1 gp.2), F h := by
  exact Equiv.sum_comp (memoryIndBIGGroupPrimeSigmaEquiv BP bigMod) F
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGHaarSourceExpectation -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

local instance (gp : PhysicalSourcePrime BP) :
    NeZero (physicalSourcePrimeValue BP bigMod gp) :=
  inferInstanceAs (NeZero (bigMod gp.1 gp.2))

/-- The TRUE physical independent BIG Haar expectation for fixed
original omega marks and signed integer offsets, as the uniform
finite sum over the complete original group-by-prime torus C_0.
The indicators check the ACTUAL physical zero coordinates at
C_0+offset_t; no Markov or prime independence is assumed. -/
def memoryIndBIGPhysicalHaarExpectation
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ) (n : ℕ) : ℝ :=
  (∑ c : MemoryIndependentBIGTorus BP bigMod,
    memoryIndBIGPhysicalAnchorIntegrand BP bigMod eta offset A n c) /
  (∏ gp : PhysicalSourcePrime BP, (bigMod gp.1 gp.2 : ℝ))

/-- Source-exact reindexing of the ORIGINAL frozen numerator from
group-by-prime Haar C_0 to source Sigma-prime Haar h_p. All original
Nu/aux/endpoint perms belong to the frozen path weight and remain
outside this integration, so no implicit expectation of these
choices is introduced here. -/
theorem memory_ind_BIG_original_integrand_sigma_sum
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ) (n : ℕ) :
    (∑ c : MemoryIndependentBIGTorus BP bigMod,
      memoryIndBIGFrozenOriginalIntegrand BP bigMod eta offset A n c) =
    (∑ h : (gp : PhysicalSourcePrime BP) →
          ZMod (bigMod gp.1 gp.2),
      ∏ gp : PhysicalSourcePrime BP,
        if ∀ i ∈ A gp,
          (offset i : ZMod (bigMod gp.1 gp.2)) = h gp
        then ∏ t ∈ Finset.range n,
          if t ∈ A gp then 1 else
            1-eta t *
              (if (offset t : ZMod (bigMod gp.1 gp.2))=h gp
               then (1:ℝ) else 0)
        else 0) := by
  let F : ((gp : PhysicalSourcePrime BP) →
        ZMod (bigMod gp.1 gp.2)) → ℝ := fun h =>
    ∏ gp : PhysicalSourcePrime BP,
      if ∀ i ∈ A gp,
        (offset i : ZMod (bigMod gp.1 gp.2))=h gp
      then ∏ t ∈ Finset.range n,
        if t ∈ A gp then 1 else
          1-eta t *
            (if (offset t : ZMod (bigMod gp.1 gp.2))=h gp
             then (1:ℝ) else 0)
      else 0
  have hr := memory_ind_BIG_group_prime_sigma_sum BP bigMod F
  change (∑ c : MemoryIndependentBIGTorus BP bigMod,
    F (memoryIndBIGGroupPrimeSigmaEquiv BP bigMod c)) =
    ∑ h, F h
  exact hr

/-- EXACT Haar normalization bridge for fixed original ω:
integrate a SINGLE physical initial BIG torus C_0 and its actual
translated-zero mark predicates. This equals the unchanged source
memoryFrozenHaarExpectation, with the TRUE product denominator
1/∏_{g,p}p and source convention h=-C_0.
This is an equality of literal sums, not a new sampled kernel. -/
theorem memory_ind_BIG_physical_anchor_eq_original_frozen_Haar
    (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (A : PhysicalSourcePrime BP → Finset ℕ) (n : ℕ) :
    memoryIndBIGPhysicalHaarExpectation BP bigMod eta offset A n =
    memoryFrozenHaarExpectation (physicalSourcePrimeValue BP bigMod)
      eta offset A n := by
  unfold memoryIndBIGPhysicalHaarExpectation
  unfold memoryFrozenHaarExpectation
  rw [memory_ind_BIG_Haar_physical_numerator_eq_frozen BP bigMod]
  rw [memory_ind_BIG_original_integrand_sigma_sum BP bigMod]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryLifespanSupport -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Support of the represented-prime source lifespan term. It is derived
from nonzero coefficients, not inserted as a new history assumption. -/
theorem memory_represented_nonzero_interval_support
    (p : ℕ) (eta : ℕ → ℝ) (h : ℕ → ZMod p)
    (A : Finset ℕ) (n a z : ℕ) (ji : Fin n × Fin n)
    (haz : a ≤ z) (ha : a ∈ A) (hz : z ∈ A)
    (hbound : ∀ t ∈ A, a ≤ t ∧ t ≤ z)
    (hn : memoryRepresentedTerm p eta h A n a z (some ji) ≠ 0) :
    ji.1.val ≤ a ∧ z ≤ ji.2.val ∧
    (∀ t ∈ A, h t = h ji.1.val) ∧
    h ji.2.val = h ji.1.val ∧
    (ji.1.val = ji.2.val → ji.1.val ∈ A) ∧
    (ji.1.val < a → eta ji.1.val ≠ 0) ∧
    (z < ji.2.val → eta ji.2.val ≠ 0) := by
  simp only [memoryRepresentedTerm] at hn
  split_ifs at hn with hc
  · have hleft : memoryPrefixChoice
        (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) a ji.1.val ≠ 0 := by
      intro he
      rw [he] at hn
      simp at hn
    have hright : memorySuffixChoice
        (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) z ji.2.val ≠ 0 := by
      intro he
      rw [he] at hn
      simp at hn
    have hzle : z ≤ ji.2.val := by
      by_contra hnot
      have hne : ji.2.val ≠ z := by omega
      have hnlt : ¬ z < ji.2.val := by omega
      simp [memorySuffixChoice, hne, hnlt] at hright
    have hhitLeft : h ji.1.val = h a := by
      by_cases he : ji.1.val = a
      · simpa [he]
      · have hh : ji.1.val < a := by omega
        by_contra hmiss
        simp [memoryPrefixChoice, he, hmiss] at hleft
    have hhitRight : h ji.2.val = h a := by
      by_cases he : ji.2.val = z
      · rw [he]
        exact hc.1 z hz
      · have hh : z < ji.2.val := by omega
        by_contra hmiss
        simp [memorySuffixChoice, he, hh, hmiss] at hright
    refine ⟨hc.2, hzle, ?_, hhitRight.trans hhitLeft.symm, ?_, ?_, ?_⟩
    · intro t ht
      exact (hc.1 t ht).trans hhitLeft.symm
    · intro he
      have hj : ji.1.val = a := by omega
      simpa [hj] using ha
    · intro hj he
      have hja : ji.1.val ≠ a := by omega
      simp [memoryPrefixChoice, hja, he] at hleft
    · intro hi he
      have hiz : ji.2.val ≠ z := by omega
      simp [memorySuffixChoice, hiz, hi, he] at hright
  · exact False.elim (hn rfl)

theorem memory_orphan_nonzero_interval_support
    (p : ℕ) (eta : ℕ → ℝ) {n : ℕ}
    (h : ℕ → ZMod p) (ji : Fin n × Fin n)
    (hn : memoryOrphanInterval p eta h ji ≠ 0) :
    ji.1.val < ji.2.val ∧ h ji.2.val = h ji.1.val ∧
      eta ji.1.val ≠ 0 ∧ eta ji.2.val ≠ 0 := by
  unfold memoryOrphanInterval at hn
  split_ifs at hn with hlt hhit
  · refine ⟨hlt, hhit, ?_, ?_⟩
    · intro he
      rw [he] at hn
      simp at hn
    · intro he
      rw [he] at hn
      simp at hn
  · simp at hn
  · exact False.elim (hn rfl)
end Green64FullPhysicalE

end

end

/-! ## MemoryIdentityTarget -/

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
/-- PINNED UNPROVED TERMINAL PROPOSITION: finite, saturated form of
source lem:memory-identity (02-transference.tex 523-535).
This is a Prop definition, not a theorem, axiom or proof certificate.
The unrestricted symmetric-Hilbert identity additionally requires the
cutoff-independence/absolute-convergence bridge. -/
def MemoryIdentityTarget
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : Prop :=
  MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R →
    memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R =
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig Knu zeta theta k R
end Green64FullPhysicalE

end

end

/-! ## MemoryCanonicalPrimeSchedule -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Exact support used only after deriving it from the actual frozen coefficient.
No reconstruction or counting hypothesis is included. -/
def MemoryFrozenScheduleSupport (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} : MemoryLifespanChoice n → Prop
  | none => A = ∅
  | some ji => ji.1.val ≤ ji.2.val ∧
      (∀ t ∈ A, ji.1.val ≤ t ∧ t ≤ ji.2.val ∧ h t = h ji.1.val) ∧
      h ji.2.val = h ji.1.val ∧
      (ji.1.val = ji.2.val → ji.1.val ∈ A)

theorem memory_frozen_nonzero_schedule_support
    (p : ℕ) (eta : ℕ → ℝ) (h : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ)
    (l : MemoryLifespanChoice n)
    (hn : memoryFrozenPrimeTerm p eta h A n l ≠ 0) :
    MemoryFrozenScheduleSupport p h A l := by
  by_cases hA : A.Nonempty
  · have ht : memoryRepresentedTerm p eta h A n (A.min' hA) (A.max' hA) l ≠ 0 := by
      simpa only [memoryFrozenPrimeTerm, dif_pos hA] using hn
    cases l with
    | none => simp [memoryRepresentedTerm] at ht
    | some ji =>
      have hs := memory_represented_nonzero_interval_support p eta h A n
        (A.min' hA) (A.max' hA) ji (A.min'_le_max' hA)
        (A.min'_mem hA) (A.max'_mem hA)
        (fun t ht => ⟨A.min'_le t ht, A.le_max' t ht⟩) ht
      have hja := hs.1
      have hzd := hs.2.1
      have haz := A.min'_le_max' hA
      refine ⟨by omega, ?_, hs.2.2.2.1, hs.2.2.2.2.1⟩
      intro t ht
      have hmin := A.min'_le t ht
      have hmax := A.le_max' t ht
      exact ⟨by omega, by omega, hs.2.2.1 t ht⟩
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    cases l with
    | none => exact he
    | some ji =>
      have ht : memoryOrphanInterval p eta h ji ≠ 0 := by
        simpa only [memoryFrozenPrimeTerm, dif_neg hA, memoryAbsentTerm] using hn
      have hs := memory_orphan_nonzero_interval_support p eta h ji ht
      refine ⟨le_of_lt hs.1, ?_, hs.2.1, ?_⟩
      · simp [he]
      · intro hj; omega

/-- One particle per numerical prime, before G_i. Active primes are never pending. -/
def memoryScheduleBefore (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => ji.1.val < i ∧ i ≤ ji.2.val ∧ i ∉ A

/-- One particle per numerical prime, after G_i. -/
def memoryScheduleAfter (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => ji.1.val ≤ i ∧ i < ji.2.val ∧ i ∉ A

def memoryScheduleTerminate (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => ji.2.val = i ∧ i ∉ A

def memoryScheduleGhostBirth (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => ji.1.val = i ∧ i ∉ A

def memoryScheduleStore (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => i ∈ A ∧ i+1 ∉ A ∧ i < ji.2.val

def memorySchedulePromote (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => i ∉ A ∧ i+1 ∈ A ∧ ji.1.val ≤ i

def memoryScheduleFresh (A : Finset ℕ) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : Prop :=
  match l with
  | none => False
  | some ji => i ∉ A ∧ i+1 ∈ A ∧ ji.1.val = i+1

def memoryScheduleResidue (p : ℕ) (h : ℕ → ZMod p) {n : ℕ}
    (l : MemoryLifespanChoice n) (i : ℕ) : ZMod p :=
  match l with
  | none => 0
  | some ji => h i - h ji.1.val

/-- The source G order is termination, then birth; this is not a bijection
between arbitrary augmented occurrence representatives. -/
theorem memory_schedule_G_exact (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ) :
    memoryScheduleAfter A l i ↔
      (memoryScheduleBefore A l i ∧ ¬ memoryScheduleTerminate A l i) ∨
        memoryScheduleGhostBirth A l i := by
  cases l with
  | none => simp [memoryScheduleAfter, memoryScheduleBefore,
      memoryScheduleTerminate, memoryScheduleGhostBirth]
  | some ji =>
    rcases hs with ⟨hjd, hA, hh, hsingle⟩
    simp only [memoryScheduleAfter, memoryScheduleBefore,
      memoryScheduleTerminate, memoryScheduleGhostBirth]
    by_cases ha : i ∈ A
    · simp [ha]
    · have hneq : ¬ (ji.1.val = i ∧ ji.2.val = i) := by
        intro he
        have heq : ji.1.val = ji.2.val := by omega
        have hm := hsingle heq
        exact ha (he.1 ▸ hm)
      simp only [ha, not_false_eq_true, and_true]
      omega

/-- Exactly the source edge pending multiset at the level of one distinct
prime: store, translate, OLD promote, retain. -/
theorem memory_schedule_E_exact (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ) :
    memoryScheduleBefore A l (i+1) ↔
      (memoryScheduleAfter A l i ∨ memoryScheduleStore A l i) ∧
        ¬ memorySchedulePromote A l i := by
  cases l with
  | none => simp [memoryScheduleAfter, memoryScheduleBefore,
      memoryScheduleStore, memorySchedulePromote]
  | some ji =>
    rcases hs with ⟨hjd, hA, hh, hsingle⟩
    have hi := fun ht : i ∈ A => hA i ht
    have hi1 := fun ht : i+1 ∈ A => hA (i+1) ht
    simp only [memoryScheduleAfter, memoryScheduleBefore,
      memoryScheduleStore, memorySchedulePromote]
    by_cases ha : i ∈ A
    · have hia := hi ha
      obtain ⟨hlo, hhi, heq⟩ := hia
      by_cases hb : i+1 ∈ A
      · simp [ha, hb]
      · simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_true,
          and_false, false_and, true_and, or_false, false_or]
        omega
    · by_cases hb : i+1 ∈ A
      · obtain ⟨hlo, hhi, heq⟩ := hi1 hb
        simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_true,
          and_false, false_and, true_and, or_false, false_or]
        exact ⟨False.elim, fun hh => hh.2 hh.1.1⟩
      · simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_true,
          and_false, false_and, true_and, or_false, false_or]
        omega

/-- A promoted atom is already pending AFTER G_i, hence OLD for E_i.
A newly stored active prime is excluded without an extra axiom. -/
theorem memory_schedule_promotion_is_old (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ)
    (hp : memorySchedulePromote A l i) :
    memoryScheduleAfter A l i ∧ ¬ memoryScheduleStore A l i := by
  cases l with
  | none => simp [memorySchedulePromote] at hp
  | some ji =>
    have hb := hs.2.1 (i+1) hp.2.1
    exact ⟨⟨hp.2.2, by omega, hp.1⟩, fun ht => hp.1 ht.1⟩

/-- Unshared target activity is either a unique fresh active birth or OLD promotion. -/
theorem memory_schedule_entry_exact (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ)
    (hi : i ∉ A) (ht : i+1 ∈ A) :
    (memorySchedulePromote A l i ∨ memoryScheduleFresh A l i) ∧
      ¬ (memorySchedulePromote A l i ∧ memoryScheduleFresh A l i) := by
  cases l with
  | none => exact False.elim (by simpa [show A = ∅ from hs] using ht)
  | some ji =>
    have hb := hs.2.1 (i+1) ht
    simp only [memorySchedulePromote, memoryScheduleFresh]
    constructor
    · by_cases hj : ji.1.val ≤ i
      · exact Or.inl ⟨hi, ht, hj⟩
      · exact Or.inr ⟨hi, ht, by omega⟩
    · rintro ⟨hp, hf⟩; omega

theorem memory_schedule_ghost_endpoints_zero (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ) :
    (memoryScheduleTerminate A l i ∨ memoryScheduleGhostBirth A l i) →
      memoryScheduleResidue p h l i = 0 := by
  cases l with
  | none => simp [memoryScheduleTerminate, memoryScheduleGhostBirth]
  | some ji =>
    intro he
    rcases he with ht | hb
    · simp only [memoryScheduleResidue]
      rw [← ht.1, hs.2.2.1, sub_self]
    · simp [memoryScheduleResidue, ← hb.1]

theorem memory_schedule_active_anchor (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (l : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A l) (i : ℕ) (hi : i ∈ A) :
    memoryScheduleResidue p h l i = 0 := by
  cases l with
  | none => exact False.elim (by simpa [show A = ∅ from hs] using hi)
  | some ji => simp [memoryScheduleResidue, (hs.2.1 i hi).2.2]

theorem memory_schedule_residue_translate (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (ji : Fin n × Fin n) (i : ℕ) :
    memoryScheduleResidue p h (some ji) i + (h (i+1) - h i) =
      memoryScheduleResidue p h (some ji) (i+1) := by
  simp only [memoryScheduleResidue]; ring

theorem memory_schedule_store_resets_same_anchor (p : ℕ) (h : ℕ → ZMod p)
    (A : Finset ℕ) {n : ℕ} (ji : Fin n × Fin n)
    (hs : MemoryFrozenScheduleSupport p h A (some ji)) (i : ℕ)
    (hi : memoryScheduleStore A (some ji) i) :
    h (i+1) - h i = memoryScheduleResidue p h (some ji) (i+1) := by
  simp only [memoryScheduleResidue]
  rw [(hs.2.1 i hi.1).2.2]

/-- Both original vacuum boundaries are automatic for every nonzero schedule. -/
theorem memory_schedule_vacua (A : Finset ℕ) {N : ℕ}
    (l : MemoryLifespanChoice (N+1)) :
    ¬ memoryScheduleBefore A l 0 ∧ ¬ memoryScheduleAfter A l N := by
  cases l with
  | none => simp [memoryScheduleBefore, memoryScheduleAfter]
  | some ji =>
    have hd := ji.2.isLt
    simp only [memoryScheduleBefore, memoryScheduleAfter]
    omega
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenPrimeScalarNormalForm -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Enlarge a tail product to the complete original visit carrier. -/
theorem memory_orphan_tail_on_full_range (u : ℕ → ℝ) (a z n : ℕ) (hzn : z ≤ n) :
    physicalOrphanTail u a z =
      ∏ t ∈ Finset.range n, if a < t ∧ t < z then 1-u t else 1 := by
  unfold physicalOrphanTail
  rw [← Finset.prod_subset (Finset.range_mono hzn)
    (f := fun t => if a < t ∧ t < z then 1-u t else 1)]
  · apply Finset.prod_congr rfl
    intro t ht
    simp only [Finset.mem_range.mp ht, and_true]
  · intro t htn htz
    have hz : ¬ t < z := by simpa only [Finset.mem_range] using htz
    simp [hz]

theorem memory_orphan_tail_self (u : ℕ → ℝ) (a : ℕ) : physicalOrphanTail u a a = 1 := by
  unfold physicalOrphanTail
  apply Finset.prod_eq_one
  intro t ht
  have hh := Finset.mem_range.mp ht
  simp [show ¬ a < t by omega]

/-- Split the whole supported interval at its first and last active visits. -/
theorem memory_supported_interval_product_split (u : ℕ → ℝ) (A : Finset ℕ)
    (n a z a0 z0 : ℕ) (haa : a ≤ a0) (ha0z0 : a0 ≤ z0)
    (hzz : z0 ≤ z) (hzn : z ≤ n) (ha0 : a0 ∈ A) (hz0 : z0 ∈ A)
    (hb : ∀ t ∈ A, a0 ≤ t ∧ t ≤ z0) :
    (∏ t ∈ Finset.range n, if a < t ∧ t < z ∧ t ∉ A then 1-u t else 1) =
      physicalOrphanTail u a a0 * memoryActiveCore u A a0 z0 n *
        physicalOrphanTail u z0 z := by
  rw [memory_orphan_tail_on_full_range u a a0 n (by omega),
    memory_orphan_tail_on_full_range u z0 z n hzn]
  unfold memoryActiveCore
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  by_cases hm : t ∈ A
  · have hh := hb t hm
    simp [hm, show ¬ (a < t ∧ t < a0) by omega,
      show ¬ (z0 < t ∧ t < z) by omega]
  · by_cases hleft : t < a0
    · have hmid : ¬ (a0 < t ∧ t < z0 ∧ t ∉ A) := by omega
      have hright : ¬ (z0 < t ∧ t < z) := by omega
      have he : (a < t ∧ t < z ∧ t ∉ A) ↔ (a < t ∧ t < a0) := by
        constructor
        · intro hh; omega
        · intro hh; exact ⟨hh.1, by omega, hm⟩
      simp only [he, hmid, hright, if_false, mul_one]
    · by_cases hright : z0 < t
      · have hmid : ¬ (a0 < t ∧ t < z0 ∧ t ∉ A) := by omega
        have hleft' : ¬ (a < t ∧ t < a0) := by omega
        have he : (a < t ∧ t < z ∧ t ∉ A) ↔ (z0 < t ∧ t < z) := by
          constructor
          · intro hh; omega
          · intro hh; exact ⟨by omega, hh.2, hm⟩
        simp only [he, hmid, hleft', if_false, one_mul]
      · have hta : a0 < t := by
          by_contra hh
          have he : t = a0 := by omega
          exact hm (he ▸ ha0)
        have htz : t < z0 := by
          by_contra hh
          have he : t = z0 := by omega
          exact hm (he ▸ hz0)
        simp [hm, hta, htz, hleft, hright, show a < t by omega, show t < z by omega]

/-- Exact literal one-prime density on a supported lifespan. This is a
coefficient identity, not an assumed terminal weighted-fibre equation. -/
theorem memory_frozen_prime_supported_normal_form (p : ℕ) (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ) (az : Fin n × Fin n)
    (hs : MemoryFrozenScheduleSupport p h A (some az)) :
    memoryFrozenPrimeTerm p eta h A n (some az) =
      (if az.1.val ∈ A then 1 else -eta az.1.val) *
      (if az.2.val ∈ A then 1 else -eta az.2.val) *
      (∏ t ∈ Finset.range n,
        if az.1.val < t ∧ t < az.2.val ∧ t ∉ A then
          1 - eta t * (if h t = h az.1.val then (1 : ℝ) else 0) else 1) / (p : ℝ) := by
  rcases hs with ⟨haz,hb,hh,hsingle⟩
  let a := az.1.val
  let z := az.2.val
  let u := fun t => eta t * (if h t = h a then (1 : ℝ) else 0)
  by_cases hA : A.Nonempty
  · let a0 := A.min' hA
    let z0 := A.max' hA
    have ha0 : a0 ∈ A := A.min'_mem hA
    have hz0 : z0 ∈ A := A.max'_mem hA
    have haa : a ≤ a0 := (hb a0 ha0).1
    have hzz : z0 ≤ z := (hb z0 hz0).2.1
    have hmid : a0 ≤ z0 := A.min'_le_max' hA
    have hb0 : ∀ t ∈ A, a0 ≤ t ∧ t ≤ z0 := fun t ht => ⟨A.min'_le t ht,A.le_max' t ht⟩
    have ha0hit : h a0 = h a := (hb a0 ha0).2.2
    have hc : (∀ t ∈ A, h t = h a0) ∧ a ≤ a0 := by
      exact ⟨fun t ht => ((hb t ht).2.2).trans ha0hit.symm, haa⟩
    have hu : (fun t => eta t * (if h t = h a0 then (1 : ℝ) else 0)) = u := by
      funext t
      simp only [u,ha0hit]
    have hpre : memoryPrefixChoice u a0 a =
        (if a ∈ A then 1 else -eta a) * physicalOrphanTail u a a0 := by
      by_cases he : a = a0
      · have ha : a ∈ A := he ▸ ha0
        simp [memoryPrefixChoice, he, ha0, memory_orphan_tail_self]
      · have ha : a ∉ A := by
          intro ht
          have := A.min'_le a ht
          omega
        simp [memoryPrefixChoice,he,ha,u]
    have hsuf : memorySuffixChoice u z0 z =
        (if z ∈ A then 1 else -eta z) * physicalOrphanTail u z0 z := by
      by_cases he : z = z0
      · have hz : z ∈ A := he ▸ hz0
        simp [memorySuffixChoice, he, hz0, memory_orphan_tail_self]
      · have hz : z ∉ A := by
          intro ht
          have := A.le_max' z ht
          omega
        have hzlt : z0 < z := by omega
        simp [memorySuffixChoice,he,hzlt,hz,u,show h z = h a from hh]
    have hp := memory_supported_interval_product_split u A n a z a0 z0 haa hmid
      hzz (Nat.le_of_lt az.2.isLt) ha0 hz0 hb0
    unfold memoryFrozenPrimeTerm
    rw [dif_pos hA]
    change memoryRepresentedTerm p eta h A n a0 z0 (some az) = _
    change ((∀ t ∈ A, h t = h a0) ∧ az.1.val ≤ a0) at hc
    unfold memoryRepresentedTerm
    dsimp only
    rw [if_pos hc, hu]
    change memoryPrefixChoice u a0 a * memoryActiveCore u A a0 z0 n *
      memorySuffixChoice u z0 z / (p : ℝ) = _
    rw [hpre,hsuf]
    change _ = (if a ∈ A then 1 else -eta a) * (if z ∈ A then 1 else -eta z) *
      (∏ t ∈ Finset.range n, if a < t ∧ t < z ∧ t ∉ A then 1-u t else 1) / (p : ℝ)
    rw [hp]
    ring
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hazlt : a < z := by
      by_contra hn
      have hae : a = z := by omega
      have := hsingle hae
      simpa [he] using this
    have hp := memory_orphan_tail_on_full_range u a z n (Nat.le_of_lt az.2.isLt)
    simp only [memoryFrozenPrimeTerm,dif_neg hA,memoryAbsentTerm,memoryOrphanInterval]
    change az.1.val < az.2.val at hazlt
    simp only [hazlt,hh,if_true,he,Finset.notMem_empty,not_false_eq_true,if_false]
    change eta a * eta z * 1 * physicalOrphanTail u a z / (p : ℝ) = _
    rw [hp]
    dsimp only [a,z,u]
    simp only [and_true]
    ring
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenPrimeFiniteOffsetCongr -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
/-- Literal supported prime density only reads its actual finite visit range. -/
theorem memory_frozen_prime_supported_offset_congr (p : ℕ) (eta : ℕ → ℝ)
    (h h' : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ)
    (life : MemoryLifespanChoice n)
    (hs : MemoryFrozenScheduleSupport p h A life)
    (hc : ∀ t < n, h t = h' t) :
    memoryFrozenPrimeTerm p eta h A n life = memoryFrozenPrimeTerm p eta h' A n life := by
  cases life with
  | none =>
    have he : A = ∅ := hs
    simp [he,memoryFrozenPrimeTerm,memoryAbsentTerm]
  | some az =>
    have hs' : MemoryFrozenScheduleSupport p h' A (some az) := by
      refine ⟨hs.1,?_,?_,hs.2.2.2⟩
      · intro t ht
        have hh := hs.2.1 t ht
        refine ⟨hh.1,hh.2.1,?_⟩
        rw [← hc t (by have := az.2.isLt; omega),← hc az.1.val az.1.isLt]
        exact hh.2.2
      · rw [← hc az.2.val az.2.isLt,← hc az.1.val az.1.isLt]
        exact hs.2.2.1
    rw [memory_frozen_prime_supported_normal_form p eta h A n az hs,
      memory_frozen_prime_supported_normal_form p eta h' A n az hs']
    congr 2
    apply Finset.prod_congr rfl
    intro t ht
    rw [hc t (Finset.mem_range.mp ht),hc az.1.val az.1.isLt]
end Green64FullPhysicalE

end

end

/-! ## MemorySourcePrimeExclusions -/

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

/-- Literal factorization of D, including repeated independent auxiliary draws.
Primality, rather than a squarefree D assumption, identifies every prime divisor. -/
theorem memory_source_D_prime_support
    (hsmall : ∀ g p, Nat.Prime (smallMod g p))
    (hbig : ∀ g p, Nat.Prime (bigMod g p))
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (p : ℕ) (hp : Nat.Prime p) :
    p ∣ memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss ↔
      (∃ g : SG, ∃ i ∈ sourceSmallShared J ell g,
        p = smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell) (x.1 g) (ss g i))) ∨
      (∃ g : BG, ∃ i ∈ sourceBigShared J ell m pat g,
        p = bigMod g (Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i))) ∨
      (∃ g : BG, ∃ i : ↥(pat.free g), p = bigMod g (aux g i)) := by
  have hr : Prime p := Nat.prime_iff.mp hp
  simp only [memoryIndependentD, hp.dvd_mul, hr.dvd_finset_prod_iff]
  constructor
  · rintro (⟨g, _, i, hi, hd⟩ | ⟨g, _, hd⟩)
    · exact Or.inl ⟨g, i, hi, ((hsmall g _).dvd_iff_eq hp.ne_one).mp hd |>.symm⟩
    · rcases hd with ⟨i, hi, hd⟩ | ⟨i, _, hd⟩
      · exact Or.inr (Or.inl ⟨g, i, hi, ((hbig g _).dvd_iff_eq hp.ne_one).mp hd |>.symm⟩)
      · exact Or.inr (Or.inr ⟨g, i, ((hbig g _).dvd_iff_eq hp.ne_one).mp hd |>.symm⟩)
  · rintro (⟨g, i, hi, he⟩ | ⟨g, i, hi, he⟩ | ⟨g, i, he⟩)
    · exact Or.inl ⟨g, Finset.mem_univ _, i, hi, he ▸ dvd_refl _⟩
    · exact Or.inr ⟨g, Finset.mem_univ _, Or.inl ⟨i, hi, he ▸ dvd_refl _⟩⟩
    · exact Or.inr ⟨g, Finset.mem_univ _, Or.inr ⟨i, Finset.mem_univ _, he ▸ dvd_refl _⟩⟩

/-- Every BIG endpoint prime dividing D comes from a prescribed shared source
slot. The auxiliary ban is retained for BOTH endpoints. -/
theorem memory_source_endpoint_divisor_is_shared
    (hsmall : ∀ g p, Nat.Prime (smallMod g p))
    (hbig : ∀ g p, Nat.Prime (bigMod g p))
    (hinj : Function.Injective (fun p : Sigma BP => bigMod p.1 p.2))
    (hdisj : ∀ gs ps gb pb, smallMod gs ps ≠ bigMod gb pb)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m pat aux x y)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (g : BG) (p : BP g)
    (hend : (∃ i, Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) i = p) ∨
      (∃ i, Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) i = p))
    (hd : bigMod g p ∣ memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss) :
    ∃ i ∈ sourceBigShared J ell m pat g,
      Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i) = p := by
  have hs := (memory_source_D_prime_support SP smallMod BP bigMod J ell m
    hsmall hbig pat aux x bs ss (bigMod g p) (hbig g p)).mp hd
  rcases hs with ⟨gg, i, hi, he⟩ | ⟨gg, i, hi, he⟩ | ⟨gg, i, he⟩
  · exact False.elim (hdisj gg _ g p he.symm)
  · have hsigma : (⟨g, p⟩ : Sigma BP) =
        ⟨gg, Green64SmallHaar.marks (bigMod gg) (J+ell) (x.2 gg) (bs gg i)⟩ := hinj he
    have hg : g = gg := congrArg Sigma.fst hsigma
    subst gg
    have hval : p = Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i) :=
      eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    exact ⟨i, hi, hval.symm⟩
  · have hsigma : (⟨g, p⟩ : Sigma BP) = ⟨gg, aux gg i⟩ := hinj he
    have hg : g = gg := congrArg Sigma.fst hsigma
    subst gg
    have hval : p = aux g i := eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    rcases hend with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact False.elim ((hban g i a).1 (hval.symm.trans ha.symm))
    · exact False.elim ((hban g i a).2 (hval.symm.trans ha.symm))

/-- Required store exclusion derived at a literal unshared source slot. -/
theorem memory_source_unshared_exit_not_dividing
    (hsmall : ∀ g p, Nat.Prime (smallMod g p))
    (hbig : ∀ g p, Nat.Prime (bigMod g p))
    (hinj : Function.Injective (fun p : Sigma BP => bigMod p.1 p.2))
    (hdisj : ∀ gs ps gb pb, smallMod gs ps ≠ bigMod gb pb)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m pat aux x y)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (g : BG) (i : Fin (J+ell)) (hi : i ∉ sourceBigShared J ell m pat g) :
    ¬ bigMod g (Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i)) ∣
      memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss := by
  intro hd
  obtain ⟨j, hj, he⟩ := memory_source_endpoint_divisor_is_shared SP smallMod BP bigMod
    J ell m hsmall hbig hinj hdisj pat aux x y hban bs ss g _
    (Or.inl ⟨bs g i, rfl⟩) hd
  have hji : j = i := (bs g).injective
    (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (x.2 g) he)
  exact hi (hji ▸ hj)

/-- Required OLD-promotion exclusion derived at a literal unshared target slot. -/
theorem memory_source_unshared_entry_not_dividing
    (hsmall : ∀ g p, Nat.Prime (smallMod g p))
    (hbig : ∀ g p, Nat.Prime (bigMod g p))
    (hinj : Function.Injective (fun p : Sigma BP => bigMod p.1 p.2))
    (hdisj : ∀ gs ps gb pb, smallMod gs ps ≠ bigMod gb pb)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m pat aux x y)
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hcopy : ∀ g j, j ∈ sourceBigShared J ell m pat g →
      Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g j))
    (g : BG) (i : Fin (J+ell)) (hi : i ∉ sourceBigShared J ell m pat g) :
    ¬ bigMod g (Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g i)) ∣
      memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss := by
  intro hd
  obtain ⟨j, hj, he⟩ := memory_source_endpoint_divisor_is_shared SP smallMod BP bigMod
    J ell m hsmall hbig hinj hdisj pat aux x y hban bs ss g _
    (Or.inr ⟨bt g i, rfl⟩) hd
  have ht : Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g i) :=
    (hcopy g j hj).symm.trans he
  have hji : j = i := (bt g).injective
    (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (y.2 g) ht)
  exact hi (hji ▸ hj)
end Green64FullPhysicalE

end

end

/-! ## MemorySourceActiveContinuation -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- True physical compatibility derives p|D for a prime active at both ends.
The hypothesis |k|<p comes from the original prime-group domain. -/
theorem memory_active_both_ends_divides_D
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)] (M : ℕ)
    (x y : Green64SmallHaar.SmallState modulus M)
    (D : ℕ) (o k : ℤ) (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (p : P) (hp : Nat.Prime (modulus p)) (habove : k.natAbs < modulus p)
    (hshift : Green64SmallHaar.residues modulus M y =
      Green64SmallHaar.translate modulus (o*k*(D : ℤ))
        (Green64SmallHaar.residues modulus M x))
    (a b : Fin M) (ha : Green64SmallHaar.marks modulus M x a = p)
    (hb : Green64SmallHaar.marks modulus M y b = p) : modulus p ∣ D := by
  have hx : Green64SmallHaar.residues modulus M x p = 0 := by
    rw [← ha]
    exact Green64SmallHaar.marked_zero modulus M x a
  have hy : Green64SmallHaar.residues modulus M y p = 0 := by
    rw [← hb]
    exact Green64SmallHaar.marked_zero modulus M y b
  have hz : ((o*k*(D : ℤ) : ℤ) : ZMod (modulus p)) = 0 := by
    have ht := congrFun hshift p
    simpa only [Green64SmallHaar.translate, hx, hy, zero_add] using ht.symm
  have hd : (modulus p : ℤ) ∣ o*k*(D : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hdk : (modulus p : ℤ) ∣ k*(D : ℤ) := by
    rcases ho with ho | ho
    · simpa [ho] using hd
    · simpa [ho, neg_mul] using hd
  have hcases := Int.Prime.dvd_mul hp hdk
  rcases hcases with hbad | hD
  · have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    exact False.elim (Nat.not_le_of_lt habove (Nat.le_of_dvd hpos hbad))
  · simpa using hD

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)

/-- Exact runs/shared bridge required by the canonical inverse. A prime active
at both endpoints is copied in the SAME canonical shared slot. Consequently
consecutive active uses incur neither fresh birth nor OLD promotion. -/
theorem memory_source_active_continuation_is_shared
    (hsmall : ∀ g p, Nat.Prime (smallMod g p))
    (hbig : ∀ g p, Nat.Prime (bigMod g p))
    (hinj : Function.Injective (fun p : Sigma BP => bigMod p.1 p.2))
    (hdisj : ∀ gs ps gb pb, smallMod gs ps ≠ bigMod gb pb)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m pat aux x y)
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (o k : ℤ) (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (habove : ∀ g p, k.natAbs < bigMod g p)
    (hleg : Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m pat)
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss : ℤ))
      bs bt x.2 y.2)
    (g : BG) (i j : Fin (J+ell))
    (he : Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g j)) :
    i ∈ sourceBigShared J ell m pat g ∧ j = i := by
  let p := Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i)
  have hd := memory_active_both_ends_divides_D (bigMod g) (J+ell) (x.2 g) (y.2 g)
    (memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss)
    o k ho hk p (hbig g p) (habove g p) (hleg g).1 (bs g i) (bt g j) rfl he.symm
  obtain ⟨a, ha, hap⟩ := memory_source_endpoint_divisor_is_shared SP smallMod BP bigMod
    J ell m hsmall hbig hinj hdisj pat aux x y hban bs ss g p
    (Or.inl ⟨bs g i, rfl⟩) hd
  have hai : a = i := (bs g).injective
    (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (x.2 g) hap)
  have hi : i ∈ sourceBigShared J ell m pat g := hai ▸ ha
  have hcopy := (hleg g).2 i hi
  have hij : i = j := (bt g).injective
    (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (y.2 g)
      (hcopy.symm.trans he))
  exact ⟨hi, hij.symm⟩
end Green64FullPhysicalE

end

end

/-! ## PhysicalOrientedGEIndexedSigmaCarrier -/

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

abbrev PhysicalOrientedGWitnessIndex :=
  Σ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    Σ yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x

abbrev PhysicalOrientedEWitnessIndex :=
  Σ xe : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns xe

/-- A genuinely indexed G→E pair is a DEPENDENT Sigma pair.
The G witness determines the true E physical Fock input fibre
and the globally seen primes. Each legal original E choice,
including SMALL/BIG sigma/tau and all ν/free-D draws, remains
separate and is never replaced by its symmetric Fock output. -/
noncomputable def physicalOrientedGEIndexedCarrier
    (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    Finset (Σ g : PhysicalOrientedGWitnessIndex
      SP smallMod BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
        J ell m cap patterns) :=
  (physicalGIndexedEligibleFibre SP smallMod BP bigMod
    J ell cap y seen).sigma (fun a =>
    physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod
      J ell m cap patterns orientation k
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap a.2.1)
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap a.1 a.2.2).toFinset))

/-- The inherited TRUE physical output of the E witness; the
underlying OLD memory multiset is never replaced by a set. -/
noncomputable def physicalOrientedGEIndexedOutput
    (orientation k : ℤ)
    (ab : Σ g : PhysicalOrientedGWitnessIndex
        SP smallMod BP bigMod J ell cap,
        PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
          J ell m cap patterns) :
    FullPhysicalOutput SP smallMod BP bigMod (J+ell) :=
  sourceOrientedPhysicalOutput SP smallMod BP bigMod
    J ell m cap patterns ab.2.1 orientation k ab.2.2

/-- EXACT chronological seen update, with G old deletions,
stores, promotions and D auxiliaries EXCLUDED from new births. -/
noncomputable def physicalOrientedGEIndexedNextSeen
    (seen : Finset ℕ)
    (ab : Σ g : PhysicalOrientedGWitnessIndex
        SP smallMod BP bigMod J ell cap,
        PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
          J ell m cap patterns) : Finset ℕ :=
  (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
    (J+ell) cap ab.1.1 ab.1.2.2).toFinset) ∪
    (orientedEFreshBirths SP smallMod BP bigMod
      J ell m cap patterns ab.2.2).toFinset

/-- The exact two conditional Hilbert fibre masses, original
G OLD/ghost scalar and COMPLETE corrected E ν/D/SMALL/BIG scalar.
No new stochastic normalization and no lost branch multiplicity. -/
noncomputable def physicalOrientedGEIndexedWeight
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (ab : Σ g : PhysicalOrientedGWitnessIndex
        SP smallMod BP bigMod J ell cap,
        PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
          J ell m cap patterns) : ℂ :=
  (((fullPhysicalMass SP smallMod BP bigMod
    (J+ell) cap Vsmall muBig ab.1.1 : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig y : ℂ)) *
    physicalGBranchTerm SP smallMod BP bigMod
      (J+ell) cap q rho N i Vbig muBig
      ab.1.1 ab.1.2.1 ab.1.2.2) *
  (((fullPhysicalMass SP smallMod BP bigMod
    (J+ell) cap Vsmall muBig ab.2.1 : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap ab.1.2.1) : ℂ)) *
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k ab.2.1 ab.2.2)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedGEIndexedSigmaExact -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 500000

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

variable (q rho : ℝ) (N i : ℕ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (orientation k : ℤ)

/-- The ENTIRE corrected physical one-edge G_i E_i marked
root operation equals the finite sum over the concrete DEPENDENT
Sigma carrier of all original indexed physical G and oriented E
witnesses. The first and second TRUE conditional Fock masses,
G OLD/ghost scalar, ν/free-D, complete SMALL/BIG Haar source
permutations, legal E-OLD operations, and single chronological
birth indicator all remain explicitly present.

No invented Markov kernel, no quotient to distinct numerical prime
sets, and no hypothesis of a preselected complete witness family. -/
theorem physical_oriented_GE_indexed_sigma_exact
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) →
      Finset ℕ → ℂ) :
    physicalOrientedRawWitnessGE SP smallMod BP bigMod
      J ell m cap patterns q rho N i Vsmall Vbig muBig
      Knu zeta theta orientation k F y seen =
    ∑ ab ∈ physicalOrientedGEIndexedCarrier SP smallMod
        BP bigMod J ell m cap patterns orientation k y seen,
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N i Vsmall Vbig muBig
        Knu zeta theta orientation k y ab *
      F (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns orientation k ab)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab) := by
  rw [physicalOrientedRawWitnessGE_eq_source]
  rw [physical_G_indexed_fibre_exact]
  let G : Finset (PhysicalOrientedGWitnessIndex SP smallMod
      BP bigMod J ell cap) :=
    physicalGIndexedEligibleFibre SP smallMod BP bigMod
      J ell cap y seen
  let E : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap → Finset (PhysicalOrientedEWitnessIndex
        SP smallMod BP bigMod J ell m cap patterns) := fun a =>
    physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod
      J ell m cap patterns orientation k
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap a.2.1)
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap a.1 a.2.2).toFinset)
  let U : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap → ℂ := fun a =>
    ((fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig a.1 : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig y : ℂ)) *
      physicalGBranchTerm SP smallMod BP bigMod
        (J+ell) cap q rho N i Vbig muBig a.1 a.2.1 a.2.2
  let V : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap → PhysicalOrientedEWitnessIndex SP smallMod
        BP bigMod J ell m cap patterns → ℂ := fun a b =>
    ((fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall muBig b.1 : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap a.2.1) : ℂ)) *
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig Knu
        zeta theta orientation k b.1 b.2
  let C : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap → PhysicalOrientedEWitnessIndex SP smallMod
        BP bigMod J ell m cap patterns → ℂ := fun a b =>
    F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns b.1 orientation k b.2)
      ((seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap a.1 a.2.2).toFinset) ∪
        (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns b.2).toFinset)
  have hE (a : PhysicalOrientedGWitnessIndex SP smallMod
      BP bigMod J ell cap) :
      physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig Knu
        zeta theta orientation k
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap a.2.1)
        (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap a.1 a.2.2).toFinset) F =
      ∑ b ∈ E a, V a b * C a b :=
    physical_oriented_E_indexed_fibre_exact SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig
      muBig Knu zeta theta orientation k _ _ F
  change (∑ a ∈ G, U a *
    physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap a.2.1)
      (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap a.1 a.2.2).toFinset) F) = _
  calc
    _ = ∑ a ∈ G, U a * (∑ b ∈ E a, V a b * C a b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hE a]
    _ = ∑ ab ∈ G.sigma E,
        (U ab.1 * V ab.1 ab.2) * C ab.1 ab.2 :=
      finite_nested_legal_sigma_weighted G E U V C
    _ = _ := by
      rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFiniteWitnessTraceCarrier -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Finite source G_N terminal input/witness occurrence carrier.
The real terminal G weight and vacuum output remain in its scalar,
rather than imposing an unproven early terminal-normalization rule. -/
abbrev PhysicalOrientedTerminalIndex
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)]
    [∀ g, DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ)
    [∀ g, ∀ p, NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (bigMod g p)]
    (J ell : ℕ) (cap : BG → ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) : Type :=
  {a : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
    J ell cap // a ∈ physicalGIndexedEligibleFibre SP smallMod
      BP bigMod J ell cap y seen}


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

/-- Real index of a complete physically admissible oriented GE
pair at the current source orbit and numerical seen-birth state. -/
abbrev PhysicalOrientedGEIndex (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) : Type :=
  {ab : (Σ g : PhysicalOrientedGWitnessIndex
    SP smallMod BP bigMod J ell cap,
    PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
      J ell m cap patterns) //
    ab ∈ physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
      J ell m cap patterns orientation k y seen}

/-- A TRUE finite original physically indexed witness TRACE:
for every E_i, the source G OLD+ghost witness, independent E Fock
input representative, ν/free-D, two SMALL/BIG endpoint permutation
families and E OLD injections/fresh births are indexed; the next
orbital state and numerical seen state are computed from that choice.
The terminal G_N is selected separately. This carrier is defined
recursively from actual source branches, not assumed complete. -/
noncomputable def physicalOrientedIndexedTrace
    (orientation k : ℤ) :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) → Type
  | 0, _, y, seen =>
    PhysicalOrientedTerminalIndex SP smallMod BP bigMod
      J ell cap y seen
  | remaining+1, start, y, seen =>
    Σ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns
      (physicalAlternatingSign start) k y seen,
      physicalOrientedIndexedTrace orientation k remaining
        (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab.val)

/-- Every bounded source witness trace is genuinely FINITE; this
is constructed recursively from the actual (potentially dependent)
physical G and E finite choice families, not from an arbitrary
finite set of predeclared literal histories. -/
@[reducible] noncomputable def physicalOrientedIndexedTraceFintype
    (orientation k : ℤ) :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns orientation k remaining start y seen)
  | 0, _, y, seen => by
      change Fintype (PhysicalOrientedTerminalIndex
        SP smallMod BP bigMod J ell cap y seen)
      infer_instance
  | remaining+1, start, y, seen => by
      change Fintype
        (Σ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k y seen,
          physicalOrientedIndexedTrace SP smallMod BP bigMod
            J ell m cap patterns orientation k remaining (start+1)
            (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
              J ell m cap patterns
              (physicalAlternatingSign start) k ab.val)
            (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
              J ell m cap patterns seen ab.val))
      letI : (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k y seen) →
        Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
          J ell m cap patterns orientation k remaining (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val)) := fun ab =>
          physicalOrientedIndexedTraceFintype orientation k
            remaining (start+1)
            (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
              J ell m cap patterns
              (physicalAlternatingSign start) k ab.val)
            (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
              J ell m cap patterns seen ab.val)
      infer_instance

end Green64FullPhysicalE

end

/-! ## PhysicalFiniteIndexedSubtypeSum -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Sum over the genuine FINITE index subtype of a legal witness
Finset is exactly its indexed Finset sum. Identical projected
outputs are NOT merged: the source indices themselves are distinct. -/
theorem finite_indexed_legal_subtype_sum
    {A : Type} [Fintype A] [DecidableEq A]
    (s : Finset A) (f : A → ℂ) :
    (∑ a : {a : A // a ∈ s}, f a.val) =
      ∑ a ∈ s, f a := by
  classical
  simp only [Finset.univ_eq_attach, Finset.sum_attach]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFiniteWitnessTraceWeight -/

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- Actual final G_N coefficient with its true input-Hilbert
conditional Fock mass and TRUE terminal vacuum output.
One final ghost witness is selected from the original carrier,
not compressed to a count or a set of numerical primes. -/
noncomputable def physicalOrientedIndexedTerminalWeight
    (start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (a : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
      J ell cap) : ℂ :=
  ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
      Vsmall muBig a.1 : ℂ) /
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap
      Vsmall muBig y : ℂ)) *
    physicalGBranchTerm SP smallMod BP bigMod
      (J+ell) cap q rho N start Vbig muBig
      a.1 a.2.1 a.2.2 *
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap a.2.1)

/-- The genuine ordered-witness trace weight is the product of
the complete indexed oriented G_iE_i scalars at every step and the
genuine terminal G_N/vacuum scalar. Each Hilbert representative is
integrated by its own original orbit-mass probability. -/
noncomputable def physicalOrientedIndexedTraceWeight :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen → ℂ
  | 0, start, y, _, a =>
    physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig muBig N start y a.val
  | remaining+1, start, y, seen, ⟨ab, tail⟩ =>
    physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      Knu ((start : ℝ)*zeta) theta
      (physicalAlternatingSign start) k y ab.val *
    physicalOrientedIndexedTraceWeight remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val) tail

/-- The FINITE sum over the actual recursively constructed indexed
original G_0E_0...G_N witness traces, with global chronological
birth checking at every branching operation. -/
noncomputable def physicalOrientedIndexedTraceSum
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) : ℂ :=
  letI : Fintype (physicalOrientedIndexedTrace SP smallMod BP
      bigMod J ell m cap patterns 1 k remaining start y seen) :=
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen
  ∑ t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen,
    physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedTerminalTraceExact -/

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
variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
variable (N start : ℕ)

/-- The REAL terminal G_N marked row with physical vacuum as its
output test equals the exact sum of ALL original finite indexed
terminal ghost witnesses, including the input conditional Fock mass.
In particular the terminal ghost branch is NOT compressed or erased. -/
theorem physical_oriented_terminal_G_indexed_exact
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    physicalRawWitnessVisit SP smallMod BP bigMod
      J ell cap q rho N start Vsmall Vbig muBig
      (fun out _seen => physicalVacuum SP smallMod BP bigMod
        J ell out) y seen =
    ∑ a : PhysicalOrientedTerminalIndex SP smallMod BP bigMod
        J ell cap y seen,
      physicalOrientedIndexedTerminalWeight SP smallMod BP
        bigMod J ell cap q rho Vsmall Vbig muBig N start y a.val := by
  rw [physicalRawWitnessVisit_eq_source]
  rw [physical_G_indexed_fibre_exact]
  let G := physicalGIndexedEligibleFibre SP smallMod BP bigMod
    J ell cap y seen
  let t : PhysicalOrientedGWitnessIndex SP smallMod BP
    bigMod J ell cap → ℂ :=
    physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig muBig N start y
  change (∑ a ∈ G, t a) =
    (∑ a : PhysicalOrientedTerminalIndex SP smallMod BP
      bigMod J ell cap y seen, t a.val)
  exact (finite_indexed_legal_subtype_sum G t).symm

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFiniteTraceFold -/

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- The terminal leaf of the genuine finite physically indexed path
tree is exactly the source G_N input-fibre × ghost witness × vacuum
coefficient, no early orbit quotient or terminal factorial. -/
theorem physical_oriented_indexed_trace_sum_zero
    (start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    physicalOrientedIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N 0 start y seen =
    ∑ a : PhysicalOrientedTerminalIndex SP smallMod BP bigMod
      J ell cap y seen,
      physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
        J ell cap q rho Vsmall Vbig muBig N start y a.val := by
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFiniteTraceFoldSucc -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 550000

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- ONE exact recursive unfolding of the complete original
finite G_iE_i...G_N indexed witness tree. Its next orbital state and
seen-birth register depend on the ACTUAL indexed oriented E output.
All original conditional Fock weights remain in the GE scalar. -/
theorem physical_oriented_indexed_trace_sum_succ
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    physicalOrientedIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N (remaining+1) start y seen =
    ∑ ab ∈ physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k y seen,
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ)*zeta) theta
        (physicalAlternatingSign start) k y ab *
      physicalOrientedIndexedTraceSum SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig Knu
        zeta theta k N remaining (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab) := by
  unfold physicalOrientedIndexedTraceSum
  letI : (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns
      (physicalAlternatingSign start) k y seen) →
    Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)) := fun ab =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)
  simp only [physicalOrientedIndexedTrace, physicalOrientedIndexedTraceWeight, Fintype.sum_sigma]
  let S := physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
    J ell m cap patterns (physicalAlternatingSign start) k y seen
  let f : (Σ g : PhysicalOrientedGWitnessIndex SP smallMod
      BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
        J ell m cap patterns) → ℂ := fun ab =>
    physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      Knu ((start : ℝ)*zeta) theta
      (physicalAlternatingSign start) k y ab *
    physicalOrientedIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns (physicalAlternatingSign start) k ab)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab)
  change
    (∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns
      (physicalAlternatingSign start) k y seen,
      ∑ tail : physicalOrientedIndexedTrace SP smallMod BP
        bigMod J ell m cap patterns 1 k remaining (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab.val),
        physicalOrientedGEIndexedWeight SP smallMod BP bigMod
          J ell m cap patterns q rho N start Vsmall Vbig muBig
          Knu ((start : ℝ)*zeta) theta
          (physicalAlternatingSign start) k y ab.val *
        physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N remaining (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail) =
    ∑ ab ∈ S, f ab
  calc
    _ = ∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k y seen,
      f ab.val := by
      apply Finset.sum_congr rfl
      intro ab hab
      dsimp only [f, physicalOrientedIndexedTraceSum]
      rw [Finset.mul_sum]
    _ = ∑ ab ∈ S, f ab :=
      finite_indexed_legal_subtype_sum S f

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFiniteRawChainIndexedExact -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 520000

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- EXACT exhaustive FULL FINITE ORIGINAL ORIENTED G/E WITNESS
PATH EXPANSION: the raw original source root operator chain with
N oriented E steps, all N+1 G visits and the actual final Fock vacuum
is identical to the sum over the recursively constructed FINITE
dependent index type `physicalOrientedIndexedTrace`.

Each tree branch is one actual original ordered G OLD/ghost witness,
two genuine conditional Fock orbit integrations, each source ν/D
and independent SMALL/BIG sigma/tau permutation family, real E OLD
promotions/stores/fresh target, plus all global chronological birth
eligibility indicators. No paths or numerical prime groups are
preselected and no artificial Markov kernel is introduced.

This proves COMPLETENESS of the indexed physical witness expansion
of the corrected ORIENTED raw chain. It does not yet establish a
bijection to the typed PhysicalFiniteActualWitnessPath carrier or the
global LiteralHistory/lifespan memory identity. -/
theorem physical_oriented_raw_chain_full_indexed_exact
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start
      (fun out _seen => physicalVacuum SP smallMod BP bigMod
        J ell out) y seen =
    physicalOrientedIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen := by
  induction remaining generalizing start y seen with
  | zero =>
      change physicalRawWitnessVisit SP smallMod BP bigMod
        J ell cap q rho N start Vsmall Vbig muBig
        (fun out _seen => physicalVacuum SP smallMod BP bigMod
          J ell out) y seen =
        physicalOrientedIndexedTraceSum SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N 0 start y seen
      rw [physical_oriented_terminal_G_indexed_exact]
      rw [physical_oriented_indexed_trace_sum_zero]
  | succ r ih =>
      change physicalOrientedRawWitnessGE SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ)*zeta) theta
        (physicalAlternatingSign start) k
        (physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N r (start+1)
          (fun out _seen => physicalVacuum SP smallMod BP bigMod
            J ell out)) y seen =
        physicalOrientedIndexedTraceSum SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N (r+1) start y seen
      rw [physical_oriented_GE_indexed_sigma_exact]
      rw [physical_oriented_indexed_trace_sum_succ]
      apply Finset.sum_congr rfl
      intro ab hab
      rw [ih (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab)]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullRootIndexedCarrier -/

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

/-- FINITE true source root witness index with initial ordered
SMALL Haar/BIG active/Fock state and exactly 2R original oriented
G/E step choices followed by terminal G_(2R). Both the initial
vacuum and unique first-birth indicator remain in the true scalar.
No initial physical state is discarded from the ambient carrier. -/
abbrev PhysicalOrientedRootIndexedTrace (k : ℤ) (R : ℕ) :=
  Σ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset

/-- The EXACT original source ordered root witness carrier is
finite without assuming any completeness of an arbitrary family. -/
@[reducible] noncomputable def physicalOrientedRootIndexedTraceFintype
    (k : ℤ) (R : ℕ) :
    Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) := by
  letI : (x : FullPhysicalState SP smallMod BP bigMod
      (J+ell) cap) →
    Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset) := fun x =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  exact inferInstance

/-- The original root scalar on one completely indexed REAL
oriented source witness: b_p product once, true initial Hilbert
mass, source vacuum on initial Fock sector, true global initial
birth-Nodup test, all indexed G/E scalars with Fock conditional
ratios and final G_N vacuum. No cancellation of zero factors. -/
noncomputable def physicalOrientedRootIndexedWeight
    (q rho : ℝ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
  (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
    Vsmall mu xt.1 : ℂ) *
  star (physicalVacuum SP smallMod BP bigMod J ell
    (physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap xt.1)) *
  (if (physicalInitialBirths SP smallMod BP bigMod
    J ell cap xt.1).Nodup then
      physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu Knu
        zeta theta k N N 0
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap xt.1).toFinset xt.2
    else 0)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullRootIndexedSum -/

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

/-- Actual exhaustive oriented SOURCE ROOT sum over its recursively
constructed finite Fock/G/E witness tree, including genuine Hilbert
initial mass, SMALL Haar, global b_p and terminal G_N vacuum.
No arbitrary finite input family, postulated Markov kernel or
numerical-prime-set quotient is used. -/
noncomputable def physicalOrientedFullRootIndexedSum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  letI : Fintype (PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  ∑ xt : PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R,
    physicalOrientedRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt

end Green64FullPhysicalE

end

/-! ## PhysicalFiniteRootSigmaFubini -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Exact finite root Fubini for a DEPENDENT trace fibre, with
two ORIGINAL initial Hilbert factors, one global baseline scalar
and the initial distinct-birth indicator. A single G/E physical
witness trace is enumerated once for each concrete root state. -/
theorem finite_root_sigma_trace_fubini
    {X : Type} [Fintype X]
    {Y : X → Type} [∀ x, Fintype (Y x)]
    (baseline : ℂ)
    (mass vacuum : X → ℂ)
    (eligible : X → Prop) (weight : (x : X) → Y x → ℂ) :
    baseline *
      (∑ x : X, (mass x * vacuum x) *
        (if eligible x then ∑ t : Y x, weight x t else 0)) =
    ∑ xt : (Σ x : X, Y x),
      baseline * mass xt.1 * vacuum xt.1 *
        (if eligible xt.1 then weight xt.1 xt.2 else 0) := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases he : eligible x
  · simp only [he, ite_true]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  · simp [he]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullRootIndexedExact -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 650000

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

/-- FULL ROOT COMPLETENESS of the ORIGINAL FINITE
PERMUTATION-CORRECTED physical G_0 E_0 ... G_N source moment.
The root equals the explicit finite sum over recursively indexed
REAL oriented source G/E witnesses and initial ordered Hilbert
states, with terminal vacuum G_N and one numerical birth condition
at every stage.

NO arbitrary W-family completeness assumption, no replacement
of OLD Fock multiplicities by prime sets, no invented Markov kernel.

This is finite root-to-indexed-physical-witness completeness,
NOT the final global lifetime/literal-history pushforward. -/
theorem physical_oriented_finite_root_full_indexed_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R =
    physicalOrientedFullRootIndexedSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  let X := FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  let T : X → Type := fun x =>
    physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k N 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  letI : (x : X) → Fintype (T x) := fun x =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  let b : ℂ := (physicalSourceBaselineProduct BP bigMod q N : ℂ)
  let a : X → ℂ := fun x =>
    (fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall mu x : ℂ)
  let v : X → ℂ := fun x =>
    star (physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x))
  let ok : X → Prop := fun x =>
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap x).Nodup
  let w : (x : X) → T x → ℂ := fun x t =>
    physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig mu Knu
      zeta theta k N N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset t
  have hChain (x : X) :
      physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu Knu
        zeta theta k N N 0
        (fun out _seen => physicalVacuum SP smallMod BP bigMod
          J ell out)
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap x)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap x).toFinset =
      ∑ t : T x, w x t := by
    exact physical_oriented_raw_chain_full_indexed_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig mu Knu zeta theta k N N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  have hFubini :=
    finite_root_sigma_trace_fubini
      (X := X) (Y := T) b a v ok w
  calc
    physicalOrientedFiniteMarkedRoot SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu
        zeta theta k R =
      b * (∑ x : X, (a x * v x) *
        (if ok x then ∑ t : T x, w x t else 0)) := by
      rw [physicalOrientedFiniteMarkedRoot_eq_rawWitnessRoot]
      change b * (∑ x : X, (a x * v x) *
        (if ok x then
          physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig mu Knu
            zeta theta k N N 0
            (fun out _seen => physicalVacuum SP smallMod BP bigMod
              J ell out)
            (physicalFockProjection SP smallMod BP bigMod
              (J+ell) cap x)
            (physicalInitialBirths SP smallMod BP bigMod
              J ell cap x).toFinset
        else 0)) = _
      apply congrArg (fun z : ℂ => b*z)
      apply Finset.sum_congr rfl
      intro x hx
      rw [hChain x]
    _ = ∑ xt : (Σ x : X, T x),
        b * a xt.1 * v xt.1 *
          (if ok xt.1 then w xt.1 xt.2 else 0) := by
      convert hFubini using 1
      apply congrArg (fun z : ℂ => b*z)
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hOk : ok x <;> simp [hOk]
      all_goals
        apply Finset.sum_congr (by ext xt; simp)
        intro xt hxt
        by_cases hOk : ok xt.1 <;> simp [hOk]
    _ = physicalOrientedFullRootIndexedSum SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu
        zeta theta k R := by
      unfold physicalOrientedFullRootIndexedSum
      apply Finset.sum_congr rfl
      intro xt hxt
      rfl

end Green64FullPhysicalE

end

/-! ## MemorySourceTraceWeights -/

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- SOURCE-FAITHFUL fixed-zeta, reverse-K corrected trace weight.
The legal carrier is reused because it has no spectral/kernel parameter.
The weight is the product of
the complete indexed oriented G_iE_i scalars at every step and the
genuine terminal G_N/vacuum scalar. Each Hilbert representative is
integrated by its own original orbit-mass probability. -/
noncomputable def memorySourceIndexedTraceWeight :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen → ℂ
  | 0, start, y, _, a =>
    physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig muBig N start y a.val
  | remaining+1, start, y, seen, ⟨ab, tail⟩ =>
    physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta
      (physicalAlternatingSign start) k y ab.val *
    memorySourceIndexedTraceWeight remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val) tail

/-- The FINITE sum over the actual recursively constructed indexed
original G_0E_0...G_N witness traces, with global chronological
birth checking at every branching operation. -/
noncomputable def memorySourceIndexedTraceSum
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) : ℂ :=
  letI : Fintype (physicalOrientedIndexedTrace SP smallMod BP
      bigMod J ell m cap patterns 1 k remaining start y seen) :=
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen
  ∑ t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen,
    memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t

end Green64FullPhysicalE

end

