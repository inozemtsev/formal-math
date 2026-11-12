module

public import Green64.Library.Sieve.Foundations.Part001
public import Mathlib
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientRing
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Sieve / Foundations / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceCRTLatticeBox -/

section

set_option maxHeartbeats 4000000
namespace Green64Analytic.SourceCRT

def residueIntervalBoxCount (D a b A B C E : ℕ) : ℕ :=
  residueIntervalCount D a A B * residueIntervalCount D b C E

theorem residueIntervalBoxCount_eq_filter
    (D a b A B C E : ℕ) :
    residueIntervalBoxCount D a b A B C E =
      ((Finset.Ico A B ×ˢ Finset.Ico C E).filter
         (fun ij : ℕ × ℕ =>
          Nat.ModEq D ij.1 a ∧ Nat.ModEq D ij.2 b)).card := by
  classical
  unfold residueIntervalBoxCount residueIntervalCount
  have hset :
    ((Finset.Ico A B ×ˢ Finset.Ico C E).filter
       (fun ij : ℕ × ℕ =>
        Nat.ModEq D ij.1 a ∧ Nat.ModEq D ij.2 b)) =
    (Finset.Ico A B).filter (fun x => Nat.ModEq D x a) ×ˢ
    (Finset.Ico C E).filter (fun x => Nat.ModEq D x b) := by
    ext ⟨x,y⟩
    simp [and_assoc,and_left_comm]
  rw [hset, Finset.card_product]

theorem rectangle_error_general
    (x y A B ε : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 ≤ ε)
    (hx : |x-A| ≤ ε) (hy : |y-B| ≤ ε) :
    |x*y-A*B| ≤ ε^2 + ε*(A+B) := by
  have hprod : |x-A| * |y-B| ≤ ε^2 := by
    nlinarith [mul_le_mul hx hy
      (abs_nonneg (y-B)) hε]
  have hsum :
    |(x-A)*(y-B) + A*(y-B) + B*(x-A)| ≤
      |x-A| * |y-B| + A*|y-B| + B*|x-A| := by
    calc
      _ ≤ |(x-A)*(y-B)| + |A*(y-B)| + |B*(x-A)| := by
        calc
          _ ≤ |(x-A)*(y-B) + A*(y-B)| + |B*(x-A)| := abs_add_le _ _
          _ ≤ _ := by
            simpa [add_comm,add_left_comm,add_assoc] using
              (add_le_add_right (abs_add_le ((x-A)*(y-B)) (A*(y-B)))
                (|B*(x-A)|))
      _ = _ := by
        rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg hB]
  have hbound :
      |x-A| * |y-B| + A*|y-B| + B*|x-A| ≤ ε^2 + ε*(A+B) := by
    nlinarith [hprod, mul_le_mul_of_nonneg_left hy hA,
      mul_le_mul_of_nonneg_left hx hB]
  have heq : x*y-A*B =
      (x-A)*(y-B) + A*(y-B) + B*(x-A) := by ring
  rw [heq]
  exact hsum.trans hbound
/-- The full source per-class lattice rectangle estimate on ANY
shifted natural box; the error has a universal explicit constant.
For dyadic [M,2M)×[N,2N), this is O(1+(M+N)/D). -/
theorem residueIntervalBoxCount_real_error
    (D a b A B C E : ℕ) (hD : 0<D) (hAB : A≤B) (hCE : C≤E) :
    |(residueIntervalBoxCount D a b A B C E : ℝ) -
      ((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/(D:ℝ)^2| ≤
      4 + 2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/(D:ℝ) := by
  let x : ℝ := residueIntervalCount D a A B
  let y : ℝ := residueIntervalCount D b C E
  let U : ℝ := ((B-A:ℕ):ℝ)/(D:ℝ)
  let V : ℝ := ((E-C:ℕ):ℝ)/(D:ℝ)
  have hU : 0≤U := by dsimp [U]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hx : |x-U| ≤ 2 :=
    residueIntervalCount_real_error D a A B hD hAB
  have hy : |y-V| ≤ 2 :=
    residueIntervalCount_real_error D b C E hD hCE
  have hh := rectangle_error_general x y U V 2 hU hV
    (by norm_num) hx hy
  have heq : x*y-U*V =
      (residueIntervalBoxCount D a b A B C E : ℝ) -
      ((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/(D:ℝ)^2 := by
    dsimp [x,y,U,V,residueIntervalBoxCount]
    push_cast
    ring
  have hrhs : (2:ℝ)^2 + 2*(U+V) =
      4 + 2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/(D:ℝ) := by
    dsimp [U,V]
    ring
  rw [heq,hrhs] at hh
  exact hh

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTUnits -/

section

set_option maxHeartbeats 2800000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- Literal ordered residue pairs (m,n) modulo D satisfying mn ≡ 1.
No squarefree assumption on D: repeated assignment factors survive. -/
def UnitPair (D : ℕ) [NeZero D] :=
    {p : ZMod D × ZMod D // p.1 * p.2 = 1}

noncomputable instance unitPairFintype (D : ℕ) [NeZero D] :
    Fintype (UnitPair D) := by
  classical
  unfold UnitPair
  infer_instance

def unitPairEquivUnits (D : ℕ) [NeZero D] :
    UnitPair D ≃ (ZMod D)ˣ where
  toFun p :=
    ⟨p.val.1, p.val.2, p.property, by simpa [mul_comm] using p.property⟩
  invFun u := ⟨(u.val, (u⁻¹).val), by simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rfl
  right_inv := by
    intro u
    apply Units.ext
    rfl

/-- Source congruence mn=1 mod D has exactly φ(D) residue pairs,
including all nonsquarefree and prime-power D>0. -/
theorem card_unit_pairs_eq_totient (D : ℕ) [NeZero D] :
    Fintype.card (UnitPair D) = D.totient := by
  classical
  calc
    _ = Fintype.card (ZMod D)ˣ :=
      Fintype.card_congr (unitPairEquivUnits D)
    _ = _ := ZMod.card_units_eq_totient D
/-- The arithmetic source convention uses one residue class of
each variable, not a "squarefree divisor" model. -/
theorem residue_mul_one_iff_is_unit (D : ℕ) [NeZero D]
    (x : ZMod D) :
    (∃ y : ZMod D, x * y = 1) ↔ IsUnit x := by
  constructor
  · rintro ⟨y,hy⟩
    exact isUnit_iff_exists_inv.mpr ⟨y,hy⟩
  · intro hx
    obtain ⟨u,rfl⟩ := hx
    exact ⟨(u⁻¹).val, by simp⟩

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTPrimeZero -/

section

set_option maxHeartbeats 3000000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

def NonzeroResidue (p : ℕ) [Fact p.Prime] :=
  {x : ZMod p // x ≠ 0}

noncomputable instance nonzeroResidueFintype (p : ℕ) [Fact p.Prime] :
    Fintype (NonzeroResidue p) := by
  classical
  unfold NonzeroResidue
  infer_instance

def nonzeroEquivUnits (p : ℕ) [Fact p.Prime] :
    NonzeroResidue p ≃ (ZMod p)ˣ where
  toFun x := Units.mk0 x.val x.property
  invFun x := ⟨x.val,x.ne_zero⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Units.ext
    rfl

/-- Genuine prime modulus: nonzero residues have exactly p-1 values. -/
theorem card_nonzero_residues (p : ℕ) [Fact p.Prime] :
    Fintype.card (NonzeroResidue p) = p - 1 := by
  classical
  exact (Fintype.card_congr (nonzeroEquivUnits p)).trans (ZMod.card_units p)
/-- Ordered modular pairs whose product is zero.
The restriction to prime p (a field) matters here. -/
def ZeroPair (p : ℕ) [Fact p.Prime] :=
   {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0}

noncomputable instance zeroPairFintype (p : ℕ) [Fact p.Prime] :
    Fintype (ZeroPair p) := by
  classical
  unfold ZeroPair
  infer_instance

/-- Partition zero-product pairs into x=0 with arbitrary y and
x≠0 forcing y=0. The second summand retains each nonzero x. -/
def zeroPairEquiv (p : ℕ) [Fact p.Prime] :
    ZeroPair p ≃ ZMod p ⊕ NonzeroResidue p where
  toFun xy := if h : xy.val.1 = 0
      then Sum.inl xy.val.2
      else Sum.inr ⟨xy.val.1,h⟩
  invFun z := match z with
    | Sum.inl y => ⟨(0,y),by simp⟩
    | Sum.inr x => ⟨(x.val,0),by simp⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,hxy⟩
    by_cases hx : x = 0
    · simp [hx] <;> rfl
    · have hy : y = 0 := (mul_eq_zero.mp hxy).resolve_left hx
      simp [hx,hy] <;> rfl
  right_inv := by
    intro z
    cases z with
    | inl y => simp
    | inr x => simp [x.property] <;> rfl

theorem card_zero_prime_pairs (p : ℕ) [Fact p.Prime] :
    Fintype.card (ZeroPair p) = 2*p - 1 := by
  classical
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  calc
    _ = Fintype.card (ZMod p ⊕ NonzeroResidue p) :=
      Fintype.card_congr (zeroPairEquiv p)
    _ = p + (p-1) := by
      rw [Fintype.card_sum, ZMod.card, card_nonzero_residues]
    _ = 2*p-1 := by omega

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTPrimeLocal -/

section

set_option maxHeartbeats 3200000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- At any genuine prime modulus the unit-product-one residue
pair count is p-1. No subtraction from a squarefree model occurs. -/
theorem card_one_prime_pairs (p : ℕ) [Fact p.Prime] :
    Fintype.card (UnitPair p) = p - 1 := by
  classical
  rw [card_unit_pairs_eq_totient]
  exact Nat.totient_prime (Fact.out : p.Prime)

theorem prime_zero_one_products_disjoint (p : ℕ) [Fact p.Prime]
    (xy : ZMod p × ZMod p) :
    ¬(xy.1 * xy.2 = 0 ∧ xy.1 * xy.2 = 1) := by
  rintro ⟨hz,ho⟩
  have hzero : (0 : ZMod p) = 1 := hz.symm.trans ho
  exact zero_ne_one hzero

/-- The exact bad CRT residue predicate in Section ex:box:
rough bad is xy=0, mask-banned bad is xy=1.
Both simultaneously means their disjoint union. -/
def LocalBadPair (p : ℕ) [Fact p.Prime] :=
  {xy : ZMod p × ZMod p //
    xy.1 * xy.2 = 0 ∨ xy.1 * xy.2 = 1}

noncomputable instance localBadPairFintype (p : ℕ) [Fact p.Prime] :
    Fintype (LocalBadPair p) := by
  classical
  unfold LocalBadPair
  infer_instance
def badPairEquiv (p : ℕ) [Fact p.Prime] :
    LocalBadPair p ≃ ZeroPair p ⊕ UnitPair p where
  toFun xy := if h : xy.val.1 * xy.val.2 = 0
    then Sum.inl ⟨xy.val,h⟩
    else Sum.inr ⟨xy.val,xy.property.resolve_left h⟩
  invFun s := match s with
    | Sum.inl z => ⟨z.val,Or.inl z.property⟩
    | Sum.inr o => ⟨o.val,Or.inr o.property⟩
  left_inv := by
    intro xy
    by_cases h : xy.val.1 * xy.val.2 = 0
    · simp [h] <;> rfl
    · simp [h] <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl z => simp [z.property] <;> rfl
    | inr o =>
      have hz : ¬o.val.1 * o.val.2 = 0 := by
        intro ho
        exact prime_zero_one_products_disjoint p o.val ⟨ho,o.property⟩
      simp [hz] <;> rfl

/-- The true union of the two disjoint modular bad events contains
exactly 3p-2 residue pairs; ℓ=2 is valid algebraically, though the
source sieve intentionally ranges over odd ℓ. -/
theorem card_local_bad_prime_pairs (p : ℕ) [Fact p.Prime] :
    Fintype.card (LocalBadPair p) = 3*p - 2 := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  calc
    _ = Fintype.card (ZeroPair p ⊕ UnitPair p) :=
      Fintype.card_congr (badPairEquiv p)
    _ = (2*p-1)+(p-1) := by
      rw [Fintype.card_sum, card_zero_prime_pairs, card_one_prime_pairs]
    _ = 3*p-2 := by omega

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTPairEquiv -/

section

set_option maxHeartbeats 3500000
namespace Green64Analytic.SourceCRT

/-- Literal CRT on two *ordered* residue pairs. The original assignment
modulus m may have repeated prime factors; only gcd(m,n)=1 is required. -/
def pairCRT (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m*n) × ZMod (m*n)) ≃
      (ZMod m × ZMod m) × (ZMod n × ZMod n) where
  toFun xy := (
      ((ZMod.chineseRemainder h xy.1).1,
       (ZMod.chineseRemainder h xy.2).1),
      ((ZMod.chineseRemainder h xy.1).2,
       (ZMod.chineseRemainder h xy.2).2))
  invFun ab := (
      (ZMod.chineseRemainder h).symm (ab.1.1,ab.2.1),
      (ZMod.chineseRemainder h).symm (ab.1.2,ab.2.2))
  left_inv := by
    intro xy
    apply Prod.ext
    · exact (ZMod.chineseRemainder h).left_inv xy.1
    · exact (ZMod.chineseRemainder h).left_inv xy.2
  right_inv := by
    intro ab
    apply Prod.ext
    · apply Prod.ext <;> simp
    · apply Prod.ext <;> simp
/-- CRT preserves exactly the two arithmetic product-one constraints. -/
theorem pairCRT_mul_one_iff
    (m n : ℕ) (h : m.Coprime n)
    (xy : ZMod (m*n) × ZMod (m*n)) :
    xy.1 * xy.2 = 1 ↔
      (pairCRT m n h xy).1.1 * (pairCRT m n h xy).1.2 = 1 ∧
      (pairCRT m n h xy).2.1 * (pairCRT m n h xy).2.2 = 1 := by
  change xy.1 * xy.2 = (1 : ZMod (m*n)) ↔ _
  constructor
  · intro hx
    have hm := congrArg (ZMod.chineseRemainder h) hx
    simpa [pairCRT, Prod.mul_def, Prod.ext_iff] using hm
  · intro hx
    apply (ZMod.chineseRemainder h).injective
    change (ZMod.chineseRemainder h) (xy.1*xy.2) =
       (ZMod.chineseRemainder h) 1
    simpa [pairCRT, Prod.mul_def, Prod.ext_iff] using hx

/-- Same exact residue pair map for product-zero conditions. -/
theorem pairCRT_mul_zero_iff
    (m n : ℕ) (h : m.Coprime n)
    (xy : ZMod (m*n) × ZMod (m*n)) :
    xy.1 * xy.2 = 0 ↔
      (pairCRT m n h xy).1.1 * (pairCRT m n h xy).1.2 = 0 ∧
      (pairCRT m n h xy).2.1 * (pairCRT m n h xy).2.2 = 0 := by
  constructor
  · intro hx
    have hm := congrArg (ZMod.chineseRemainder h) hx
    simpa [pairCRT, Prod.mul_def, Prod.ext_iff] using hm
  · intro hx
    apply (ZMod.chineseRemainder h).injective
    change (ZMod.chineseRemainder h) (xy.1*xy.2) =
       (ZMod.chineseRemainder h) 0
    simpa [pairCRT, Prod.mul_def, Prod.ext_iff] using hx

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTRestricted -/

section

set_option maxHeartbeats 4000000
namespace Green64Analytic.SourceCRT

/-- Actual residue-pair CRT fibre for mn≡1 mod assignment modulus
D1=m and an arbitrary independent local sieving condition P mod n.
Neither side asserts m squarefree or loses repeated assignment primes. -/
def CRTRestrictedPairs (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (P : (ZMod n × ZMod n) → Prop) :=
  {xy : ZMod (m*n) × ZMod (m*n) //
      ((pairCRT m n h xy).1.1 * (pairCRT m n h xy).1.2 = 1)
      ∧ P ((pairCRT m n h xy).2)}

noncomputable instance crtRestrictedFintype
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (P : (ZMod n × ZMod n) → Prop) :
    Fintype (CRTRestrictedPairs m n h P) := by
  classical
  unfold CRTRestrictedPairs
  infer_instance

/-- Exact CRT equivalence from the original modulus m*n to
a product of the *actual* unit-product pair modulo m and
the local sieving pair modulo n. -/
def crtRestrictedEquiv (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (P : ZMod n × ZMod n → Prop) :
    CRTRestrictedPairs m n h P ≃
      UnitPair m × {z : ZMod n × ZMod n // P z} where
  toFun xy := (⟨(pairCRT m n h xy.val).1,xy.property.1⟩,
               ⟨(pairCRT m n h xy.val).2,xy.property.2⟩)
  invFun xy := ⟨(pairCRT m n h).symm (xy.1.val,xy.2.val), by
    simpa using And.intro xy.1.property xy.2.property⟩
  left_inv := by
    intro xy
    apply Subtype.ext
    exact (pairCRT m n h).left_inv xy.val
  right_inv := by
    intro xy
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((pairCRT m n h).right_inv (xy.1.val,xy.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd ((pairCRT m n h).right_inv (xy.1.val,xy.2.val))

noncomputable instance localPredicateFintype (n : ℕ) [NeZero n]
    (P : ZMod n × ZMod n → Prop) :
    Fintype {z : ZMod n × ZMod n // P z} := by
  classical
  infer_instance

/-- Exact cardinality for an arbitrary coprime sieving modulus n and
ANY predicate P on pairs modulo n. This proves the φ(m) base density
without requiring m squarefree. -/
theorem card_restricted_crt_pairs
    (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (P : ZMod n × ZMod n → Prop) :
    Fintype.card (CRTRestrictedPairs m n h P) =
      m.totient * Fintype.card {z : ZMod n × ZMod n // P z} := by
  classical
  calc
    _ = Fintype.card (UnitPair m × {z : ZMod n × ZMod n // P z}) :=
      Fintype.card_congr (crtRestrictedEquiv m n h P)
    _ = _ := by
      rw [Fintype.card_prod, card_unit_pairs_eq_totient]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTBoxLocal -/

section

set_option maxHeartbeats 4500000
namespace Green64Analytic.SourceCRT

/-- Source ex:box exact product-one base modulus φ(D1) times
one bad zero residue condition at a coprime prime ℓ. -/
theorem cardinal_crt_rough_zero
    (D ℓ : ℕ) [NeZero D] [Fact ℓ.Prime]
    (h : D.Coprime ℓ) :
    Fintype.card (CRTRestrictedPairs D ℓ h
      (fun xy : ZMod ℓ × ZMod ℓ => xy.1*xy.2=0)) =
      D.totient*(2*ℓ-1) := by
  rw [card_restricted_crt_pairs]
  calc
    _ = D.totient * Fintype.card (ZeroPair ℓ) := by
      congr 1
      exact Fintype.card_congr (Equiv.refl _)
    _ = _ := by rw [card_zero_prime_pairs]

/-- Source ex:box exact product-one base modulus times each
independently banned product-one residue at ℓ. -/
theorem cardinal_crt_banned_one
    (D ℓ : ℕ) [NeZero D] [Fact ℓ.Prime]
    (h : D.Coprime ℓ) :
    Fintype.card (CRTRestrictedPairs D ℓ h
      (fun xy : ZMod ℓ × ZMod ℓ => xy.1*xy.2=1)) =
      D.totient*(ℓ-1) := by
  rw [card_restricted_crt_pairs]
  calc
    _ = D.totient * Fintype.card (UnitPair ℓ) := by
      congr 1
      exact Fintype.card_congr (Equiv.refl _)
    _ = _ := by rw [card_one_prime_pairs]
/-- When the source rough and banned conditions both apply at
the same prime ℓ, the two bad classes are disjoint and have
exactly 3ℓ−2 residue pairs. -/
theorem cardinal_crt_rough_and_banned
    (D ℓ : ℕ) [NeZero D] [Fact ℓ.Prime]
    (h : D.Coprime ℓ) :
    Fintype.card (CRTRestrictedPairs D ℓ h
      (fun xy : ZMod ℓ × ZMod ℓ =>
        xy.1*xy.2=0 ∨ xy.1*xy.2=1)) =
      D.totient*(3*ℓ-2) := by
  rw [card_restricted_crt_pairs]
  calc
    _ = D.totient * Fintype.card (LocalBadPair ℓ) := by
      congr 1
      exact Fintype.card_congr (Equiv.refl _)
    _ = _ := by rw [card_local_bad_prime_pairs]

/-- The actual original shift N_u=2u+1:
any assignment divisor D1|u forces the product mn≡1 mod D1.
No squarefreeness or assumption on primality of m,n is used. -/
theorem assignment_divisor_forces_pair_one
    (D u m n : ℕ) (hDu : D ∣ u)
    (hShift : m*n=2*u+1) :
    Nat.ModEq D (m*n) 1 := by
  rw [hShift]
  rcases hDu with ⟨k, rfl⟩
  change (2*(D*k)+1)%D = 1%D
  simp [Nat.add_mod, Nat.mul_mod, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm]
end Green64Analytic.SourceCRT

end

/-! ## SourceCRTLatticeAggregate -/

section

set_option maxHeartbeats 4500000
namespace Green64Analytic.SourceCRT

/-- The integer-box sum over an arbitrary fixed finite family of
distinct ZMod D residue-pair classes, including all CRT classes. -/
noncomputable def residueClassBoxSum (D : ℕ) [NeZero D]
    (S : Finset (ZMod D × ZMod D))
    (A B C E : ℕ) : ℝ :=
  ∑ ab ∈ S, (residueIntervalBoxCount D ab.1.val ab.2.val A B C E : ℝ)

/-- Sum the true per-residue box errors, retaining the number
of surviving residue pairs as a factor. The source proof needs
this before summing over assignments and squarefree sieve d. -/
theorem residueClassBoxSum_error
    (D : ℕ) [NeZero D]
    (S : Finset (ZMod D × ZMod D))
    (A B C E : ℕ) (hAB : A≤B) (hCE : C≤E) :
    |residueClassBoxSum D S A B C E -
      (S.card : ℝ) *
         (((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/(D:ℝ)^2)| ≤
      (S.card:ℝ) *
        (4+2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/(D:ℝ)) := by
  let k : ℝ := ((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/(D:ℝ)^2
  let Err : ℝ := 4+2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/(D:ℝ)
  have hD : 0<D := NeZero.pos D
  have hBound (ab : ZMod D × ZMod D) :
      |(residueIntervalBoxCount D ab.1.val ab.2.val A B C E:ℝ)-k| ≤ Err :=
    residueIntervalBoxCount_real_error D ab.1.val ab.2.val
      A B C E hD hAB hCE
  have hOne :
      (∑ ab ∈ S, |(residueIntervalBoxCount D ab.1.val ab.2.val A B C E:ℝ)-k|) ≤
      (S.card:ℝ)*Err := by
    calc
      _ ≤ ∑ ab ∈ S, Err := Finset.sum_le_sum
        (fun ab _ => hBound ab)
      _ = _ := by simp
  calc
    _ = |∑ ab ∈ S,
        ((residueIntervalBoxCount D ab.1.val ab.2.val A B C E:ℝ)-k)| := by
      unfold residueClassBoxSum
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ ab ∈ S,
          |(residueIntervalBoxCount D ab.1.val ab.2.val A B C E:ℝ)-k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := hOne

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTMultiplicative -/

section

set_option maxHeartbeats 3600000
namespace Green64Analytic.SourceCRT

/-- Exact independent local residue-pair predicates after CRT.
The two moduli may themselves contain repeated prime factors, but
must be coprime, exactly as in the original source product D1*d. -/
def CRTLocalConjunction
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (Pm : ZMod m × ZMod m → Prop)
    (Pn : ZMod n × ZMod n → Prop) :=
  {ab : ZMod (m*n) × ZMod (m*n) //
     Pm ((pairCRT m n h ab).1) ∧
     Pn ((pairCRT m n h ab).2)}

noncomputable instance crtLocalConjunctionFintype
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (Pm : ZMod m × ZMod m → Prop)
    (Pn : ZMod n × ZMod n → Prop) :
    Fintype (CRTLocalConjunction m n h Pm Pn) := by
  classical
  unfold CRTLocalConjunction
  infer_instance

/-- The cardinal-multiplicativity equivalence is explicitly built
over the *original CRT bijection*, not an informal product heuristic. -/
def crtLocalConjunctionEquiv
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (Pm : ZMod m × ZMod m → Prop)
    (Pn : ZMod n × ZMod n → Prop) :
    CRTLocalConjunction m n h Pm Pn ≃
      {ab : ZMod m × ZMod m // Pm ab} ×
      {ab : ZMod n × ZMod n // Pn ab} where
  toFun ab :=
    (⟨(pairCRT m n h ab.val).1,ab.property.1⟩,
     ⟨(pairCRT m n h ab.val).2,ab.property.2⟩)
  invFun ab := ⟨(pairCRT m n h).symm (ab.1.val,ab.2.val),
    by simpa using And.intro ab.1.property ab.2.property⟩
  left_inv := by
    intro ab
    apply Subtype.ext
    exact (pairCRT m n h).left_inv ab.val
  right_inv := by
    intro ab
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        ((pairCRT m n h).right_inv (ab.1.val,ab.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd
        ((pairCRT m n h).right_inv (ab.1.val,ab.2.val))

/-- Exact CRT multiplicativity of local pair counts, with no
squarefree assumption except pairwise coprimality of moduli. -/
theorem card_crt_local_conjunction
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (Pm : ZMod m × ZMod m → Prop)
    (Pn : ZMod n × ZMod n → Prop) :
    Fintype.card (CRTLocalConjunction m n h Pm Pn) =
      Fintype.card {ab : ZMod m × ZMod m // Pm ab} *
      Fintype.card {ab : ZMod n × ZMod n // Pn ab} := by
  classical
  calc
    _ = Fintype.card
      ({ab : ZMod m × ZMod m // Pm ab} ×
       {ab : ZMod n × ZMod n // Pn ab}) :=
      Fintype.card_congr (crtLocalConjunctionEquiv m n h Pm Pn)
    _ = _ := by rw [Fintype.card_prod]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTTwoPrimes -/

section

set_option maxHeartbeats 3800000
namespace Green64Analytic.SourceCRT

/-- Both local disjoint residue events at each of two different
sieving primes. CRT gives exactly ν(p)ν(q), not a heuristic density. -/
theorem cardinal_two_bad_primes
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) :
    Fintype.card (CRTLocalConjunction p q hpq
      (fun xy : ZMod p × ZMod p =>
        xy.1*xy.2=0 ∨ xy.1*xy.2=1)
      (fun xy : ZMod q × ZMod q =>
        xy.1*xy.2=0 ∨ xy.1*xy.2=1)) =
      (3*p-2)*(3*q-2) := by
  rw [card_crt_local_conjunction]
  have hp : Fintype.card {xy : ZMod p × ZMod p //
      xy.1*xy.2=0 ∨ xy.1*xy.2=1} =
      Fintype.card (LocalBadPair p) :=
    Fintype.card_congr (Equiv.refl _)
  have hq : Fintype.card {xy : ZMod q × ZMod q //
      xy.1*xy.2=0 ∨ xy.1*xy.2=1} =
      Fintype.card (LocalBadPair q) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hp,hq,card_local_bad_prime_pairs,card_local_bad_prime_pairs]

/-- Original ex:box CRT count φ(D1)ν(d) when d is the squarefree
product of two distinct primes. D1 is ANY positive assignment
modulus coprime to pq, including all prime powers and repetitions. -/
theorem cardinal_assignment_two_bad_primes
    (D p q : ℕ) [NeZero D] [Fact p.Prime] [Fact q.Prime]
    (hpq : p.Coprime q) (hD : D.Coprime (p*q)) :
    Fintype.card (CRTRestrictedPairs D (p*q) hD
      (fun xy : ZMod (p*q) × ZMod (p*q) =>
        ((pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 0 ∨
         (pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 1) ∧
        ((pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 0 ∨
         (pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 1))) =
      D.totient * ((3*p-2)*(3*q-2)) := by
  rw [card_restricted_crt_pairs]
  have hcount : Fintype.card
      {xy : ZMod (p*q) × ZMod (p*q) //
        ((pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 0 ∨
         (pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 1) ∧
        ((pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 0 ∨
         (pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 1)} =
      (3*p-2)*(3*q-2) := by
    have hc : Fintype.card
      {xy : ZMod (p*q) × ZMod (p*q) //
        ((pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 0 ∨
         (pairCRT p q hpq xy).1.1 *
           (pairCRT p q hpq xy).1.2 = 1) ∧
        ((pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 0 ∨
         (pairCRT p q hpq xy).2.1 *
           (pairCRT p q hpq xy).2.2 = 1)} =
       Fintype.card (CRTLocalConjunction p q hpq
         (fun xy : ZMod p × ZMod p =>
           xy.1*xy.2=0 ∨ xy.1*xy.2=1)
         (fun xy : ZMod q × ZMod q =>
           xy.1*xy.2=0 ∨ xy.1*xy.2=1)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [hc]
    exact cardinal_two_bad_primes p q hpq
  rw [hcount]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTLocalDensity -/

section

set_option maxHeartbeats 3600000
namespace Green64Analytic.SourceCRT

/-- Exactly the source local bad-class count ν(ℓ) at odd prime ℓ:
zero product for roughness, product one for the independent mask.
The flags may both hold, and events are disjoint. -/
def localNu (ℓ : ℕ) (rough banned : Bool) : ℕ :=
    (if rough then 2*ℓ-1 else 0) +
    (if banned then ℓ-1 else 0)

theorem localNu_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (rough banned : Bool) :
    localNu ℓ rough banned ≤ 3*ℓ-2 := by
  cases rough <;> cases banned <;>
    simp [localNu] <;> omega

/-- The original source sieve bound g(ℓ)≤7/9 for all odd primes.
The restriction ℓ≥3 is essential: simultaneous bad events exhaust
all four pairs modulo 2. -/
theorem local_density_le_seven_ninths (ℓ : ℕ)
    (hℓ : 3 ≤ ℓ) (rough banned : Bool) :
    (localNu ℓ rough banned : ℝ)/(ℓ:ℝ)^2 ≤ 7/9 := by
  have hbound := localNu_le ℓ (by omega) rough banned
  have hcast : (localNu ℓ rough banned : ℝ) ≤
      3*(ℓ:ℝ)-2 := by
    have hb : 2 ≤ 3*ℓ := by omega
    exact_mod_cast hbound
  have hR : (3:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hmul : 0 ≤ ((ℓ:ℝ)-3)*(7*(ℓ:ℝ)-6) :=
    mul_nonneg (by linarith) (by linarith)
  have hpow : 0 < ((ℓ:ℝ)^2) := by positivity
  apply (div_le_iff₀ hpow).mpr
  nlinarith

/-- This is the second source sieve density hypothesis g(ℓ)≤3/ℓ,
valid uniformly in the mask and independent of assignments. -/
theorem local_density_le_three_div (ℓ : ℕ)
    (hℓ : 3 ≤ ℓ) (rough banned : Bool) :
    (localNu ℓ rough banned : ℝ)/(ℓ:ℝ)^2 ≤ 3/(ℓ:ℝ) := by
  have hbound := localNu_le ℓ (by omega) rough banned
  have hcast : (localNu ℓ rough banned : ℝ) ≤
      3*(ℓ:ℝ)-2 := by
    have hb : 2 ≤ 3*ℓ := by omega
    exact_mod_cast hbound
  have hR : (0:ℝ) < ℓ := by exact_mod_cast (by omega : 0<ℓ)
  have hpow : 0 < ((ℓ:ℝ)^2) := by positivity
  apply (div_le_iff₀ hpow).mpr
  field_simp
  nlinarith

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTFlagged -/

section

set_option maxHeartbeats 4500000
namespace Green64Analytic.SourceCRT

/-- Exact bad-pair predicate with the literal source rough/banned flags.
The flags may coincide: 0 and 1 are distinct residues. -/
def FlaggedBadPair (p : ℕ) [Fact p.Prime]
    (rough banned : Bool) :=
  {xy : ZMod p × ZMod p //
     (rough = true ∧ xy.1*xy.2=0) ∨
     (banned = true ∧ xy.1*xy.2=1)}

noncomputable instance flaggedBadFintype (p : ℕ) [Fact p.Prime]
    (rough banned : Bool) : Fintype (FlaggedBadPair p rough banned) := by
  classical
  unfold FlaggedBadPair
  infer_instance

/-- Every local mask gives exactly the source number ν(ℓ),
not just an upper bound or heuristic residue density. -/
theorem cardinal_flagged_prime_pairs
    (p : ℕ) [Fact p.Prime] (rough banned : Bool) :
    Fintype.card (FlaggedBadPair p rough banned) =
      localNu p rough banned := by
  classical
  cases rough <;> cases banned
  · haveI : IsEmpty (FlaggedBadPair p false false) := ⟨by
      rintro ⟨xy, hxy⟩
      simp at hxy⟩
    simp [localNu, Fintype.card_eq_zero]
  · change Fintype.card (FlaggedBadPair p false true) = _
    have hc : Fintype.card (FlaggedBadPair p false true) =
        Fintype.card (UnitPair p) := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _)
        (by intro xy; simp [FlaggedBadPair,UnitPair])
    rw [hc,card_one_prime_pairs]
    simp [localNu]
  · have hc : Fintype.card (FlaggedBadPair p true false) =
        Fintype.card (ZeroPair p) := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _)
        (by intro xy; simp [FlaggedBadPair,ZeroPair])
    rw [hc,card_zero_prime_pairs]
    simp [localNu]
  · have hc : Fintype.card (FlaggedBadPair p true true) =
        Fintype.card (LocalBadPair p) := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _)
        (by intro xy; simp [FlaggedBadPair,LocalBadPair])
    rw [hc,card_local_bad_prime_pairs]
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    simp [localNu] <;> omega
/-- The exact Section ex:box local bad-density bound is now a
statement about the actual cardinal of modular pair classes,
uniformly over all finite masks. -/
theorem cardinal_flagged_density_bound
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (rough banned : Bool) :
    (Fintype.card (FlaggedBadPair p rough banned) : ℝ)/(p:ℝ)^2 ≤
      7/9 ∧
    (Fintype.card (FlaggedBadPair p rough banned) : ℝ)/(p:ℝ)^2 ≤
      3/(p:ℝ) := by
  rw [cardinal_flagged_prime_pairs]
  exact ⟨local_density_le_seven_ninths p hp rough banned,
    local_density_le_three_div p hp rough banned⟩

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTAllPrimes -/

section

set_option maxHeartbeats 4200000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Full, source-relevant CRT on both ordered coordinates for an
arbitrary FINITE family of mutually coprime local moduli. -/
noncomputable def pairCRTAll (q : ι → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) :
    (ZMod (∏ i, q i) × ZMod (∏ i, q i)) ≃
      ((i : ι) → ZMod (q i) × ZMod (q i)) where
  toFun xy i :=
    ((ZMod.prodEquivPi q hc xy.1) i,
     (ZMod.prodEquivPi q hc xy.2) i)
  invFun fam :=
    ((ZMod.prodEquivPi q hc).symm (fun i => (fam i).1),
     (ZMod.prodEquivPi q hc).symm (fun i => (fam i).2))
  left_inv := by
    intro xy
    apply Prod.ext <;>
      simp only [RingEquiv.symm_apply_apply]
  right_inv := by
    intro fam
    funext i
    apply Prod.ext <;>
      simp only [RingEquiv.apply_symm_apply]
/-- Original per-prime pair events, uniform in two source masks. -/
def localFlagPredicate (p : ℕ)
    (rough banned : Bool) (xy : ZMod p × ZMod p) : Prop :=
  (rough = true ∧ xy.1 * xy.2 = 0) ∨
    (banned = true ∧ xy.1 * xy.2 = 1)

/-- The global CRT bad-pair set: it is a genuine subset of the
original product-modulus ZMod, not a synthetic independent model. -/
def CRTAllFlaggedPairs (q : ι → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (rough banned : ι → Bool) :=
  {xy : ZMod (∏ i, q i) × ZMod (∏ i, q i) //
    ∀ i : ι, localFlagPredicate (q i) (rough i) (banned i)
       ((pairCRTAll q hc xy) i)}

noncomputable instance crtAllFlaggedFintype
    (q : ι → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (rough banned : ι → Bool)
    [NeZero (∏ i, q i)] :
    Fintype (CRTAllFlaggedPairs q hc rough banned) := by
  classical
  unfold CRTAllFlaggedPairs
  infer_instance
/-- Global flagged pairs are in exact, explicit bijection with
ALL local flagged pairs: independent products in the sense of CRT. -/
noncomputable def crtAllFlaggedEquiv
    (q : ι → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (rough banned : ι → Bool)
    [NeZero (∏ i, q i)] :
    CRTAllFlaggedPairs q hc rough banned ≃
      ((i : ι) → {xy : ZMod (q i) × ZMod (q i) //
         localFlagPredicate (q i) (rough i) (banned i) xy}) where
  toFun x i :=
    ⟨(pairCRTAll q hc x.val) i, x.property i⟩
  invFun fam :=
    ⟨(pairCRTAll q hc).symm (fun i => (fam i).val), by
       intro i
       simpa only [(pairCRTAll q hc).apply_symm_apply] using (fam i).property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (pairCRTAll q hc).left_inv x.val
  right_inv := by
    intro fam
    funext i
    apply Subtype.ext
    exact congrArg (fun f => f i)
      ((pairCRTAll q hc).right_inv (fun i => (fam i).val))

/-- Prime-local density product exactly, for any number of distinct
prime moduli and any independent rough/banned Boolean masks.
No squarefree assumption is hidden: the product modulus is explicit
and CRT coprimality is the only modular hypothesis. -/
theorem cardinal_all_flagged_pairs (q : ι → ℕ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hprime : ∀ i, (q i).Prime)
    (rough banned : ι → Bool) :
    Nat.card (CRTAllFlaggedPairs q hc rough banned) =
      ∏ i : ι, localNu (q i) (rough i) (banned i) := by
  have hnonzero : (∏ i : ι, q i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (hprime i).ne_zero
  letI : NeZero (∏ i : ι, q i) := ⟨hnonzero⟩
  letI : ∀ i : ι, NeZero (q i) := fun i => ⟨(hprime i).ne_zero⟩
  classical
  calc
    _ = Fintype.card (CRTAllFlaggedPairs q hc rough banned) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card
          ((i : ι) → {xy : ZMod (q i) × ZMod (q i) //
            localFlagPredicate (q i) (rough i) (banned i) xy}) :=
      Fintype.card_congr (crtAllFlaggedEquiv q hc rough banned)
    _ = ∏ i : ι, Fintype.card
          {xy : ZMod (q i) × ZMod (q i) //
            localFlagPredicate (q i) (rough i) (banned i) xy} := by
      rw [Fintype.card_pi]
    _ = ∏ i : ι, localNu (q i) (rough i) (banned i) := by
      apply Finset.prod_congr rfl
      intro i _
      letI : Fact (q i).Prime := ⟨hprime i⟩
      calc
        _ = Fintype.card (FlaggedBadPair (q i) (rough i) (banned i)) :=
          Fintype.card_congr
            (Equiv.subtypeEquiv (Equiv.refl _) (by intro xy; rfl))
        _ = _ := cardinal_flagged_prime_pairs (q i) (rough i) (banned i)

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTAllSquarefree -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- An arbitrary squarefree prime-factor FINSET has genuine,
pairwise coprime residue moduli. No bound on the cardinality. -/
theorem primeFamilyPairwise (d : ℕ) :
    Pairwise (fun (p q : d.primeFactors) => p.val.Coprime q.val) := by
  intro p q hpq
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hq := Nat.prime_of_mem_primeFactors q.property
  apply (Nat.coprime_primes hp hq).mpr
  intro h
  exact hpq (Subtype.ext h)

/-- The full product of prime factors equals d exactly when d is
squarefree, including the empty prime family for d=1. -/
theorem squarefreePrimeFamilyModulus
    (d : ℕ) (hd : Squarefree d) :
    (∏ p : d.primeFactors, (p : ℕ)) = d := by
  calc
    _ = ∏ p ∈ d.primeFactors, p :=
      (Finset.prod_subtype d.primeFactors (fun p => Iff.rfl)
        (fun p : ℕ => p)).symm
    _ = d := Nat.prod_primeFactors_of_squarefree hd
/-- Literal excluded residue pairs modulo the prime-factor
product of a squarefree d. Each local flag is indexed by the
ACTUAL arithmetic prime p; the CRT lift is a genuine ZMod map. -/
def squarefreeFlaggedPairs (d : ℕ)
    (rough banned : ℕ → Bool) :=
  CRTAllFlaggedPairs
    (fun p : d.primeFactors => (p : ℕ))
    (primeFamilyPairwise d)
    (fun p => rough (p : ℕ))
    (fun p => banned (p : ℕ))

/-- Exactly the original sieve ν(d) product, with local flags that
can overlap, and no restriction to at most two prime factors. -/
theorem squarefreeFlaggedPairs_count (d : ℕ)
    (hd : Squarefree d) (rough banned : ℕ → Bool) :
    Nat.card (squarefreeFlaggedPairs d rough banned) =
      ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  have hprime (p : d.primeFactors) : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.property
  have h := cardinal_all_flagged_pairs
    (q := fun p : d.primeFactors => (p : ℕ))
    (primeFamilyPairwise d) hprime
    (fun p => rough (p : ℕ)) (fun p => banned (p : ℕ))
  change Nat.card (squarefreeFlaggedPairs d rough banned) = _ at h
  calc
    _ = ∏ p : d.primeFactors, localNu p.val (rough p.val) (banned p.val) := h
    _ = ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) :=
      (Finset.prod_subtype d.primeFactors (fun _ => Iff.rfl)
        (fun p : ℕ => localNu p (rough p) (banned p))).symm

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTAllAssignment -/

section

set_option maxHeartbeats 5000000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- The exact original CRT sieve type for an arbitrary positive
assignment D and arbitrary squarefree d coprime to D.  D may have
repeated prime factors.  The source modulus is D*d literally
after the checked equality ∏_{p|d}p=d. -/
def squarefreeAssignmentPairs
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) : Type :=
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero (∏ p : d.primeFactors, (p : ℕ)) :=
    ⟨by rw [squarefreePrimeFamilyModulus d hd]
        exact hd.ne_zero⟩
  CRTRestrictedPairs D (∏ p : d.primeFactors, (p : ℕ))
    (by rw [squarefreePrimeFamilyModulus d hd]; exact hC)
    (fun xy => ∀ p : d.primeFactors,
       localFlagPredicate (p : ℕ) (rough p.val) (banned p.val)
         ((pairCRTAll (fun q : d.primeFactors => (q : ℕ))
           (primeFamilyPairwise d) xy) p))
/-- The key φ(D)*ν(d) count for every source squarefree d and
arbitrary nonsquarefree D coprime to d; all local flags survive. -/
theorem squarefreeAssignmentPairs_card
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    Nat.card (squarefreeAssignmentPairs D d hD hd hC rough banned) =
      D.totient *
        ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  let q : d.primeFactors → ℕ := fun p => (p : ℕ)
  have hprod : (∏ p : d.primeFactors, (p : ℕ)) = d :=
    squarefreePrimeFamilyModulus d hd
  have hqzero : (∏ p : d.primeFactors, (p : ℕ)) ≠ 0 := by
    rw [hprod]
    exact hd.ne_zero
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero (∏ p : d.primeFactors, (p : ℕ)) := ⟨hqzero⟩
  have hc : D.Coprime (∏ p : d.primeFactors, (p : ℕ)) := by
    rw [hprod]
    exact hC
  let Q : ZMod (∏ p : d.primeFactors, (p : ℕ)) ×
      ZMod (∏ p : d.primeFactors, (p : ℕ)) → Prop :=
    fun xy => ∀ p : d.primeFactors,
      localFlagPredicate p.val (rough p.val) (banned p.val)
        ((pairCRTAll (fun q : d.primeFactors => (q : ℕ))
          (primeFamilyPairwise d) xy) p)
  have hcardCRT := card_restricted_crt_pairs D
      (∏ p : d.primeFactors, (p : ℕ)) hc Q
  letI : Fintype (squarefreeFlaggedPairs d rough banned) := by
    unfold squarefreeFlaggedPairs
    infer_instance
  have hcardLocal :
      Fintype.card {xy : ZMod (∏ p : d.primeFactors, (p : ℕ)) ×
                           ZMod (∏ p : d.primeFactors, (p : ℕ)) // Q xy} =
      Nat.card (squarefreeFlaggedPairs d rough banned) := by
    have hnat :
        Nat.card (squarefreeFlaggedPairs d rough banned) =
        Fintype.card (squarefreeFlaggedPairs d rough banned) :=
      Nat.card_eq_fintype_card
    have hcongr : Fintype.card {xy : ZMod (∏ p : d.primeFactors, (p : ℕ)) ×
                                     ZMod (∏ p : d.primeFactors, (p : ℕ)) // Q xy} =
                      Fintype.card (squarefreeFlaggedPairs d rough banned) :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
        (by intro xy; rfl))
    exact hcongr.trans hnat.symm
  have hcardNat :
      Nat.card (squarefreeAssignmentPairs D d hD hd hC rough banned) =
      Fintype.card (CRTRestrictedPairs D
        (∏ p : d.primeFactors, (p : ℕ)) hc Q) := by
    change Nat.card (CRTRestrictedPairs D
      (∏ p : d.primeFactors, (p : ℕ)) hc Q) = _
    exact Nat.card_eq_fintype_card
  calc
    _ = Fintype.card (CRTRestrictedPairs D
        (∏ p : d.primeFactors, (p : ℕ)) hc Q) := hcardNat
    _ = D.totient * Fintype.card
          {xy : ZMod (∏ p : d.primeFactors, (p : ℕ)) ×
                 ZMod (∏ p : d.primeFactors, (p : ℕ)) // Q xy} :=
      hcardCRT
    _ = D.totient * Nat.card (squarefreeFlaggedPairs d rough banned) := by
      rw [hcardLocal]
    _ = _ := by rw [squarefreeFlaggedPairs_count d hd rough banned]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTActualModulus -/

section

set_option maxHeartbeats 5000000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- The residue-pair transport identifies the verified prime-factor
product modulus with EXACTLY ZMod d for squarefree d. -/
noncomputable def squarefreePairToPrimeProduct (d : ℕ)
    (hd : Squarefree d) :
    (ZMod d × ZMod d) ≃
      (ZMod (∏ p : d.primeFactors, (p : ℕ)) ×
       ZMod (∏ p : d.primeFactors, (p : ℕ))) :=
  Equiv.prodCongr
    (ZMod.ringEquivCongr
      (squarefreePrimeFamilyModulus d hd).symm).toEquiv
    (ZMod.ringEquivCongr
      (squarefreePrimeFamilyModulus d hd).symm).toEquiv

/-- Source bad classes as an actual predicate modulo d, not just
its formal prime-factor product. -/
def squarefreeBadOnD (d : ℕ) (hd : Squarefree d)
    (rough banned : ℕ → Bool) (xy : ZMod d × ZMod d) : Prop :=
  ∀ p : d.primeFactors,
    localFlagPredicate p.val (rough p.val) (banned p.val)
      ((pairCRTAll (fun q : d.primeFactors => (q : ℕ))
        (primeFamilyPairwise d)
        (squarefreePairToPrimeProduct d hd xy)) p)
/-- The modular pair count for every squarefree d exactly equals
the product of its original prime-by-prime forbidden classes. -/
theorem squarefreeBadOnD_card
    (d : ℕ) (hd : Squarefree d)
    (rough banned : ℕ → Bool) :
    Nat.card {xy : ZMod d × ZMod d //
      squarefreeBadOnD d hd rough banned xy} =
      ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  have htransport :
      Nat.card {xy : ZMod d × ZMod d //
        squarefreeBadOnD d hd rough banned xy} =
        Nat.card (squarefreeFlaggedPairs d rough banned) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (squarefreePairToPrimeProduct d hd)
      (by intro xy; rfl)
  exact htransport.trans (squarefreeFlaggedPairs_count d hd rough banned)

/-- The actual source assignment CRT object lives on ZMod(D*d),
with a true product-one constraint modulo D and all local
forbidden pair predicates modulo d. D may contain prime powers. -/
def sourceActualAssignmentPairs
    (D d : ℕ) (hC : D.Coprime d)
    (hd : Squarefree d) (rough banned : ℕ → Bool) :=
  {xy : ZMod (D*d) × ZMod (D*d) //
    (pairCRT D d hC xy).1.1 * (pairCRT D d hC xy).1.2 = 1 ∧
    squarefreeBadOnD d hd rough banned ((pairCRT D d hC xy).2)}
/-- Full original-source phi(D)*nu(d) CRT theorem for arbitrary
squarefree d and arbitrary positive, potentially nonsquarefree
assignment D. The modulus is literally D*d, not an opaque model. -/
theorem sourceActualAssignmentPairs_card
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    Nat.card (sourceActualAssignmentPairs D d hC hd rough banned) =
      D.totient *
        ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero d := ⟨hd.ne_zero⟩
  let P : ZMod d × ZMod d → Prop :=
    squarefreeBadOnD d hd rough banned
  have hCRT :=
    card_restricted_crt_pairs D d hC P
  have hSource :
      Nat.card (sourceActualAssignmentPairs D d hC hd rough banned) =
        Nat.card (CRTRestrictedPairs D d hC P) :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (by intro xy; rfl))
  have hLocal :
      Nat.card {xy : ZMod d × ZMod d // P xy} =
      ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) :=
    squarefreeBadOnD_card d hd rough banned
  calc
    _ = Nat.card (CRTRestrictedPairs D d hC P) := hSource
    _ = Fintype.card (CRTRestrictedPairs D d hC P) :=
      Nat.card_eq_fintype_card
    _ = D.totient * Fintype.card {xy : ZMod d × ZMod d // P xy} :=
      hCRT
    _ = D.totient * Nat.card {xy : ZMod d × ZMod d // P xy} := by
      rw [Nat.card_eq_fintype_card]
    _ = _ := by rw [hLocal]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTActualBox -/

section

set_option maxHeartbeats 5000000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- The exact residue-class set, not a proxy, for the source CRT
modulus D*d and arbitrary mixed rough/banned masks. -/
noncomputable def sourceActualResidueClasses
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    Finset (ZMod (D*d) × ZMod (D*d)) := by
  letI : NeZero (D*d) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hD (Nat.pos_of_ne_zero hd.ne_zero))⟩
  classical
  exact Finset.univ.filter (fun xy =>
    (pairCRT D d hC xy).1.1 * (pairCRT D d hC xy).1.2 = 1 ∧
    squarefreeBadOnD d hd rough banned ((pairCRT D d hC xy).2))

/-- Cardinal of the literal source residue set is φ(D)*ν(d), not
only abstract equivalence cardinality. -/
theorem sourceActualResidueClasses_card
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    (sourceActualResidueClasses D d hD hd hC rough banned).card =
      D.totient *
        ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  letI : NeZero (D*d) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hD (Nat.pos_of_ne_zero hd.ne_zero))⟩
  classical
  letI : Fintype (sourceActualAssignmentPairs D d hC hd rough banned) := by
    unfold sourceActualAssignmentPairs
    infer_instance
  have hcount : (sourceActualResidueClasses D d hD hd hC rough banned).card =
      Nat.card (sourceActualAssignmentPairs D d hC hd rough banned) := by
    have hsub :
        (sourceActualResidueClasses D d hD hd hC rough banned).card =
          Fintype.card (sourceActualAssignmentPairs D d hC hd rough banned) := by
      simpa only [sourceActualResidueClasses, sourceActualAssignmentPairs] using
        (Fintype.card_subtype (fun xy : ZMod (D*d) × ZMod (D*d) =>
          (pairCRT D d hC xy).1.1 * (pairCRT D d hC xy).1.2 = 1 ∧
          squarefreeBadOnD d hd rough banned ((pairCRT D d hC xy).2))).symm
    exact hsub.trans Nat.card_eq_fintype_card.symm
  exact hcount.trans
    (sourceActualAssignmentPairs_card D d hD hd hC rough banned)

/-- Literal sum of integer lattice-box counts over actual source
CRT classes modulo D*d, with the positivity instance justified
from D>0 and squarefree d. -/
noncomputable def sourceActualResidueBoxCount
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool)
    (A B C E : ℕ) : ℝ := by
  letI : NeZero (D*d) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hD (Nat.pos_of_ne_zero hd.ne_zero))⟩
  exact residueClassBoxSum (D*d)
    (sourceActualResidueClasses D d hD hd hC rough banned) A B C E

/-- Error in a literal integer box, summing exactly the source
CRT residue classes. No restriction that D be squarefree. -/
theorem sourceActualResidueBox_error
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    |sourceActualResidueBoxCount D d hD hd hC rough banned A B C E -
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
         (((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/((D*d:ℕ):ℝ)^2)| ≤
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (4+2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/((D*d:ℕ):ℝ)) := by
  have hpos : 0 < D*d :=
    Nat.mul_pos hD (Nat.pos_of_ne_zero hd.ne_zero)
  letI : NeZero (D*d) := ⟨Nat.ne_of_gt hpos⟩
  have hcount := sourceActualResidueClasses_card D d hD hd hC rough banned
  change |residueClassBoxSum (D*d)
      (sourceActualResidueClasses D d hD hd hC rough banned) A B C E - _| ≤ _
  have hbox := residueClassBoxSum_error (D*d)
    (sourceActualResidueClasses D d hD hd hC rough banned)
    A B C E hAB hCE
  rw [hcount] at hbox
  simpa only [Nat.cast_mul] using hbox

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTIntegerFilter -/

section

set_option maxHeartbeats 4500000
namespace Green64Analytic.SourceCRT

/-- Sum the cardinalities of all disjoint fibers exactly, for
an arbitrary map into a finite family of target residue classes. -/
theorem card_fiber_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (S : Finset β) (f : α → β) :
    (∑ y ∈ S, (s.filter (fun x => f x = y)).card) =
      (s.filter (fun x => f x ∈ S)).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]

/-- Literal congruence to an element of ZMod D means precisely
the equality to that residue class, with D>0. -/
theorem modEq_val_iff_cast_eq (D n : ℕ) [NeZero D] (v : ZMod D) :
    Nat.ModEq D n v.val ↔ (n : ZMod D) = v := by
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.natCast_eq_natCast_iff n v.val D).symm
/-- The actual sum of fixed-residue lattice counts is IDENTICAL
to the integer pair count satisfying membership in the union
of those original modular residue classes. No overlap is possible. -/
theorem residueClassBoxSum_eq_integer_filter
    (D A B C E : ℕ) [NeZero D]
    (S : Finset (ZMod D × ZMod D)) :
    residueClassBoxSum D S A B C E =
      (((Finset.Ico A B) ×ˢ (Finset.Ico C E)).filter
        (fun ij : ℕ × ℕ =>
           ((ij.1 : ZMod D), (ij.2 : ZMod D)) ∈ S)).card := by
  classical
  let R : Finset (ℕ × ℕ) := Finset.Ico A B ×ˢ Finset.Ico C E
  let f : ℕ × ℕ → ZMod D × ZMod D :=
    fun ij => ((ij.1 : ZMod D), (ij.2 : ZMod D))
  have hf (ab : ZMod D × ZMod D) :
      residueIntervalBoxCount D ab.1.val ab.2.val A B C E =
      (R.filter (fun ij => f ij = ab)).card := by
    rw [residueIntervalBoxCount_eq_filter]
    congr 1
    ext ij
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr,ha,hb⟩
      refine ⟨hr,?_⟩
      apply Prod.ext
      · exact (modEq_val_iff_cast_eq D ij.1 ab.1).mp ha
      · exact (modEq_val_iff_cast_eq D ij.2 ab.2).mp hb
    · rintro ⟨hr,heq⟩
      have ha : (ij.1 : ZMod D) = ab.1 := congrArg Prod.fst heq
      have hb : (ij.2 : ZMod D) = ab.2 := congrArg Prod.snd heq
      exact ⟨hr,
        (modEq_val_iff_cast_eq D ij.1 ab.1).mpr ha,
        (modEq_val_iff_cast_eq D ij.2 ab.2).mpr hb⟩
  unfold residueClassBoxSum
  simp_rw [hf]
  exact_mod_cast card_fiber_sum R S f

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTPairs -/

section

set_option maxHeartbeats 3000000

namespace Green64Analytic.SourceCRT

/-- Literal ordered product-two pairs. The assignment modulus may have
repeated prime factors; no squarefree condition is imposed. -/
def parityOriginalProductTwoPair434 (D : ℕ) [NeZero D] :=
  {z : ZMod D × ZMod D // z.1 * z.2 = (2 : ZMod D)}

noncomputable instance parityOriginalProductTwoPairFintype434
    (D : ℕ) [NeZero D] : Fintype (parityOriginalProductTwoPair434 D) := by
  classical
  unfold parityOriginalProductTwoPair434
  infer_instance

/-- This is an equivalence of finite residue sets only. It will never
be used to rescale the integer coordinates of a source box. -/
noncomputable def parityOriginalProductTwoEquivUnitPair434
    (D : ℕ) [NeZero D] (h2D : Nat.Coprime 2 D) :
    parityOriginalProductTwoPair434 D ≃ UnitPair D := by
  let a : (ZMod D)ˣ := ZMod.unitOfCoprime 2 h2D
  have ha : (a : ZMod D) = (2 : ZMod D) := by simp [a]
  exact
    { toFun := fun z => ⟨(z.val.1, z.val.2 * (↑(a⁻¹) : ZMod D)), by
        change z.val.1 * (z.val.2 * (↑(a⁻¹) : ZMod D)) = 1
        rw [← mul_assoc, z.property, ← ha]
        simp⟩
      invFun := fun z => ⟨(z.val.1, z.val.2 * (a : ZMod D)), by
        change z.val.1 * (z.val.2 * (a : ZMod D)) = 2
        rw [← mul_assoc, z.property, one_mul]
        exact ha⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · simp [mul_assoc]
      right_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · simp [mul_assoc] }

/-- The actual h=-2 assignment congruence has phi(D) roots for every
positive odd D, including D=1 and nonsquarefree D. -/
theorem parity_original_product_two_pairs_card434
    (D : ℕ) [NeZero D] (h2D : Nat.Coprime 2 D) :
    Fintype.card (parityOriginalProductTwoPair434 D) = D.totient := by
  calc
    _ = Fintype.card (UnitPair D) :=
      Fintype.card_congr (parityOriginalProductTwoEquivUnitPair434 D h2D)
    _ = _ := card_unit_pairs_eq_totient D

/-- Exact original shift-two semantics, valid in both directions and
without squarefreeness, coprimality of m,n, or cancellation of factors. -/
theorem parity_original_shift_two_product_residue_iff_dvd434
    (D u m n : ℕ) (hShift : m * n = u + 2) :
    (m : ZMod D) * (n : ZMod D) = (2 : ZMod D) ↔ D ∣ u := by
  have hcast :
      ((m : ZMod D) * (n : ZMod D) = (2 : ZMod D)) ↔
        Nat.ModEq D (m * n) 2 := by
    simpa using (ZMod.natCast_eq_natCast_iff (m * n) 2 D)
  rw [hcast, hShift]
  constructor
  · intro hz
    have hz' : Nat.ModEq D (u + 2) (0 + 2) := by simpa using hz
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 2 hz')
  · intro hDu
    simpa using Nat.ModEq.add_right 2 (Nat.modEq_zero_iff_dvd.mpr hDu)

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTRestricted -/

section

set_option maxHeartbeats 3500000

namespace Green64Analytic.SourceCRT

/-- The literal product-two assignment condition and an arbitrary
independent predicate on the second CRT component. -/
def parityOriginalShiftTwoCRTRestricted434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) :=
  {xy : ZMod (D * d) × ZMod (D * d) //
    (pairCRT D d hDd xy).1.1 * (pairCRT D d hDd xy).1.2 = (2 : ZMod D) ∧
      P (pairCRT D d hDd xy).2}

noncomputable instance parityOriginalShiftTwoCRTRestrictedFintype434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) :
    Fintype (parityOriginalShiftTwoCRTRestricted434 D d hDd P) := by
  classical
  unfold parityOriginalShiftTwoCRTRestricted434
  infer_instance

def parityOriginalShiftTwoCRTRestrictedEquiv434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) :
    parityOriginalShiftTwoCRTRestricted434 D d hDd P ≃
      parityOriginalProductTwoPair434 D × {z : ZMod d × ZMod d // P z} where
  toFun xy :=
    (⟨(pairCRT D d hDd xy.val).1, xy.property.1⟩,
      ⟨(pairCRT D d hDd xy.val).2, xy.property.2⟩)
  invFun xy :=
    ⟨(pairCRT D d hDd).symm (xy.1.val, xy.2.val), by
      simpa using And.intro xy.1.property xy.2.property⟩
  left_inv := by
    intro xy
    apply Subtype.ext
    exact (pairCRT D d hDd).left_inv xy.val
  right_inv := by
    intro xy
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((pairCRT D d hDd).right_inv (xy.1.val, xy.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd ((pairCRT D d hDd).right_inv (xy.1.val, xy.2.val))

theorem parity_original_shift_two_restricted_card434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (P : ZMod d × ZMod d → Prop) :
    Fintype.card (parityOriginalShiftTwoCRTRestricted434 D d hDd P) =
      D.totient * Fintype.card {z : ZMod d × ZMod d // P z} := by
  classical
  calc
    _ = Fintype.card
        (parityOriginalProductTwoPair434 D × {z : ZMod d × ZMod d // P z}) :=
      Fintype.card_congr (parityOriginalShiftTwoCRTRestrictedEquiv434 D d hDd P)
    _ = _ := by
      rw [Fintype.card_prod, parity_original_product_two_pairs_card434 D h2D]

noncomputable def parityOriginalShiftTwoCRTClasses434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) :
    Finset (ZMod (D * d) × ZMod (D * d)) := by
  classical
  exact Finset.univ.filter (fun xy =>
    (pairCRT D d hDd xy).1.1 * (pairCRT D d hDd xy).1.2 = (2 : ZMod D) ∧
      P (pairCRT D d hDd xy).2)

theorem parity_original_shift_two_crt_classes_card434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (P : ZMod d × ZMod d → Prop) :
    (parityOriginalShiftTwoCRTClasses434 D d hDd P).card =
      D.totient * Fintype.card {z : ZMod d × ZMod d // P z} := by
  classical
  have hsub :
      (parityOriginalShiftTwoCRTClasses434 D d hDd P).card =
        Fintype.card (parityOriginalShiftTwoCRTRestricted434 D d hDd P) := by
    simpa only [parityOriginalShiftTwoCRTClasses434, parityOriginalShiftTwoCRTRestricted434] using
      (Fintype.card_subtype (fun xy : ZMod (D * d) × ZMod (D * d) =>
        (pairCRT D d hDd xy).1.1 * (pairCRT D d hDd xy).1.2 = (2 : ZMod D) ∧
          P (pairCRT D d hDd xy).2)).symm
  exact hsub.trans (parity_original_shift_two_restricted_card434 D d hDd h2D P)

/-- Natural coordinates are reduced, not changed. This is the exact
membership identity needed before applying an integer-box estimate. -/
theorem parity_original_shift_two_crt_classes_nat_mem434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) (m n : ℕ) :
    ((m : ZMod (D * d)), (n : ZMod (D * d))) ∈
        parityOriginalShiftTwoCRTClasses434 D d hDd P ↔
      (m : ZMod D) * (n : ZMod D) = (2 : ZMod D) ∧
        P ((m : ZMod d), (n : ZMod d)) := by
  classical
  have hCRT :
      (pairCRT D d hDd ((m : ZMod (D * d)), (n : ZMod (D * d)))).1 =
        ((m : ZMod D), (n : ZMod D)) ∧
      (pairCRT D d hDd ((m : ZMod (D * d)), (n : ZMod (D * d)))).2 =
        ((m : ZMod d), (n : ZMod d)) := by
    simp [pairCRT, map_natCast]
  unfold parityOriginalShiftTwoCRTClasses434
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hCRT.1, hCRT.2]

/-- Literal carrier equivalence for the original product equation. -/
theorem parity_original_shift_two_fibre_crt_mem_iff434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop)
    (u m n : ℕ) (hShift : m * n = u + 2) :
    ((m : ZMod (D * d)), (n : ZMod (D * d))) ∈
        parityOriginalShiftTwoCRTClasses434 D d hDd P ↔
      D ∣ u ∧ P ((m : ZMod d), (n : ZMod d)) := by
  rw [parity_original_shift_two_crt_classes_nat_mem434,
    parity_original_shift_two_product_residue_iff_dvd434 D u m n hShift]

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTIntegerBox -/

section

set_option maxHeartbeats 3500000
open scoped BigOperators

namespace Green64Analytic.SourceCRT

/-- The actual integer rectangle with the product-two assignment
congruence and the unchanged local predicate. Endpoints are literal. -/
noncomputable def parityOriginalShiftTwoIntegerBox434
    (D d : ℕ) (P : ZMod d × ZMod d → Prop) (A B C E : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Ico A B ×ˢ Finset.Ico C E).filter (fun ij =>
    (ij.1 : ZMod D) * (ij.2 : ZMod D) = (2 : ZMod D) ∧
      P ((ij.1 : ZMod d), (ij.2 : ZMod d)))

theorem parity_original_shift_two_integer_box_eq_residue_sum434
    (D d : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (P : ZMod d × ZMod d → Prop) (A B C E : ℕ) :
    ((parityOriginalShiftTwoIntegerBox434 D d P A B C E).card : ℝ) =
      residueClassBoxSum (D * d)
        (parityOriginalShiftTwoCRTClasses434 D d hDd P) A B C E := by
  classical
  have h := residueClassBoxSum_eq_integer_filter
    (D * d) A B C E (parityOriginalShiftTwoCRTClasses434 D d hDd P)
  simp_rw [parity_original_shift_two_crt_classes_nat_mem434] at h
  exact h.symm

/-- Genuine fixed integer-box estimate. The residue equivalence is
used solely to count classes; the original integer box is unchanged. -/
theorem parity_original_shift_two_integer_box_error434
    (D d A B C E : ℕ) [NeZero D] [NeZero d]
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (P : ZMod d × ZMod d → Prop) (hAB : A ≤ B) (hCE : C ≤ E) :
    |((parityOriginalShiftTwoIntegerBox434 D d P A B C E).card : ℝ) -
      ((D.totient * Fintype.card {z : ZMod d × ZMod d // P z} : ℕ) : ℝ) *
        (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ) / ((D * d : ℕ) : ℝ) ^ 2)| ≤
      ((D.totient * Fintype.card {z : ZMod d × ZMod d // P z} : ℕ) : ℝ) *
        (4 + 2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) /
          ((D * d : ℕ) : ℝ)) := by
  classical
  rw [parity_original_shift_two_integer_box_eq_residue_sum434 D d hDd]
  have h := residueClassBoxSum_error (D * d)
    (parityOriginalShiftTwoCRTClasses434 D d hDd P) A B C E hAB hCE
  rw [parity_original_shift_two_crt_classes_card434 D d hDd h2D P] at h
  exact h

/-- The integer rectangle on an actual shifted-product fibre is
exactly the divisibility source, with all four endpoints retained. -/
theorem parity_original_shift_two_integer_box_mem_iff434
    (D d A B C E u m n : ℕ) (P : ZMod d × ZMod d → Prop)
    (hShift : m * n = u + 2) :
    (m, n) ∈ parityOriginalShiftTwoIntegerBox434 D d P A B C E ↔
      (A ≤ m ∧ m < B) ∧ (C ≤ n ∧ n < E) ∧
        D ∣ u ∧ P ((m : ZMod d), (n : ZMod d)) := by
  classical
  simp only [parityOriginalShiftTwoIntegerBox434, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Ico,
    parity_original_shift_two_product_residue_iff_dvd434 D u m n hShift]
  tauto

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTLocalMasks -/

section

set_option maxHeartbeats 4000000

namespace Green64Analytic.SourceCRT

/-- For the original relation mn=u+2, roughness excludes product zero
and the source banned-prime condition excludes product TWO. -/
def parityOriginalShiftTwoLocalFlag434 (p : ℕ) (rough banned : Bool)
    (xy : ZMod p × ZMod p) : Prop :=
  (rough = true ∧ xy.1 * xy.2 = 0) ∨
    (banned = true ∧ xy.1 * xy.2 = 2)

/-- Exact local count, including prime two. At p=2 the banned flag
must vanish; otherwise the two events overlap and old nu is false. -/
theorem parity_original_shift_two_local_flag_card434
    (p : ℕ) (hp : p.Prime) (rough banned : Bool)
    (hTwo : p = 2 → banned = false) :
    Nat.card {xy : ZMod p × ZMod p //
      parityOriginalShiftTwoLocalFlag434 p rough banned xy} =
      localNu p rough banned := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hcard :
      Nat.card {xy : ZMod p × ZMod p //
        parityOriginalShiftTwoLocalFlag434 p rough banned xy} =
      Nat.card (FlaggedBadPair p rough banned) := by
    by_cases hpTwo : p = 2
    · have hb := hTwo hpTwo
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (by
        intro xy
        simp [parityOriginalShiftTwoLocalFlag434, FlaggedBadPair, hb])
    · have h2p : Nat.Coprime 2 p :=
        (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpTwo)
      let a : (ZMod p)ˣ := ZMod.unitOfCoprime 2 h2p
      have ha : (a : ZMod p) = (2 : ZMod p) := by simp [a]
      let e : (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) :=
        { toFun := fun xy => (xy.1, xy.2 * (↑(a⁻¹) : ZMod p))
          invFun := fun xy => (xy.1, xy.2 * (a : ZMod p))
          left_inv := by
            intro xy
            apply Prod.ext
            · rfl
            · change (xy.2 * a.inv) * a.val = xy.2
              rw [mul_assoc, a.inv_val, mul_one]
          right_inv := by
            intro xy
            apply Prod.ext
            · rfl
            · change (xy.2 * a.val) * a.inv = xy.2
              rw [mul_assoc, a.val_inv, mul_one] }
      have hz (xy : ZMod p × ZMod p) :
          (e xy).1 * (e xy).2 = 0 ↔ xy.1 * xy.2 = 0 := by
        constructor
        · intro h
          have h' := congrArg (fun z : ZMod p => z * (a : ZMod p)) h
          change (xy.1 * (xy.2 * a.inv)) * a.val = 0 * a.val at h'
          simpa only [mul_assoc, a.inv_val, mul_one, zero_mul] using h'
        · intro h
          change xy.1 * (xy.2 * (↑(a⁻¹) : ZMod p)) = 0
          rw [← mul_assoc, h, zero_mul]
      have ho (xy : ZMod p × ZMod p) :
          (e xy).1 * (e xy).2 = 1 ↔ xy.1 * xy.2 = 2 := by
        constructor
        · intro h
          have h' := congrArg (fun z : ZMod p => z * (a : ZMod p)) h
          have h'' : xy.1 * xy.2 = (a : ZMod p) := by
            change (xy.1 * (xy.2 * a.inv)) * a.val = 1 * a.val at h'
            simpa only [mul_assoc, a.inv_val, mul_one, one_mul] using h'
          exact h''.trans ha
        · intro h
          change xy.1 * (xy.2 * (↑(a⁻¹) : ZMod p)) = 1
          rw [← mul_assoc, h, ← ha]
          exact a.val_inv
      apply Nat.card_congr
      refine Equiv.subtypeEquiv e ?_
      intro xy
      change parityOriginalShiftTwoLocalFlag434 p rough banned xy ↔
        (rough = true ∧ (e xy).1 * (e xy).2 = 0) ∨
          (banned = true ∧ (e xy).1 * (e xy).2 = 1)
      rw [hz, ho]
      rfl
  rw [hcard, Nat.card_eq_fintype_card]
  exact cardinal_flagged_prime_pairs p rough banned

/-- Source local sieve-density constants remain valid at prime two
when its banned flag is false; no deletion of prime two is used. -/
theorem parity_original_shift_two_local_density_bounds434
    (p : ℕ) (hp : p.Prime) (rough banned : Bool)
    (hTwo : p = 2 → banned = false) :
    (Nat.card {xy : ZMod p × ZMod p //
      parityOriginalShiftTwoLocalFlag434 p rough banned xy} : ℝ) / (p : ℝ) ^ 2 ≤ 7 / 9 ∧
    (Nat.card {xy : ZMod p × ZMod p //
      parityOriginalShiftTwoLocalFlag434 p rough banned xy} : ℝ) / (p : ℝ) ^ 2 ≤ 3 / (p : ℝ) := by
  rw [parity_original_shift_two_local_flag_card434 p hp rough banned hTwo]
  by_cases hpTwo : p = 2
  · subst p
    have hb := hTwo rfl
    subst banned
    cases rough <;> norm_num [localNu]
  · have hpThree : 3 ≤ p := by
      have := hp.two_le
      omega
    exact ⟨local_density_le_seven_ninths p hpThree rough banned,
      local_density_le_three_div p hpThree rough banned⟩

theorem parity_original_shift_two_prime_two_good_factor434 :
    1 - (Nat.card {xy : ZMod 2 × ZMod 2 //
      parityOriginalShiftTwoLocalFlag434 2 true false xy} : ℝ) / (2 : ℝ) ^ 2 =
      (1 - 1 / (2 : ℝ)) ^ 2 := by
  rw [parity_original_shift_two_local_flag_card434 2 Nat.prime_two true false (by simp)]
  norm_num [localNu]


/-- Parity6.2 bans u-divisibility only at odd primes. This explicit
source mask supplies banned2=false without deleting prime2 roughness. -/
noncomputable def parityOriginalOddBannedMask434 (banned : ℕ → Bool) (p : ℕ) : Bool := by
  classical
  exact if Odd p then banned p else false

theorem parity_original_odd_banned_mask_two434 (banned : ℕ → Bool) :
    parityOriginalOddBannedMask434 banned 2 = false := by
  norm_num [parityOriginalOddBannedMask434]

theorem parity_original_odd_banned_mask_true_iff434 (banned : ℕ → Bool) (p : ℕ) :
    parityOriginalOddBannedMask434 banned p = true ↔ Odd p ∧ banned p = true := by
  classical
  by_cases h : Odd p <;> simp [parityOriginalOddBannedMask434, h]

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTSquarefree -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators

namespace Green64Analytic.SourceCRT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def parityOriginalShiftTwoAllFlaggedPairs434
    (q : ι → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (rough banned : ι → Bool) :=
  {xy : ZMod (∏ i, q i) × ZMod (∏ i, q i) //
    ∀ i, parityOriginalShiftTwoLocalFlag434 (q i) (rough i) (banned i)
      ((pairCRTAll q hc xy) i)}

theorem parity_original_shift_two_all_flagged_card434
    (q : ι → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hPrime : ∀ i, (q i).Prime) (rough banned : ι → Bool)
    (hTwo : ∀ i, q i = 2 → banned i = false) :
    Nat.card (parityOriginalShiftTwoAllFlaggedPairs434 q hc rough banned) =
      ∏ i, localNu (q i) (rough i) (banned i) := by
  classical
  letI : NeZero (∏ i, q i) := ⟨by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (hPrime i).ne_zero⟩
  letI : ∀ i, NeZero (q i) := fun i => ⟨(hPrime i).ne_zero⟩
  letI : Fintype (parityOriginalShiftTwoAllFlaggedPairs434 q hc rough banned) := by
    unfold parityOriginalShiftTwoAllFlaggedPairs434
    infer_instance
  let e : parityOriginalShiftTwoAllFlaggedPairs434 q hc rough banned ≃
      ((i : ι) → {xy : ZMod (q i) × ZMod (q i) //
        parityOriginalShiftTwoLocalFlag434 (q i) (rough i) (banned i) xy}) :=
    { toFun := fun x i => ⟨(pairCRTAll q hc x.val) i, x.property i⟩
      invFun := fun fam => ⟨(pairCRTAll q hc).symm (fun i => (fam i).val), by
        intro i
        simpa only [(pairCRTAll q hc).apply_symm_apply] using (fam i).property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (pairCRTAll q hc).left_inv x.val
      right_inv := by
        intro fam
        funext i
        apply Subtype.ext
        exact congrArg (fun f => f i)
          ((pairCRTAll q hc).right_inv (fun i => (fam i).val)) }
  calc
    _ = Fintype.card (parityOriginalShiftTwoAllFlaggedPairs434 q hc rough banned) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card
        ((i : ι) → {xy : ZMod (q i) × ZMod (q i) //
          parityOriginalShiftTwoLocalFlag434 (q i) (rough i) (banned i) xy}) :=
      Fintype.card_congr e
    _ = ∏ i, Fintype.card {xy : ZMod (q i) × ZMod (q i) //
        parityOriginalShiftTwoLocalFlag434 (q i) (rough i) (banned i) xy} := by
      rw [Fintype.card_pi]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Nat.card_eq_fintype_card]
      exact parity_original_shift_two_local_flag_card434
        (q i) (hPrime i) (rough i) (banned i) (hTwo i)

/-- Literal original product0/product2 local conditions on ZMod d.
Even squarefree d and the empty prime family d=1 are retained. -/
def parityOriginalShiftTwoSquarefreeBad434
    (d : ℕ) (hd : Squarefree d) (rough banned : ℕ → Bool)
    (xy : ZMod d × ZMod d) : Prop :=
  ∀ p : d.primeFactors,
    parityOriginalShiftTwoLocalFlag434 p.val (rough p.val) (banned p.val)
      ((pairCRTAll (fun q : d.primeFactors => (q : ℕ))
        (primeFamilyPairwise d)
        (squarefreePairToPrimeProduct d hd xy)) p)

theorem parity_original_shift_two_squarefree_bad_card434
    (d : ℕ) (hd : Squarefree d) (rough banned : ℕ → Bool)
    (hBannedTwo : banned 2 = false) :
    Nat.card {xy : ZMod d × ZMod d //
      parityOriginalShiftTwoSquarefreeBad434 d hd rough banned xy} =
      ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  have htransport :
      Nat.card {xy : ZMod d × ZMod d //
        parityOriginalShiftTwoSquarefreeBad434 d hd rough banned xy} =
      Nat.card (parityOriginalShiftTwoAllFlaggedPairs434
        (fun p : d.primeFactors => (p : ℕ)) (primeFamilyPairwise d)
        (fun p => rough (p : ℕ)) (fun p => banned (p : ℕ))) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (squarefreePairToPrimeProduct d hd) (by intro xy; rfl)
  rw [htransport]
  have hPrime (p : d.primeFactors) : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.property
  have hTwo (p : d.primeFactors) : (p : ℕ) = 2 → banned (p : ℕ) = false := by
    intro h
    rw [h]
    exact hBannedTwo
  have h := parity_original_shift_two_all_flagged_card434
    (fun p : d.primeFactors => (p : ℕ)) (primeFamilyPairwise d)
    hPrime (fun p => rough (p : ℕ)) (fun p => banned (p : ℕ)) hTwo
  exact h.trans ((Finset.prod_subtype d.primeFactors (fun _ => Iff.rfl)
    (fun p : ℕ => localNu p (rough p) (banned p))).symm)

theorem parity_original_squarefree_pair_projection_nat434
    (d m n : ℕ) (hd : Squarefree d) (p : d.primeFactors) :
    (pairCRTAll (fun q : d.primeFactors => (q : ℕ))
      (primeFamilyPairwise d)
      (squarefreePairToPrimeProduct d hd
        ((m : ZMod d), (n : ZMod d)))) p =
      ((m : ZMod p.val), (n : ZMod p.val)) := by
  change
    (((ZMod.prodEquivPi (fun q : d.primeFactors => (q : ℕ))
        (primeFamilyPairwise d))
        ((ZMod.ringEquivCongr (squarefreePrimeFamilyModulus d hd).symm)
          (m : ZMod d))) p,
      ((ZMod.prodEquivPi (fun q : d.primeFactors => (q : ℕ))
        (primeFamilyPairwise d))
        ((ZMod.ringEquivCongr (squarefreePrimeFamilyModulus d hd).symm)
          (n : ZMod d))) p) =
      ((m : ZMod p.val), (n : ZMod p.val))
  simp only [map_natCast, Pi.natCast_apply]

/-- Exact source semantics for arbitrary Boolean flags. The ban at
two restriction is needed for nu-cardinality, not for this identity. -/
theorem parity_original_shift_two_squarefree_bad_nat_iff434
    (d u m n : ℕ) (hd : Squarefree d) (rough banned : ℕ → Bool)
    (hShift : m * n = u + 2) :
    parityOriginalShiftTwoSquarefreeBad434 d hd rough banned
      ((m : ZMod d), (n : ZMod d)) ↔
      ∀ p ∈ d.primeFactors,
        (rough p = true ∧ p ∣ m * n) ∨ (banned p = true ∧ p ∣ u) := by
  have hzero (p : ℕ) :
      (m : ZMod p) * (n : ZMod p) = 0 ↔ p ∣ m * n := by
    simpa only [Nat.cast_mul] using ZMod.natCast_eq_zero_iff (m * n) p
  have hlocal (p : ℕ) :
      parityOriginalShiftTwoLocalFlag434 p (rough p) (banned p)
        ((m : ZMod p), (n : ZMod p)) ↔
        (rough p = true ∧ p ∣ m * n) ∨ (banned p = true ∧ p ∣ u) := by
    unfold parityOriginalShiftTwoLocalFlag434
    rw [hzero p, parity_original_shift_two_product_residue_iff_dvd434 p u m n hShift]
  constructor
  · intro h p hp
    have ht := h ⟨p, hp⟩
    rw [parity_original_squarefree_pair_projection_nat434] at ht
    exact (hlocal p).mp ht
  · intro h p
    rw [parity_original_squarefree_pair_projection_nat434]
    exact (hlocal p.val).mpr (h p.val p.property)

end Green64Analytic.SourceCRT

end

/-! ## OriginalShiftTwoCRTMaskedBox -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators

namespace Green64Analytic.SourceCRT

/-- The actual assignment root and both original local masks on the
literal combined modulus D*d. D is not required to be squarefree. -/
def parityOriginalShiftTwoMaskedCRT434
    (D d : ℕ) (hDd : D.Coprime d) (hd : Squarefree d)
    (rough banned : ℕ → Bool) :=
  {xy : ZMod (D * d) × ZMod (D * d) //
    (pairCRT D d hDd xy).1.1 * (pairCRT D d hDd xy).1.2 = (2 : ZMod D) ∧
      parityOriginalShiftTwoSquarefreeBad434 d hd rough banned (pairCRT D d hDd xy).2}

theorem parity_original_shift_two_masked_crt_card434
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hBannedTwo : banned 2 = false) :
    Nat.card (parityOriginalShiftTwoMaskedCRT434 D d hDd hd rough banned) =
      D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) := by
  classical
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero d := ⟨hd.ne_zero⟩
  let P := parityOriginalShiftTwoSquarefreeBad434 d hd rough banned
  change Nat.card (parityOriginalShiftTwoCRTRestricted434 D d hDd P) = _
  calc
    _ = Fintype.card (parityOriginalShiftTwoCRTRestricted434 D d hDd P) :=
      Nat.card_eq_fintype_card
    _ = D.totient * Fintype.card {xy : ZMod d × ZMod d // P xy} :=
      parity_original_shift_two_restricted_card434 D d hDd h2D P
    _ = D.totient * Nat.card {xy : ZMod d × ZMod d // P xy} := by
      rw [Nat.card_eq_fintype_card]
    _ = _ := by
      rw [parity_original_shift_two_squarefree_bad_card434 d hd rough banned hBannedTwo]

/-- Fixed integer box with every local rough/banned source condition,
including the exact ordinary prime-two factor. -/
theorem parity_original_shift_two_masked_integer_box_error434
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hBannedTwo : banned 2 = false)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    |((parityOriginalShiftTwoIntegerBox434 D d
        (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) A B C E).card : ℝ) -
      ((D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ) / ((D * d : ℕ) : ℝ) ^ 2)| ≤
      ((D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (4 + 2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) /
          ((D * d : ℕ) : ℝ)) := by
  classical
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero d := ⟨hd.ne_zero⟩
  have h := parity_original_shift_two_integer_box_error434
    D d A B C E hDd h2D
    (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) hAB hCE
  have hc :
      Fintype.card {xy : ZMod d × ZMod d //
        parityOriginalShiftTwoSquarefreeBad434 d hd rough banned xy} =
      ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) :=
    Nat.card_eq_fintype_card.symm.trans
      (parity_original_shift_two_squarefree_bad_card434 d hd rough banned hBannedTwo)
  rw [hc] at h
  exact h

/-- No assumption on masks is used in the literal natural source
identity. Cardinality restrictions are stated separately above. -/
theorem parity_original_shift_two_masked_integer_box_mem_iff434
    (D d A B C E u m n : ℕ) (hd : Squarefree d)
    (rough banned : ℕ → Bool) (hShift : m * n = u + 2) :
    (m, n) ∈ parityOriginalShiftTwoIntegerBox434 D d
        (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) A B C E ↔
      (A ≤ m ∧ m < B) ∧ (C ≤ n ∧ n < E) ∧ D ∣ u ∧
        ∀ p ∈ d.primeFactors,
          (rough p = true ∧ p ∣ m * n) ∨ (banned p = true ∧ p ∣ u) := by
  rw [parity_original_shift_two_integer_box_mem_iff434 D d A B C E u m n
    (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) hShift]
  rw [parity_original_shift_two_squarefree_bad_nat_iff434 d u m n hd rough banned hShift]


/-- Cardinality for the actual odd banned-prime convention of Parity6.2.
The prime-two flag premise has been constructed, not assumed. -/
theorem parity_original_shift_two_odd_mask_crt_card434
    (D d : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) :
    Nat.card (parityOriginalShiftTwoMaskedCRT434 D d hDd hd rough
      (parityOriginalOddBannedMask434 banned)) =
      D.totient * ∏ p ∈ d.primeFactors,
        localNu p (rough p) (parityOriginalOddBannedMask434 banned p) :=
  parity_original_shift_two_masked_crt_card434 D d hD hd hDd h2D
    rough (parityOriginalOddBannedMask434 banned) (parity_original_odd_banned_mask_two434 banned)

/-- The literal original odd-prime banned events on the shifted fibre. -/
theorem parity_original_shift_two_odd_mask_box_mem_iff434
    (D d A B C E u m n : ℕ) (hd : Squarefree d)
    (rough banned : ℕ → Bool) (hShift : m * n = u + 2) :
    (m, n) ∈ parityOriginalShiftTwoIntegerBox434 D d
        (parityOriginalShiftTwoSquarefreeBad434 d hd rough
          (parityOriginalOddBannedMask434 banned)) A B C E ↔
      (A ≤ m ∧ m < B) ∧ (C ≤ n ∧ n < E) ∧ D ∣ u ∧
        ∀ p ∈ d.primeFactors,
          (rough p = true ∧ p ∣ m * n) ∨
            ((Odd p ∧ banned p = true) ∧ p ∣ u) := by
  rw [parity_original_shift_two_masked_integer_box_mem_iff434
    D d A B C E u m n hd rough (parityOriginalOddBannedMask434 banned) hShift]
  simp_rw [parity_original_odd_banned_mask_true_iff434]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTActualIntegerBox -/

section

set_option maxHeartbeats 4800000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- Exactly the source shifted integer [A,B)×[C,E) pairs whose
original residues modulo D*d meet BOTH the assignment D condition
and every rough/banned d condition. No lattice approximation. -/
noncomputable def literalSourceIntegerBoxCount
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) : ℕ :=
  ((Finset.Ico A B ×ˢ Finset.Ico C E).filter
    (fun ij : ℕ × ℕ =>
      ((ij.1 : ZMod (D*d)), (ij.2 : ZMod (D*d))) ∈
        sourceActualResidueClasses D d hD hd hC rough banned)).card

/-- The true finite integer count has exact CRT expected density
φ(D)*ν(d)/(Dd)^2, and the per-residue lattice O(1+side/Dd)
error accumulated over exactly φ(D)*ν(d) surviving classes. -/
theorem literalSourceIntegerBox_error
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    |(literalSourceIntegerBoxCount D d A B C E hD hd hC rough banned : ℝ) -
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/((D*d:ℕ):ℝ)^2)| ≤
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (4+2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/((D*d:ℕ):ℝ)) := by
  have hpos : 0 < D*d :=
    Nat.mul_pos hD (Nat.pos_of_ne_zero hd.ne_zero)
  letI : NeZero (D*d) := ⟨Nat.ne_of_gt hpos⟩
  have hbound :=
    sourceActualResidueBox_error D d A B C E hD hd hC
      rough banned hAB hCE
  have hident :=
    residueClassBoxSum_eq_integer_filter (D*d)
      A B C E
      (sourceActualResidueClasses D d hD hd hC rough banned)
  change |residueClassBoxSum (D*d)
      (sourceActualResidueClasses D d hD hd hC rough banned)
      A B C E - _| ≤ _ at hbound
  rw [hident] at hbound
  exact hbound

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTSourceSemantics -/

section

set_option maxHeartbeats 5000000
namespace Green64Analytic.SourceCRT

/-- CRT projection of the *same two natural integers*, with no loss
of information about the original p-2 shift. -/
theorem pairCRT_natCast (D d m n : ℕ) (hC : D.Coprime d) :
    (pairCRT D d hC
      ((m : ZMod (D*d)), (n : ZMod (D*d)))).1 =
         ((m : ZMod D), (n : ZMod D)) ∧
    (pairCRT D d hC
      ((m : ZMod (D*d)), (n : ZMod (D*d)))).2 =
         ((m : ZMod d), (n : ZMod d)) := by
  simp [pairCRT, map_natCast]

/-- The CRT residue predicate is exactly the source natural
assignment congruence mn ≡ 1 mod D, together with the literal
local product-zero/one prime constraints after reduction mod d. -/
theorem sourceActualResidue_natCast_iff
    (D d m n : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    ((m : ZMod (D*d)), (n : ZMod (D*d))) ∈
       sourceActualResidueClasses D d hD hd hC rough banned ↔
       Nat.ModEq D (m*n) 1 ∧
         squarefreeBadOnD d hd rough banned
           ((m : ZMod d), (n : ZMod d)) := by
  classical
  have hCRT := pairCRT_natCast D d m n hC
  have hMN : ((m : ZMod D) * (n : ZMod D) = 1) ↔
      Nat.ModEq D (m*n) 1 := by
    simpa only [Nat.cast_mul, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (m*n) 1 D)
  unfold sourceActualResidueClasses
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hCRT.1, hCRT.2, hMN]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTActualIntegerExact -/

section

set_option maxHeartbeats 4800000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- The true natural pair predicate is deliberately formed under
classical decidability; it is not a synthetic real-valued surrogate. -/
noncomputable def sourceNaturalCongruenceBoxCount
    (D d A B C E : ℕ) (hd : Squarefree d)
    (rough banned : ℕ → Bool) : ℕ := by
  classical
  exact ((Finset.Ico A B ×ˢ Finset.Ico C E).filter
    (fun mn : ℕ × ℕ =>
      Nat.ModEq D (mn.1*mn.2) 1 ∧
      squarefreeBadOnD d hd rough banned
        ((mn.1 : ZMod d),(mn.2 : ZMod d)))).card

/-- The source count over an arbitrary shifted integer box is
LITERALLY the count of mn≡1 modulo D and all local forbidden
classes modulo squarefree d; no residue-set surrogate remains. -/
theorem literalSourceIntegerBoxCount_eq_natural_filter
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool) :
    literalSourceIntegerBoxCount D d A B C E hD hd hC rough banned =
      sourceNaturalCongruenceBoxCount D d A B C E hd rough banned := by
  classical
  unfold literalSourceIntegerBoxCount sourceNaturalCongruenceBoxCount
  apply congrArg Finset.card
  ext mn
  simp only [Finset.mem_filter]
  rw [sourceActualResidue_natCast_iff D d mn.1 mn.2 hD hd hC rough banned]
/-- Source shift N_u=2u+1: if an assignment modulus D divides
the assignment variable u, then the actual pair (m,n)
satisfying mn=2u+1 occupies one of the proved CRT classes
iff its remaining squarefree sieve flags allow it. -/
theorem sourceShift_assignment_in_crt_classes
    (D d u m n : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool)
    (hDu : D ∣ u) (hShift : m*n = 2*u+1)
    (hBad : squarefreeBadOnD d hd rough banned
       ((m : ZMod d),(n : ZMod d))) :
    ((m : ZMod (D*d)),(n : ZMod (D*d))) ∈
      sourceActualResidueClasses D d hD hd hC rough banned := by
  rw [sourceActualResidue_natCast_iff D d m n hD hd hC rough banned]
  exact ⟨assignment_divisor_forces_pair_one D u m n hDu hShift,hBad⟩

/-- Completely natural-number formulation of the literal source
Section ex:box CRT sieve: mn≡1 modulo arbitrary D, squarefree
local flags modulo d, count over arbitrary shifted integer rectangle. -/
theorem sourceNaturalCongruenceBox_error
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hC : D.Coprime d) (rough banned : ℕ → Bool)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    |(sourceNaturalCongruenceBoxCount D d A B C E hd rough banned : ℝ) -
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (((B-A:ℕ):ℝ)*((E-C:ℕ):ℝ)/((D*d:ℕ):ℝ)^2)| ≤
      ((D.totient * ∏ p ∈ d.primeFactors,
         localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (4+2*(((B-A:ℕ):ℝ)+((E-C:ℕ):ℝ))/((D*d:ℕ):ℝ)) := by
  have h := literalSourceIntegerBox_error D d A B C E hD hd hC
    rough banned hAB hCE
  rw [literalSourceIntegerBoxCount_eq_natural_filter
    D d A B C E hD hd hC rough banned] at h
  exact h

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTDivisorMajorant -/

section

set_option maxHeartbeats 5500000
open scoped BigOperators
namespace Green64Analytic.SourceCRT

/-- Uniform, no mask dependence: each odd prime's bad local class
count is ≤ 3p (in fact ≤ 3p-2). -/
theorem localNu_le_three_mul (p : ℕ) (hp : p.Prime)
    (rough banned : Bool) :
    localNu p rough banned ≤ 3*p := by
  have hp1 : 1 ≤ p := hp.one_le
  exact (localNu_le p hp1 rough banned).trans (by omega)

/-- For squarefree d its number of divisors is exactly 2^ω(d).
This proof retains the arithmetic factorization, not an invented τ. -/
theorem squarefree_divisors_card (d : ℕ) (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  rw [Nat.card_divisors hd.ne_zero]
  have heach (p : ℕ) (hp : p ∈ d.primeFactors) :
      d.factorization p + 1 = 2 := by
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdiv : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.factorization_eq_one_of_squarefree hd hprime hdiv]
  have heq : d.primeFactors.prod (fun p => d.factorization p + 1) =
      d.primeFactors.prod (fun _p => (2 : ℕ)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact heach p hp
  rw [heq]
  simp
/-- Precisely the source inequality ν(d) ≤ d τ(d)^2,
uniform in both overlapping local sieve flags, for any squarefree d.
The edge case d=1 is automatic. -/
theorem localNu_product_le_divisorSquare (d : ℕ)
    (hd : Squarefree d) (rough banned : ℕ → Bool) :
    (∏ p ∈ d.primeFactors, localNu p (rough p) (banned p)) ≤
      d * d.divisors.card ^ 2 := by
  have hprod :
      (∏ p ∈ d.primeFactors, localNu p (rough p) (banned p)) ≤
      ∏ p ∈ d.primeFactors, 3 * p := by
    apply Finset.prod_le_prod
    intro p hp
    exact localNu_le_three_mul p
      (Nat.prime_of_mem_primeFactors hp) (rough p) (banned p)
  have h3 :
      (∏ p ∈ d.primeFactors, 3*p) =
      d * 3 ^ d.primeFactors.card := by
    rw [Finset.prod_mul_distrib]
    rw [Nat.prod_primeFactors_of_squarefree hd]
    simp [mul_comm]
  have h34 : 3 ^ d.primeFactors.card ≤
      d.divisors.card ^ 2 := by
    rw [squarefree_divisors_card d hd]
    calc
      _ ≤ 4 ^ d.primeFactors.card :=
        (Nat.pow_le_pow_left (by decide : 3 ≤ 4)) _
      _ = (2 ^ d.primeFactors.card)^2 := by
        rw [show (4:ℕ) = 2^2 by norm_num]
        simp only [← pow_mul, Nat.mul_comm]
  calc
    _ ≤ d * 3 ^ d.primeFactors.card := by
      rw [← h3]
      exact hprod
    _ ≤ d * d.divisors.card ^ 2 := Nat.mul_le_mul_left _ h34

end Green64Analytic.SourceCRT

end

/-! ## ArcLift -/

section

namespace Green64CorrArc

/-! Exact rational-center lift for an approximation to k times a frequency. -/
theorem lift_signed_rational_center
    (k a z : ℤ) (r : ℕ) (theta delta : ℝ)
    (hk : k ≠ 0) (hr : 0 < r)
    (hnear : |(k : ℝ) * theta - (a : ℝ) / (r : ℝ) - (z : ℝ)| ≤ delta) :
    |theta - ((a + z * (r : ℤ) : ℤ) : ℝ) / ((k : ℝ) * (r : ℝ))| ≤
      delta / |(k : ℝ)| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hid : (k : ℝ) *
      (theta - ((a + z * (r : ℤ) : ℤ) : ℝ) / ((k : ℝ) * (r : ℝ))) =
      (k : ℝ) * theta - (a : ℝ) / (r : ℝ) - (z : ℝ) := by
    push_cast
    field_simp
    ring
  have habs : |(k : ℝ)| *
      |theta - ((a + z * (r : ℤ) : ℤ) : ℝ) / ((k : ℝ) * (r : ℝ))| ≤ delta := by
    rw [← abs_mul, hid]
    exact hnear
  exact (le_div_iff₀ (abs_pos.mpr hkR)).mpr (by simpa [mul_comm] using habs)

end Green64CorrArc

namespace Green64CorrArc

theorem lift_to_positive_denominator
    (k a z : ℤ) (r : ℕ) (theta delta : ℝ)
    (hk : k ≠ 0) (hr : 0 < r)
    (hnear : |(k : ℝ) * theta - (a : ℝ) / (r : ℝ) - (z : ℝ)| ≤ delta) :
    ∃ (h : ℤ) (q : ℕ), q = k.natAbs * r ∧ 0 < q ∧
      |theta - (h : ℝ) / (q : ℝ)| ≤ delta / |(k : ℝ)| := by
  have hbound := lift_signed_rational_center k a z r theta delta hk hr hnear
  have hqpos : 0 < k.natAbs * r :=
    Nat.mul_pos (Int.natAbs_pos.mpr hk) hr
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · have hkcast : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hi : ((k.natAbs : ℕ) : ℤ) = -k := by
        simpa [Int.natAbs_neg] using
          (Int.natAbs_of_nonneg (a := -k) (neg_nonneg.mpr (le_of_lt hkneg)))
      simpa using congrArg (fun v : ℤ => (v : ℝ)) hi
    refine ⟨-(a + z * (r : ℤ)), k.natAbs * r, rfl, hqpos, ?_⟩
    have hcenter :
        ((-(a + z * (r : ℤ)) : ℤ) : ℝ) / ((k.natAbs * r : ℕ) : ℝ) =
        ((a + z * (r : ℤ) : ℤ) : ℝ) / ((k : ℝ) * (r : ℝ)) := by
      simp [Nat.cast_mul, hkcast, neg_mul]
      ring
    rw [hcenter]
    exact hbound
  · have hkcast : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hi : ((k.natAbs : ℕ) : ℤ) = k :=
        Int.natAbs_of_nonneg (le_of_lt hkpos)
      simpa using congrArg (fun v : ℤ => (v : ℝ)) hi
    refine ⟨a + z * (r : ℤ), k.natAbs * r, rfl, hqpos, ?_⟩
    simpa [Nat.cast_mul, hkcast] using hbound

end Green64CorrArc

namespace Green64CorrArc

theorem reduced_center_exact (h : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ (h0 z : ℤ), 0 ≤ h0 ∧ h0 < (q : ℤ) ∧
      h = h0 + (q : ℤ) * z := by
  have hqInt : 0 < (q : ℤ) := by exact_mod_cast hq
  have hh := (Int.ediv_emod_unique (a := h) (b := (q : ℤ))
      (r := h % (q : ℤ)) (q := h / (q : ℤ)) hqInt).mp ⟨rfl, rfl⟩
  rcases hh with ⟨heq, hge, hlt⟩
  refine ⟨h % (q : ℤ), h / (q : ℤ), hge, hlt, ?_⟩
  omega

theorem source_denominator_budget (k r K R : ℕ)
    (hk : k ≤ K) (hr : r ≤ R) :
    k * r ≤ K * R := Nat.mul_le_mul hk hr

theorem polylog_rational_center_count (Q : ℕ) :
    (∑ q ∈ Finset.range (Q + 1), q) ≤ Q * (Q + 1) := by
  induction Q with
  | zero => norm_num
  | succ Q ih =>
      rw [show Q + 1 + 1 = Q + 2 by omega, Finset.sum_range_succ]
      nlinarith

end Green64CorrArc

namespace Green64CorrArc

theorem lift_circle_rational_center
    (k a z : ℤ) (r : ℕ) (theta delta : ℝ)
    (hk : k ≠ 0) (hr : 0 < r)
    (hnear : |(k : ℝ) * theta - (a : ℝ) / (r : ℝ) - (z : ℝ)| ≤ delta) :
    ∃ (h0 : ℤ) (q : ℕ) (translate : ℤ),
      q = k.natAbs * r ∧ 0 < q ∧ 0 ≤ h0 ∧ h0 < (q : ℤ) ∧
      |theta - (translate : ℝ) - (h0 : ℝ) / (q : ℝ)| ≤
        delta / |(k : ℝ)| := by
  obtain ⟨h, q, hq, hqpos, hbound⟩ :=
    lift_to_positive_denominator k a z r theta delta hk hr hnear
  obtain ⟨h0, translate, h0nonneg, h0lt, hdecomp⟩ :=
    reduced_center_exact h q hqpos
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hfrac : (h : ℝ) / (q : ℝ) =
      (h0 : ℝ) / (q : ℝ) + (translate : ℝ) := by
    rw [hdecomp]
    push_cast
    field_simp
  refine ⟨h0, q, translate, hq, hqpos, h0nonneg, h0lt, ?_⟩
  rw [hfrac] at hbound
  convert hbound using 1 <;> ring

end Green64CorrArc

end

/-! ## SourceDirichletArcDichotomy -/

section

namespace Green64Analytic.CorrelationD

/-- One genuinely unconditional Dirichlet approximation to k θ.
Either it has the large denominator required by minor C6, or θ
lies in a small rational arc of the correct signed lifted denominator.
This is the actual major/minor split and not an arc covering
hypothesis. -/
theorem source_dirichlet_major_minor_dichotomy
    (k : ℤ) (theta : ℝ) (Q R : ℕ)
    (hk : k ≠ 0) (hQ : 0 < Q) :
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ Q ∧ Int.gcd a (r:ℤ) = 1 ∧
      |(k:ℝ)*theta - (a:ℝ)/(r:ℝ)| ≤
        1/(((Q:ℝ)+1)*(r:ℝ)) ∧
      |(k:ℝ)*theta - (a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
      (R ≤ r ∨ ∃ (h : ℤ) (q : ℕ) (shift : ℤ),
        r < R ∧ q = k.natAbs*r ∧ 0 < q ∧
        q ≤ k.natAbs*Q ∧ 0 ≤ h ∧ h < (q:ℤ) ∧
        |theta-(shift:ℝ)-(h:ℝ)/(q:ℝ)| ≤
          (1/(((Q:ℝ)+1)*(r:ℝ)))/|(k:ℝ)|) := by
  obtain ⟨a,r,hr,hrQ,hcop,hnear,hbeta⟩ :=
    source_exists_reduced_dirichlet_approximation ((k:ℝ)*theta) Q hQ
  refine ⟨a,r,hr,hrQ,hcop,hnear,hbeta,?_⟩
  by_cases hR : R ≤ r
  · exact Or.inl hR
  · have hrR : r < R := Nat.lt_of_not_ge hR
    have hnear' :
      |(k:ℝ)*theta - (a:ℝ)/(r:ℝ) - ((0:ℤ):ℝ)| ≤
        1/(((Q:ℝ)+1)*(r:ℝ)) := by simpa using hnear
    obtain ⟨h,q,shift,hq,hqpos,h0,h0lt,hbound⟩ :=
      Green64CorrArc.lift_circle_rational_center k a 0 r theta
        (1/(((Q:ℝ)+1)*(r:ℝ))) hk hr hnear'
    right
    refine ⟨h,q,shift,hrR,hq,hqpos,?_,h0,h0lt,hbound⟩
    rw [hq]
    exact Nat.mul_le_mul_left _ hrQ
end Green64Analytic.CorrelationD

end

/-! ## BilinearBridge -/

section

namespace Green64SourceC6

/-- Literal finite two-coefficient L2 bilinear transfer from a Gram row bound.
No assumption on signs/regularity of A,B or locations of the finite sets. -/
theorem bilinear_from_gram_bound {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (A : ι → ℂ) (B : κ → ℂ) (E : ι → κ → ℂ)
    (K : κ → κ → ℝ) (R : ℝ)
    (hK : ∀ j ∈ t, ∀ k ∈ t, 0 ≤ K j k)
    (hsym : ∀ j ∈ t, ∀ k ∈ t, K j k = K k j)
    (hdom : ∀ j ∈ t, ∀ k ∈ t,
      ‖∑ i ∈ s, E i j * star (E i k)‖ ≤ K j k)
    (hrow : ∀ j ∈ t, (∑ k ∈ t, K j k) ≤ R) :
    ‖∑ i ∈ s, A i * (∑ j ∈ t, B j * E i j)‖^2 ≤
      (∑ i ∈ s, ‖A i‖^2) * (R * (∑ j ∈ t, ‖B j‖^2)) := by
  classical
  let Z := fun i => ∑ j ∈ t, B j * E i j
  let G := fun j k => ∑ i ∈ s, E i j * star (E i k)
  have hEnergyNonneg : (0 : ℝ) ≤ ∑ i ∈ s, ‖Z i‖^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  have hGram : (∑ i ∈ s, ‖Z i‖^2) =
      ‖∑ j ∈ t, ∑ k ∈ t, G j k * B j * star (B k)‖ := by
    calc
      _ = ‖(((∑ i ∈ s, ‖Z i‖^2 : ℝ) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEnergyNonneg]
      _ = _ := congrArg norm (finite_bilinear_gram_identity s t B E)
  have hEnergy : (∑ i ∈ s, ‖Z i‖^2) ≤
      R * (∑ j ∈ t, ‖B j‖^2) := by
    rw [hGram]
    exact complex_gram_schur t G K B R hK hsym hdom hrow
  have hApos : (0 : ℝ) ≤ ∑ i ∈ s, ‖A i‖^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  exact (bilinear_first_cauchy s t A B E).trans
    (mul_le_mul_of_nonneg_left hEnergy hApos)

end Green64SourceC6

end

/-! ## BinSeparation -/

section

namespace Green64SourceC6

/-- A cell of width 1/r cannot contain three circularly separated
fractional phases with pairwise gaps at least 1/(2r). -/
theorem no_three_separated_in_one_cell
    (r x y z : ℝ) (hr : 0 < r)
    (hxy : 1/(2*r) ≤ y-x)
    (hyz : 1/(2*r) ≤ z-y)
    (hcell : z-x < 1/r) : False := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have heq : (1:ℝ)/r = 2*(1/(2*r)) := by
    field_simp
  rw [heq] at hcell
  linarith

/-- The gap lower bound propagates across a sorted triple without
any assumption on the starting position of its containing cell. -/
theorem three_point_span_lower
    (r x y z : ℝ) (hr : 0 < r)
    (hxy : 1/(2*r) ≤ y-x)
    (hyz : 1/(2*r) ≤ z-y) :
    1/r ≤ z-x := by
  have heq : (1:ℝ)/r = 2*(1/(2*r)) := by
    field_simp
  rw [heq]
  linarith

end Green64SourceC6

end

