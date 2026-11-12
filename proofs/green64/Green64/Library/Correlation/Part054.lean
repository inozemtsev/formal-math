module

public import Green64.Library.Weights.Part075
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.RingTheory.Int.Basic
public import Green64.Library.Correlation.Part036
public import Mathlib.Algebra.BigOperators.Associated
public import Green64.Library.Weights.Part074
public import Green64.Library.Weights.Part072
public import Green64.Library.Weights.Part073
public import Green64.Library.Weights.Part071
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Correlation / Part054

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSource03OwnConditionalCharacterGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Exact projected arithmetic character Gram. The coefficient weights
may be the ORIGINAL signed full joint physical K; no separation,
independence, TV envelope, or missing off-diagonal terms. The
remaining pairs are precisely equal-residue collisions in ZMod q. -/
theorem source_original_TRUE_physical_character_collision_Gram434
    {q : ℕ} [NeZero q]
    {I : Type} [DecidableEq I] (F : Finset I)
    (u : I → ZMod q) (w : I → ℂ)
    (hu : ∀ i ∈ F, IsUnit (u i)) :
    (∑ χ : DirichletCharacter ℂ q, ∑ i ∈ F, ∑ j ∈ F,
      (star (w i)*w j) * (χ ((u i)⁻¹)*χ (u j))) =
    (q.totient:ℂ) * (∑ i ∈ F, ∑ j ∈ F,
      if u i = u j then star (w i)*w j else 0) := by
  classical
  calc
    _ = ∑ i ∈ F, ∑ j ∈ F,
         (star (w i)*w j) *
          (∑ χ : DirichletCharacter ℂ q,
            χ ((u i)⁻¹)*χ (u j)) := by
      calc
        _ = ∑ i ∈ F, ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ F,
              (star (w i)*w j) * (χ ((u i)⁻¹)*χ (u j)) := Finset.sum_comm
        _ = ∑ i ∈ F, ∑ j ∈ F, ∑ χ : DirichletCharacter ℂ q,
              (star (w i)*w j) * (χ ((u i)⁻¹)*χ (u j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ i ∈ F, ∑ j ∈ F,
         (star (w i)*w j) * (if u i = u j then (q.totient:ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (hu i hi) (u j)]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalThreeFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- The actual, NOT independent, shared BIG labels from the
physical oriented source state and its same BIG permutation. -/
noncomputable def sourceOriginalPhysicalBIGShared434
    (pat : SourcePattern BG J m)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell)) : ℕ :=
  ∏ g : BG, ∏ i ∈ sourceBigShared J ell m pat g,
    bm g ((x.2 g).1 (bs g i))

/-- The actual independent auxiliary free BIG labels from the
SAME physical source choice and the SAME source pattern. -/
noncomputable def sourceOriginalPhysicalBIGAux434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat) : ℕ :=
  ∏ g : BG, ∏ j : ↥(pat.free g), bm g (aux g j)
/-- The genuine BIG product splits EXACTLY into its source
shared-endpoint product and its auxiliary free product.
This is an algebraic factorization, NOT probabilistic independence. -/
theorem source_original_ACTUAL_PHYSICAL_BIG_shared_aux_split434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell)) :
    sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap pat aux x bs =
    sourceOriginalPhysicalBIGShared434
      SP sm BP bm J ell m cap pat x bs *
    sourceOriginalPhysicalBIGAux434 BP bm J m pat aux := by
  unfold sourceOriginalPhysicalSourceBIGFactor434
    sourceOriginalPhysicalBIGShared434 sourceOriginalPhysicalBIGAux434
  exact Finset.prod_mul_distrib

/-- EXACT original source03 THREE-FACTOR physical divisor:
SHARED SMALL * SHARED BIG * FREE AUXILIARY BIG.
In particular the physically shared SMALL factor cannot be
omitted from the shifted equality, even before any averaging. -/
theorem source_original_ACTUAL_PHYSICAL_D_three_factor434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell)) :
    sourceOrientedPhysicalD SP sm BP bm J ell m cap
      pat aux x bs ss =
    sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss *
      sourceOriginalPhysicalBIGShared434
        SP sm BP bm J ell m cap pat x bs *
      sourceOriginalPhysicalBIGAux434 BP bm J m pat aux := by
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434,
      source_original_ACTUAL_PHYSICAL_BIG_shared_aux_split434]
  ring
/-- The TRUE signed Fourier displacement uses the exact same
three factors, with the ORIGINAL orientation and SAME k.
No replacement of the moving source divisor by BIG-only D. -/
theorem source_original_ACTUAL_PHYSICAL_STEP_three_factor434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (orientation k : ℤ) :
    sourceOrientedStep SP sm BP bm J ell m cap
      pat aux x bs ss orientation k =
    orientation * k *
      (sourceOriginalPhysicalSourceSMALLFactor434
        SP sm BP bm J ell cap x ss : ℤ) *
      (sourceOriginalPhysicalBIGShared434
        SP sm BP bm J ell m cap pat x bs : ℤ) *
      (sourceOriginalPhysicalBIGAux434 BP bm J m pat aux : ℤ) := by
  unfold sourceOrientedStep
  rw [source_original_ACTUAL_PHYSICAL_D_three_factor434]
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ConditionalSmallModulus -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- The true SOURCE03 SMALL modulus of primes not dividing an
actual given shared SMALL factor s. This modulus is path-dependent;
it is NOT a replacement by a fixed independent prime alphabet. -/
noncomputable def sourceOriginalSource03UNMARKEDModulus434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s : ℕ) : ℕ :=
  ((sourceOriginalSource03AllSmall434 z).filter (fun q => ¬q ∣ s)).prod id

/-- The remaining true SMALL primes are precisely chosen not to
divide s, and therefore their entire product is coprime to s.
No distribution theorem is required for this exact identity. -/
theorem source_original_TRUE_source03_UNMARKED_coprime_SMALL434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s : ℕ) :
    Nat.Coprime (sourceOriginalSource03UNMARKEDModulus434 z s) s := by
  unfold sourceOriginalSource03UNMARKEDModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro q hq
  obtain ⟨hqSmall,hnot⟩ := Finset.mem_filter.mp hq
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hqSmall
    rcases Finset.mem_union.mp hqSmall with hs | ht
    · exact ⟨none,hs⟩
    · obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp ht
      exact ⟨some g,hp⟩
  obtain ⟨g,hg⟩ := hgroups
  exact ((z.hSmallBand g q hg).1.coprime_iff_not_dvd).2 hnot
/-- If the full genuine SMALL modulus is coprime to a BIG
factor b, then so is the exact conditional UNMARKED product.
The proof uses TRUE primes and no spurious probabilistic splitting. -/
theorem source_original_TRUE_source03_UNMARKED_coprime_BIG434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s b : ℕ)
    (hbig : Nat.Coprime (sourceOriginalSource03SMALLModulus434 z) b) :
    Nat.Coprime (sourceOriginalSource03UNMARKEDModulus434 z s) b := by
  unfold sourceOriginalSource03UNMARKEDModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro q hq
  obtain ⟨hqSmall, hnotSmall⟩ := Finset.mem_filter.mp hq
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hqSmall
    rcases Finset.mem_union.mp hqSmall with hs | ht
    · exact ⟨none,hs⟩
    · obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp ht
      exact ⟨some g,hp⟩
  obtain ⟨g,hg⟩ := hgroups
  have hp : q.Prime := (z.hSmallBand g q hg).1
  apply (hp.coprime_iff_not_dvd).2
  intro hqB
  have hqQ : q ∣ sourceOriginalSource03SMALLModulus434 z := by
    unfold sourceOriginalSource03SMALLModulus434
    exact Finset.dvd_prod_of_mem id hqSmall
  have hqOne := Nat.eq_one_of_dvd_coprimes hbig hqQ hqB
  exact hp.ne_one hqOne
/-- The actual physical product s*b is a UNIT modulo the
moving conditional SMALL modulus obtained after removing shared
SMALL divisors. Its modulus depends on the true physical s. -/
theorem source_original_TRUE_source03_UNMARKED_coprime_physical_product434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s b : ℕ)
    (hbig : Nat.Coprime (sourceOriginalSource03SMALLModulus434 z) b) :
    Nat.Coprime (sourceOriginalSource03UNMARKEDModulus434 z s)
      (s*b) := by
  apply (Nat.coprime_mul_iff_right).2
  exact ⟨source_original_TRUE_source03_UNMARKED_coprime_SMALL434 z s,
    source_original_TRUE_source03_UNMARKED_coprime_BIG434 z s b hbig⟩

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
/-- The genuine original physical D, including all shared SMALL
marks, becomes a UNIT only AFTER conditioning on those marks
and removing exactly the q dividing the physical SMALL factor.
The BIG alphabet is constrained to the true canonical Tb ranges;
the historical state and auxiliary labels remain physical. -/
theorem source_original_TRUE_source03_PHYSICAL_D_UNMARKED_unit434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell)) :
    Nat.Coprime
      (sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          SP sm BP bm J ell cap x ss))
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap
        pat aux x bs ss) := by
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434]
  apply source_original_TRUE_source03_UNMARKED_coprime_physical_product434
  exact source_original_TRUE_source03_PHYSICAL_BIG_factor_coprime434
    SP sm BP bm J ell m cap z hbig pat aux x bs

/-- Every prime of the TRUE conditional unmarked modulus
exceeds the permitted original |k|, not merely the BIG labels. -/
theorem source_original_TRUE_source03_UNMARKED_coprime_moving_k434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s : ℕ) (k : ℤ) (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    Nat.Coprime (sourceOriginalSource03UNMARKEDModulus434 z s)
      k.natAbs := by
  unfold sourceOriginalSource03UNMARKEDModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro q hq
  obtain ⟨hqSmall, hnot⟩ := Finset.mem_filter.mp hq
  have hgroups : ∃ g : Option (Fin n), q ∈ z.P g := by
    simp only [sourceOriginalSource03AllSmall434] at hqSmall
    rcases Finset.mem_union.mp hqSmall with hs | ht
    · exact ⟨none,hs⟩
    · obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp ht
      exact ⟨some g,hp⟩
  obtain ⟨g,hg⟩ := hgroups
  have hprime : q.Prime := (z.hSmallBand g q hg).1
  apply (hprime.coprime_iff_not_dvd).2
  exact source_original_TRUE_source03_ANY_SMALL_exceeds_shift434
    z g q hg k hk hK hOrigSmall

/-- The ENTIRE authentic physical signed step is a unit in its
own PATH-DEPENDENT UNMARKED prime modulus, for a legal ±1
orientation and the original moving k budget.
Full Qsmall and conditional Qunmarked must not be confused. -/
theorem source_original_TRUE_source03_PHYSICAL_STEP_UNMARKED_unit434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    Nat.Coprime
      (sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          SP sm BP bm J ell cap x ss))
      (sourceOrientedStep SP sm BP bm J ell m cap
        pat aux x bs ss o k).natAbs := by
  have hD := source_original_TRUE_source03_PHYSICAL_D_UNMARKED_unit434
    SP sm BP bm J ell m cap z hbig pat aux x bs ss
  have hKcop := source_original_TRUE_source03_UNMARKED_coprime_moving_k434
    z (sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss) k hk hK hOrigSmall
  have hO : o.natAbs = 1 := by
    rcases ho with h | h
    · simp [h]
    · simp [h]
  have hAbs : (sourceOrientedStep SP sm BP bm J ell m cap
      pat aux x bs ss o k).natAbs =
      k.natAbs * sourceOrientedPhysicalD SP sm BP bm J ell m cap
        pat aux x bs ss := by
    unfold sourceOrientedStep
    simp only [Int.natAbs_mul, Int.natAbs_natCast, hO, one_mul]
  rw [hAbs]
  exact (Nat.coprime_mul_iff_right).2 ⟨hKcop,hD⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ConditionalCharacter -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- The true physical first-DIRTY displacement is NONZERO under
every multiplicative character of the path-conditioned UNMARKED
SMALL modulus, for all original legal ±1 directions and |k| budget.
This is a necessary nonvanishing input for a projected character RMS;
it does NOT establish any RMS power saving or path independence. -/
theorem source_original_TRUE_source03_PHYSICAL_UNMARKED_character_nonzero434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (χ : DirichletCharacter ℂ
      (sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          SP sm BP bm J ell cap x ss))) :
    χ (sourceOrientedStep SP sm BP bm J ell m cap
      pat aux x bs ss o k : ℤ) ≠ 0 := by
  have hcop := source_original_TRUE_source03_PHYSICAL_STEP_UNMARKED_unit434
    SP sm BP bm J ell m cap z hbig pat aux x bs ss o k
    ho hk hK hOrigSmall
  apply (DirichletCharacter.apply_ne_zero_iff χ _).2
  apply (Int.isCoprime_iff_nat_coprime).2
  simpa only [Int.natAbs_natCast, Nat.coprime_comm] using hcop

/-- EXACT multiplicative character decomposition at the
authentic physical source step, using the SAME oriented state:
orientation * moving k * shared SMALL * shared BIG * aux BIG.
This equality is before the physical coefficient, path sum,
signed endpoint projector or Gram square: no factors are
probabilistically independent or estimated here. -/
theorem source_original_TRUE_source03_PHYSICAL_UNMARKED_character_factor434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : GroupPermFamily (G := SG) (J+ell))
    (o k : ℤ)
    (χ : DirichletCharacter ℂ
      (sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          SP sm BP bm J ell cap x ss))) :
    χ (sourceOrientedStep SP sm BP bm J ell m cap
      pat aux x bs ss o k : ℤ) =
    χ o * χ k *
      χ (sourceOriginalPhysicalSourceSMALLFactor434
        SP sm BP bm J ell cap x ss : ℤ) *
      χ (sourceOriginalPhysicalBIGShared434
        SP sm BP bm J ell m cap pat x bs : ℤ) *
      χ (sourceOriginalPhysicalBIGAux434 BP bm J m pat aux : ℤ) := by
  rw [source_original_ACTUAL_PHYSICAL_STEP_three_factor434]
  push_cast
  simp only [map_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ConditionalCharacterOrthogonality -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Every path-conditioned true SMALL modulus is POSITIVE,
even if no unmarked primes survive (empty product = 1).
There is NO hidden nonzero-modulus axiom. -/
theorem source_original_TRUE_source03_UNMARKED_modulus_pos434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s : ℕ) : 0 < sourceOriginalSource03UNMARKEDModulus434 z s := by
  unfold sourceOriginalSource03UNMARKEDModulus434
  apply Finset.prod_pos
  intro q hq
  have hsmall := (Finset.mem_filter.mp hq).1
  simp only [sourceOriginalSource03AllSmall434] at hsmall
  rcases Finset.mem_union.mp hsmall with hS | hTs
  · exact (z.hSmallBand none q hS).1.pos
  · obtain ⟨g,hg,hqg⟩ := Finset.mem_biUnion.mp hTs
    exact (z.hSmallBand (some g) q hqg).1.pos

/-- TRUE Dirichlet-character orthogonality on the moving conditional
SMALL modulus. The left residue must actually be a unit; this holds
for authentic physical BIG labels and the full legal source step.
The equality preserves every congruence collision. -/
theorem source_original_TRUE_source03_UNMARKED_character_orthogonality434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s a b : ℕ)
    (ha : Nat.Coprime (sourceOriginalSource03UNMARKEDModulus434 z s) a) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z s
    ∑ χ : DirichletCharacter ℂ Q,
      χ ((a : ZMod Q)⁻¹) * χ (b : ZMod Q) =
    if (a : ZMod Q) = (b : ZMod Q) then (Q.totient : ℂ) else 0 := by
  dsimp only
  let Q := sourceOriginalSource03UNMARKEDModulus434 z s
  letI : NeZero Q :=
    ⟨Nat.ne_of_gt (source_original_TRUE_source03_UNMARKED_modulus_pos434 z s)⟩
  have hunit : IsUnit (a : ZMod Q) := by
    apply (ZMod.isUnit_iff_coprime a Q).2
    exact ha.symm
  exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit
    (b : ZMod Q)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalConditionalCollisionGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- TRUE conditional character Gram of ORIGINAL physical oriented
source choices, WITHIN ONE fixed actual shared-SMALL factor s.
The weights may contain the complete joint RAW/COMPARISON
physical coefficient (including complex signs and Fock history).
All same-residue off-diagonal pairs are retained. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_conditional_collision_gram434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (F : Finset (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x))
    (s : ℕ)
    (hs : ∀ ch ∈ F,
      sourceOriginalPhysicalSourceSMALLFactor434
        SP sm BP bm J ell cap x ch.2.2.2.1 = s)
    (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (w : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ℂ) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z s
    let v : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ZMod Q :=
      fun ch => (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k : ZMod Q)
    (∑ χ : DirichletCharacter ℂ Q,
      ∑ ch ∈ F, ∑ ch' ∈ F,
        (star (w ch)*w ch') *
          (χ ((v ch)⁻¹)*χ (v ch'))) =
    (Q.totient:ℂ) *
      (∑ ch ∈ F, ∑ ch' ∈ F,
        if v ch = v ch' then star (w ch)*w ch' else 0) := by
  dsimp only
  let Q := sourceOriginalSource03UNMARKEDModulus434 z s
  letI : NeZero Q :=
    ⟨Nat.ne_of_gt
      (source_original_TRUE_source03_UNMARKED_modulus_pos434 z s)⟩
  apply source_original_TRUE_physical_character_collision_Gram434
  intro ch hch
  have hc := source_original_TRUE_source03_PHYSICAL_STEP_UNMARKED_unit434
    SP sm BP bm J ell m cap z hbig (patterns ch.1)
    ch.2.1 x ch.2.2.1.sigmaBig ch.2.2.2.1 o k
    ho hk hK hOrigSmall
  rw [hs ch hch] at hc
  apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).2
  apply (Int.isCoprime_iff_nat_coprime).2
  simpa only [Int.natAbs_natCast, Nat.coprime_comm] using hc
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalCoefficientConditionalGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2600000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- ACTUAL legal source E-choices, conditioned on their own true
shared SMALL source factor. The legal Fock, OLD/promotion, auxiliary
bans and both source permutations are retained before filtering. -/
noncomputable def sourceOriginalPhysicalSameSharedChoices434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (o k : ℤ) (s : ℕ) :
    Finset (FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :=
  (sourceOrientedPhysicalChoices SP sm BP bm J ell m cap
     patterns x o k).filter (fun ch =>
    sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ch.2.2.2.1 = s)
/-- Exact original PHYSICAL E source coefficient, including the
SAME joint Knu, both small/big endpoint permutation averages, true
BIG source auxiliaries and arbitrary future Fock/output observable.
The signed complex weight is not replaced by its absolute value. -/
noncomputable def sourceOriginalPhysicalFutureWeight434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (future : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ)
    (ch : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) : ℂ :=
  sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
    q rho Vs Vb mu Knu zeta theta o k x ch *
  future (sourceOrientedPhysicalOutput SP sm BP bm
    J ell m cap patterns x o k ch)

/-- The exact conditionally-character-averaged Gram of the TRUE
original signed physical E coefficient, on every fixed shared-SMALL
stratum. Same-residue OFF-DIAGONAL terms are retained. This does not
assert character equidistribution, correlation saving, or a result
for the combined unconditioned Fock x seen chronological Gram. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_future_conditional_Gram434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (future : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ)
    (s : ℕ) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z s
    let F := sourceOriginalPhysicalSameSharedChoices434
      SP sm BP bm J ell m cap patterns x o k s
    let v : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ZMod Q :=
      fun ch => (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k : ZMod Q)
    let w : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ℂ :=
      sourceOriginalPhysicalFutureWeight434
        SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k x future
    (∑ χ : DirichletCharacter ℂ Q,
      ∑ ch ∈ F, ∑ ch' ∈ F,
        (star (w ch)*w ch') *
          (χ ((v ch)⁻¹)*χ (v ch'))) =
    (Q.totient:ℂ) * (∑ ch ∈ F, ∑ ch' ∈ F,
       if v ch = v ch' then star (w ch)*w ch' else 0) := by
  dsimp only
  apply source_original_TRUE_SOURCE03_PHYSICAL_conditional_collision_gram434
    SP sm BP bm J ell m cap patterns z hbig x
    (sourceOriginalPhysicalSameSharedChoices434
      SP sm BP bm J ell m cap patterns x o k s) s
    (by
      intro ch hch
      exact (Finset.mem_filter.mp hch).2)
    o k ho hk hK hOrigSmall
    (sourceOriginalPhysicalFutureWeight434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k x future)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalConditionalBigCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2700000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- In one authentic path-conditioned SMALL stratum s, the common
physical factor o*k*s is a UNIT of the conditional unmarked modulus.
It can be cancelled from congruences BETWEEN physical source edges.
This keeps both physical BIG factors inside the same true source K. -/
theorem source_original_TRUE_SOURCE03_conditional_common_factor_unit434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (s : ℕ) (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    IsUnit ((o*k*(s:ℤ)):ZMod
       (sourceOriginalSource03UNMARKEDModulus434 z s)) := by
  let Q := sourceOriginalSource03UNMARKEDModulus434 z s
  have hs := source_original_TRUE_source03_UNMARKED_coprime_SMALL434 z s
  have hkcop := source_original_TRUE_source03_UNMARKED_coprime_moving_k434
    z s k hk hK hOrigSmall
  have hoabs : o.natAbs = 1 := by
    rcases ho with h | h
    · simp [h]
    · simp [h]
  have hcop : Nat.Coprime Q (o*k*(s:ℤ)).natAbs := by
    have hh : (o*k*(s:ℤ)).natAbs = k.natAbs*s := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast, hoabs, one_mul]
    rw [hh]
    exact (Nat.coprime_mul_iff_right).2 ⟨hkcop,hs⟩
  have hunit : IsUnit (((o*k*(s:ℤ)):ℤ) : ZMod Q) := by
    apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).2
    apply (Int.isCoprime_iff_nat_coprime).2
    simpa only [Int.natAbs_natCast, Nat.coprime_comm] using hcop
  simpa only [Int.cast_mul, Int.cast_natCast] using hunit

/-- With its own actual shared-SMALL factor fixed to s, the exact
oriented Fourier displacement is the common unit o*k*s multiplied
by the true physical shared/auxiliary BIG product. No pure-BIG
comparison substitution is used. -/
theorem source_original_TRUE_SOURCE03_fixed_small_step_factor434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ch : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (s : ℕ) (hs : sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ch.2.2.2.1 = s)
    (o k : ℤ) :
    sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
      ch.2.2.2.1 o k =
    o*k*(s:ℤ)*
      (sourceOriginalPhysicalSourceBIGFactor434
        SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig:ℤ) := by
  unfold sourceOrientedStep
  rw [source_original_ACTUAL_PHYSICAL_D_SMALL_TIMES_BIG434,hs]
  push_cast
  ring

/-- Actual physical edge pairs within ONE shared-SMALL fibre have
the SAME integer Fourier frequency modulo the conditional modulus
IFF their TRUE physical BIG products have the same residue.
This equivalence retains all same-frequency collisions. -/
theorem source_original_TRUE_SOURCE03_conditional_step_collision_iff_BIG434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ch ch' : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (s : ℕ)
    (hs : sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ch.2.2.2.1 = s)
    (hs' : sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ch'.2.2.2.1 = s)
    (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z s
    ((sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
      ch.2.2.2.1 o k:ℤ):ZMod Q) =
    ((sourceOrientedStep SP sm BP bm J ell m cap
      (patterns ch'.1) ch'.2.1 x ch'.2.2.1.sigmaBig
      ch'.2.2.2.1 o k:ℤ):ZMod Q) ↔
    ((sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap
      (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig:ℕ):ZMod Q) =
    ((sourceOriginalPhysicalSourceBIGFactor434
      SP sm BP bm J ell m cap
      (patterns ch'.1) ch'.2.1 x ch'.2.2.1.sigmaBig:ℕ):ZMod Q) := by
  dsimp only
  have hunit := source_original_TRUE_SOURCE03_conditional_common_factor_unit434
    z s o k ho hk hK hOrigSmall
  rw [source_original_TRUE_SOURCE03_fixed_small_step_factor434
    SP sm BP bm J ell m cap patterns x ch s hs o k,
    source_original_TRUE_SOURCE03_fixed_small_step_factor434
    SP sm BP bm J ell m cap patterns x ch' s hs' o k]
  push_cast
  simpa only [Int.cast_mul, Int.cast_natCast] using
    (hunit.mul_right_inj)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalConditionalBIGGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exact character mean-square collision identity of the ACTUAL
SOURCE oriented physical coefficient with original joint Knu,
Fock/OLD legality, independent physical permutations, complete
shared-BIG and free auxiliary BIG marks, and the original
terminal future observable. Every off-diagonal BIG-product
collision remains with its TRUE complex signed weight.
The common physical SMALL and moving shift factors cancel
ONLY within a fixed true shared-SMALL stratum; this is not a
comparison replacement and yields no bound by itself. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_future_BIG_collision_Gram434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (hbig : ∀ (g : BG) (p : BP g),
      ∃ i : Fin n, bm g p ∈ z.Tb i)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (hk : 0 < k.natAbs)
    (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
    (future : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ)
    (s : ℕ) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z s
    let F := sourceOriginalPhysicalSameSharedChoices434
      SP sm BP bm J ell m cap patterns x o k s
    let v : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ZMod Q :=
      fun ch => (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 o k : ZMod Q)
    let B : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ZMod Q :=
      fun ch => (sourceOriginalPhysicalSourceBIGFactor434
        SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig : ZMod Q)
    let w : (FullOrientedSourceChoice
      SP sm BP bm J ell m cap patterns x) → ℂ :=
      sourceOriginalPhysicalFutureWeight434
        SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k x future
    (∑ χ : DirichletCharacter ℂ Q,
      ∑ ch ∈ F, ∑ ch' ∈ F,
        (star (w ch)*w ch') *
          (χ ((v ch)⁻¹)*χ (v ch'))) =
    (Q.totient:ℂ) *
      (∑ ch ∈ F, ∑ ch' ∈ F,
        if B ch = B ch' then star (w ch)*w ch' else 0) := by
  have h := source_original_TRUE_SOURCE03_PHYSICAL_future_conditional_Gram434
    SP sm BP bm J ell m cap patterns
    z hbig x q rho Vs Vb mu Knu zeta theta o k
    ho hk hK hOrigSmall future s
  dsimp only at h ⊢
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro ch hch
  apply Finset.sum_congr rfl
  intro ch' hch'
  have hs : sourceOriginalPhysicalSourceSMALLFactor434
    SP sm BP bm J ell cap x ch.2.2.2.1 = s :=
    (Finset.mem_filter.mp hch).2
  have hs' : sourceOriginalPhysicalSourceSMALLFactor434
    SP sm BP bm J ell cap x ch'.2.2.2.1 = s :=
    (Finset.mem_filter.mp hch').2
  have hiff := source_original_TRUE_SOURCE03_conditional_step_collision_iff_BIG434
    SP sm BP bm J ell m cap patterns z x ch ch' s
    hs hs' o k ho hk hK hOrigSmall
  dsimp only at hiff
  simpa only [hiff]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ActualSharedSmallCapacity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- TRUE marked prime SUPPORT of one original source's SMALL
factor, across every group and the actual SMALL endpoint
permutation. Repeated marks are deduplicated only for counting. -/
noncomputable def sourceOriginalActualSharedSmallPrimeLabels434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ss : GroupPermFamily (G := SG) (J+ell)) : Finset ℕ :=
  (Finset.univ : Finset SG).biUnion (fun g =>
    (sourceSmallShared J ell g).image (fun j =>
      sm g (marks (sm g) (J+ell) (x.1 g) (ss g j))))
/-- A prime divides the genuine physical shared-SMALL source
factor IFF it occurs among the original physical marked labels.
This equivalence is exact even with repeated active marks. -/
theorem source_original_ACTUAL_shared_SMALL_prime_dvd_iff_selected434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ss : GroupPermFamily (G := SG) (J+ell))
    (hprime : ∀ g (p : SP g), (sm g p).Prime)
    (q : ℕ) (hq : q.Prime) :
    q ∣ sourceOriginalPhysicalSourceSMALLFactor434
      SP sm BP bm J ell cap x ss ↔
    q ∈ sourceOriginalActualSharedSmallPrimeLabels434
      SP sm BP bm J ell cap x ss := by
  classical
  constructor
  · intro hd
    change q ∣ ∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
      sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)) at hd
    obtain ⟨g,hg,hgd⟩ :=
      (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)
        (fun g : SG => ∏ j ∈ sourceSmallShared J ell g,
          sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)))).mp hd
    obtain ⟨j,hj,hjd⟩ :=
      (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)
        (fun j : Fin (J+ell) =>
          sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)))).mp hgd
    have hEq : q = sm g (marks (sm g) (J+ell)
        (x.1 g) (ss g j)) :=
      (Nat.prime_dvd_prime_iff_eq hq
        (hprime g (marks (sm g) (J+ell) (x.1 g) (ss g j)))).mp hjd
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j,hj,hEq.symm⟩⟩
  · intro h
    obtain ⟨g,hg,himg⟩ := Finset.mem_biUnion.mp
      (show q ∈ sourceOriginalActualSharedSmallPrimeLabels434
        SP sm BP bm J ell cap x ss from h)
    obtain ⟨j,hj,hEq⟩ := Finset.mem_image.mp himg
    change q ∣ ∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
      sm g (marks (sm g) (J+ell) (x.1 g) (ss g j))
    rw [← hEq]
    exact dvd_trans
      (Finset.dvd_prod_of_mem
        (fun j : Fin (J+ell) =>
          sm g (marks (sm g) (J+ell) (x.1 g) (ss g j))) hj)
      (Finset.dvd_prod_of_mem
        (fun g : SG => ∏ j ∈ sourceSmallShared J ell g,
          sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)))
        (Finset.mem_univ g))

/-- Without any distinctness or independence assumption, at most
(card SMALL-groups)*(J+ell) different true prime labels occur in
the actual shared-SMALL source factor. -/
theorem source_original_ACTUAL_shared_SMALL_prime_support_card_le434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (ss : GroupPermFamily (G := SG) (J+ell)) :
    (sourceOriginalActualSharedSmallPrimeLabels434
      SP sm BP bm J ell cap x ss).card ≤
        Fintype.card SG * (J+ell) := by
  classical
  unfold sourceOriginalActualSharedSmallPrimeLabels434
  calc
    _ ≤ ∑ g : SG, ((sourceSmallShared J ell g).image (fun j =>
       sm g (marks (sm g) (J+ell) (x.1 g) (ss g j)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ g : SG, (sourceSmallShared J ell g).card := by
      apply Finset.sum_le_sum
      intro g hg
      exact Finset.card_image_le
    _ ≤ ∑ _g : SG, (J+ell) := by
      apply Finset.sum_le_sum
      intro g hg
      have hsub : sourceSmallShared J ell g ⊆
          (Finset.univ : Finset (Fin (J+ell))) :=
        Finset.subset_univ _
      simpa using (Finset.card_le_card hsub)
    _ = _ := by simp [nsmul_eq_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalUnmarkedPrime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A REAL SMALL prime from the distinguished canonical S survives
the PHYSICAL shared source marks once the TRUE S cardinality
exceeds the maximum (n+1)*(J+ell) actual SMALL mark slots.
No iid prime assumption or free prime selection is introduced. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_exists_unmarked_SMALL_prime434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell : ℕ) (cap : Fin n → ℕ)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ss : GroupPermFamily (G := Option (Fin n)) (J+ell))
    (hcapacity : (n+1)*(J+ell) < z.S.card) :
    ∃ q ∈ z.S, ¬ q ∣ sourceOriginalPhysicalSourceSMALLFactor434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell cap x ss := by
  classical
  let SP := sourceOriginalSource03CanonicalSmallCarrier434 z
  let BP := sourceOriginalSource03CanonicalBigCarrier434 z
  let Sused := sourceOriginalActualSharedSmallPrimeLabels434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap x ss
  have hsupport : Sused.card ≤ (n+1)*(J+ell) := by
    have hh := source_original_ACTUAL_shared_SMALL_prime_support_card_le434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ss
    simpa [Sused] using hh
  have hnsubset : ¬ z.S ⊆ Sused := by
    intro hsubset
    have hle := Finset.card_le_card hsubset
    omega
  obtain ⟨q,hqS,hqNot⟩ := Finset.not_subset.mp hnsubset
  refine ⟨q,hqS,?_⟩
  intro hdvd
  have hprime : q.Prime := (z.hSmallBand none q hqS).1
  have htyped : ∀ g (p : SP g), (p.val).Prime :=
    fun g p => (z.hSmallBand g p.val p.property).1
  have hiff := source_original_ACTUAL_shared_SMALL_prime_dvd_iff_selected434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap x ss htyped q hprime
  exact hqNot (hiff.mp hdvd)
/-- Quantitative GENUINE conditional modulus lower bound from
a surviving prime of true S. This is not a synthetic lower
modulus assumption: the only finite input is the number of
actual SMALL shared mark slots versus true source03 S size. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_unmarked_modulus_lower434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell : ℕ) (cap : Fin n → ℕ)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ss : GroupPermFamily (G := Option (Fin n)) (J+ell))
    (hcapacity : (n+1)*(J+ell) < z.S.card) :
    Real.exp (L^cfg.aexp) ≤
      (sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ss):ℝ) := by
  obtain ⟨q,hqS,hqNot⟩ :=
    source_original_TRUE_SOURCE03_PHYSICAL_exists_unmarked_SMALL_prime434
      z J ell cap x ss hcapacity
  let s := sourceOriginalPhysicalSourceSMALLFactor434
    (sourceOriginalSource03CanonicalSmallCarrier434 z)
    (fun _ p => p.val)
    (sourceOriginalSource03CanonicalBigCarrier434 z)
    (fun _ p => p.val) J ell cap x ss
  let Q := sourceOriginalSource03UNMARKEDModulus434 z s
  have hqmem : q ∈ (sourceOriginalSource03AllSmall434 z).filter
      (fun r => ¬ r ∣ s) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_union.mpr (Or.inl hqS),hqNot⟩
  have hqQ : q ∣ Q := by
    change q ∣ ((sourceOriginalSource03AllSmall434 z).filter
      (fun r => ¬ r ∣ s)).prod id
    exact Finset.dvd_prod_of_mem id hqmem
  have hQpos : 0 < Q :=
    source_original_TRUE_source03_UNMARKED_modulus_pos434 z s
  have hnat : q ≤ Q := Nat.le_of_dvd hQpos hqQ
  exact (z.hSmallBand none q hqS).2.1.trans (by exact_mod_cast hnat)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TrueSMALLSpectralScale -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Genuine canonical source03 distinguished S has exact
reciprocal harmonic mass. The full SMALL prime product thus has
an unconditional superexponential lower bound
exp(L^a * exp(L^a) * cfg.vmin).
For nonpositive L^a the bound follows trivially from Q >= 1;
no unjustified assertion L > 0 from log L > 0 (negative L can
also have positive logarithm in Real.log) is made. -/
theorem source_original_TRUE_CANONICAL_source03_SMALL_superexp_modulus434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0) :
    Real.exp (L^cfg.aexp * (Real.exp (L^cfg.aexp) * cfg.vmin)) ≤
      (sourceOriginalSource03SMALLModulus434 z : ℝ) := by
  let A : ℝ := L^cfg.aexp
  let S := z.S
  let P := sourceOriginalSource03AllSmall434 z
  have hprimes : ∀ q ∈ P, q.Prime := by
    intro q hq
    change q ∈ z.S ∪
      ((Finset.univ : Finset (Fin n)).biUnion z.Ts) at hq
    rcases Finset.mem_union.mp hq with hs | hts
    · exact (z.hSmallBand none q hs).1
    · obtain ⟨g,hg,hqg⟩ := Finset.mem_biUnion.mp hts
      exact (z.hSmallBand (some g) q hqg).1
  have hQpos : 0 < P.prod id := by
    apply Finset.prod_pos
    intro q hq
    exact (hprimes q hq).pos
  have hQone : (1:ℝ) ≤ ((P.prod id : ℕ) : ℝ) := by
    exact_mod_cast hQpos
  by_cases hA : 0 ≤ A
  · have hcard : Real.exp A * cfg.vmin ≤ (S.card:ℝ) := by
      exact source_original_CANONICAL_true_SMALL_card_lower434 z none
    have hcardexp : Real.exp (A * (Real.exp A * cfg.vmin)) ≤
        Real.exp (A * (S.card:ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hcard hA
    have hpow : Real.exp (A * (S.card:ℝ)) = (Real.exp A)^S.card := by
      calc
        _ = Real.exp ((S.card:ℝ)*A) := by ring
        _ = _ := Real.exp_nat_mul A S.card
    have hSprod : (Real.exp A)^S.card ≤ ((S.prod id:ℕ):ℝ) := by
      calc
        _ = ∏ q ∈ S, Real.exp A := by simp only [Finset.prod_const]
        _ ≤ ∏ q ∈ S, (q:ℝ) := by
          apply Finset.prod_le_prod₀
          · intro q hq
            exact (Real.exp_pos _).le
          · intro q hq
            exact (z.hSmallBand none q hq).2.1
        _ = ((S.prod id:ℕ):ℝ) := by
          simp only [Nat.cast_prod]
          rfl
    have hSubset : S ⊆ P := Finset.subset_union_left
    have hSdiv : S.prod id ∣ P.prod id :=
      Finset.prod_dvd_prod_of_subset S P id hSubset
    have hSle : S.prod id ≤ P.prod id := Nat.le_of_dvd hQpos hSdiv
    calc
      _ ≤ Real.exp (A * (S.card:ℝ)) := hcardexp
      _ = (Real.exp A)^S.card := hpow
      _ ≤ ((S.prod id:ℕ):ℝ) := hSprod
      _ ≤ ((P.prod id:ℕ):ℝ) := by exact_mod_cast hSle
      _ = _ := rfl
  · have hAneg : A ≤ 0 := le_of_lt (lt_of_not_ge hA)
    have hbody : A * (Real.exp A * cfg.vmin) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAneg
        (mul_nonneg (Real.exp_pos A).le cfg.hv.le)
    calc
      _ ≤ (1:ℝ) := Real.exp_le_one_iff.mpr hbody
      _ ≤ ((P.prod id:ℕ):ℝ) := hQone
      _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalMatchedSpectralScale -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The REAL original comparison data with all six source prime
group fields equal to the canonical prime slice has literally
THE SAME complete original S+Ts spectral modulus. -/
theorem source_original_TRUE_CANONICAL_MATCH_actual_SMALL_modulus_eq434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    sourceOriginalActualSourceALLSmallModulus434 u =
      sourceOriginalSource03SMALLModulus434 z := by
  rcases hmatch with ⟨hS,hTs,_,_,_,_⟩
  unfold sourceOriginalActualSourceALLSmallModulus434
    sourceOriginalSource03SMALLModulus434 sourceOriginalSource03AllSmall434
  rw [hS,hTs]
/-- Superexponentially growing physical source03 TOTAL SMALL
spectral modulus for TRUE constructed group data. This is a
conclusion of canonical-field equality, not an assumption of
independent group sampling or of arbitrary harmonic V. -/
theorem source_original_TRUE_CANONICAL_MATCH_actual_SMALL_superexp434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    Real.exp (L^cfg.aexp * (Real.exp (L^cfg.aexp) * cfg.vmin)) ≤
      (sourceOriginalActualSourceALLSmallModulus434 u : ℝ) := by
  rw [source_original_TRUE_CANONICAL_MATCH_actual_SMALL_modulus_eq434 z u hmatch]
  exact source_original_TRUE_CANONICAL_source03_SMALL_superexp_modulus434 z

/-- The original source03 canonical-replacement comparison
constructor actually inherits the full true superexponential
SMALL spectral modulus. The ONLY extra arguments are those
needed to build that same SOURCE endpoint from existing fields. -/
theorem source_original_TRUE_CANONICAL_REPLACED_SMALL_superexp434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 1 < L) (hd : d < (1/2:ℝ)) (hcd : cfg.cexp < d)
    (hSN : ∀ p∈z.S, p ≤ u.Ncap)
    (PtwNew : Finset ℕ) (hParityNew : PtwNew ⊆ z.G) :
    Real.exp (L^cfg.aexp * (Real.exp (L^cfg.aexp) * cfg.vmin)) ≤
      (sourceOriginalActualSourceALLSmallModulus434
        (sourceOriginalCanonicalComparisonReplaceGroups434
          z u hL hd hcd hSN PtwNew hParityNew) : ℝ) := by
  apply source_original_TRUE_CANONICAL_MATCH_actual_SMALL_superexp434 z
    (sourceOriginalCanonicalComparisonReplaceGroups434
      z u hL hd hcd hSN PtwNew hParityNew)
  exact source_original_canonical_replacement_real_fields434
    z u hL hd hcd hSN PtwNew hParityNew
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalMatchedFullShiftGap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Under a TRUE certified canonical prime-group match, not
only distinguished S but EVERY genuine SMALL prime of Ts is
larger than the ORIGINAL moving Fourier shift |k|.
Therefore the WHOLE REAL SMALL modulus is coprime to |k|. -/
theorem source_original_TRUE_CANONICAL_MATCH_ALL_SMALL_coprime_k434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (k : ℤ) (hk : 0 < k.natAbs)
    (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc) :
    Nat.Coprime (sourceOriginalActualSourceALLSmallModulus434 u)
      k.natAbs := by
  rw [source_original_TRUE_CANONICAL_MATCH_actual_SMALL_modulus_eq434 z u hmatch]
  unfold sourceOriginalSource03SMALLModulus434
  apply (Nat.coprime_prod_left_iff).2
  intro p hp
  have hpg : ∃ g : Option (Fin n), p ∈ z.P g := by
    unfold sourceOriginalSource03AllSmall434 at hp
    rcases Finset.mem_union.mp hp with hs | hts
    · exact ⟨none, hs⟩
    · obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hts
      exact ⟨some g, hpg⟩
  obtain ⟨g,hpg⟩ := hpg
  apply ((z.hSmallBand g p hpg).1.coprime_iff_not_dvd).2
  exact source_original_TRUE_source03_ANY_SMALL_exceeds_shift434
    z g p hpg k hk hkBound u.hOrigSmall

/-- The EXACT true source03 signed FULL first-DIRTY physical
chronology, when constructed from canonical certified primes, has
a JOINT frequency lattice of modulus
Q_SMALL * |k| (NOT merely lcm), for TWO physical paths whose
S+Ts initial and final SMALL tori coincide. -/
theorem source_original_TRUE_CANONICAL_MATCH_DIRTY_FULL_SMALL_times_k434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hstarts : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) :
    sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs ∣
      (freq-freq').natAbs := by
  have hQ := source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p q freq freq' hstarts hends hnp hnq
  have hk1 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p freq hnp
  have hk2 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q freq' hnq
  have hkd : k.natAbs ∣ (freq-freq').natAbs :=
    (Int.natAbs_dvd_natAbs).mpr (dvd_sub hk1 hk2)
  exact (source_original_TRUE_CANONICAL_MATCH_ALL_SMALL_coprime_k434
    z u hmatch k hk hkBound).mul_dvd_of_dvd_of_dvd hQ hkd

/-- Quantitative TRUE source03 canonical physical spectral gap
on the actual joint RAW/comparison first-DIRTY Fock×seen path
amplitudes, with full BIG prime bands and alternating signs:
distinct total modes require at least
|k| * exp(L^a * exp(L^a) * cfg.vmin) separation,
PROVIDED the two paths match at both SMALL torus endpoints.
This is arithmetic spacing; it does NOT yet imply log saving. -/
theorem source_original_TRUE_CANONICAL_MATCH_DIRTY_superexp_gap434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hstarts : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0)
    (hneq : freq ≠ freq') :
    (k.natAbs:ℝ) *
      Real.exp (L^cfg.aexp * (Real.exp (L^cfg.aexp)*cfg.vmin)) ≤
      ((freq-freq').natAbs:ℝ) := by
  have hdiv :=
    source_original_TRUE_CANONICAL_MATCH_DIRTY_FULL_SMALL_times_k434
      z u hmatch blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hk hkBound
      p q freq freq' hstarts hends hnp hnq
  have hpos : 0 < (freq-freq').natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hneq)
  have hle :
      sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs ≤
        (freq-freq').natAbs := Nat.le_of_dvd hpos hdiv
  calc
    _ ≤ (k.natAbs:ℝ) *
        (sourceOriginalActualSourceALLSmallModulus434 u:ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (source_original_TRUE_CANONICAL_MATCH_actual_SMALL_superexp434 z u hmatch)
        (Nat.cast_nonneg k.natAbs)
    _ = ((sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs : ℕ):ℝ) := by
      push_cast
      ring
    _ ≤ ((freq-freq').natAbs:ℝ) := by exact_mod_cast hle
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalMatchedKCancelledNoReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Strongest presently available physical chronological
NO-FREQUENCY-RETURN criterion for REAL canonical source03:
the ENTIRE original S+Ts SMALL product dominates twice the
chronological physical E-divisor total radius AFTER |k| cancellation.
This keeps the original arbitrary nonzero moving k, matched true
canonical groups, all Fock×seen states, four signed original K
channels, and the two OLD gates. It does NOT establish the
arithmetic size premise nor a same-frequency signed Gram saving. -/
theorem source_original_TRUE_CANONICAL_MATCH_DIRTY_k_cancelled_no_return434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hwindow :
      2*(2*R)*sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k <
          sourceOriginalActualSourceALLSmallModulus434 u)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hstarts : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option (Fin n),
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) : freq = freq' := by
  let M := sourceOriginalActualSourceGEDualDivisorCap434
    u blockA blockB J ell m hmJ k
  let B := (2*R)*(k.natAbs*M)
  have hd : freq.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq hnp
  have he : freq'.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' hnq
  have hsmall : (freq-freq').natAbs ≤ (2*(2*R)*M)*k.natAbs := by
    calc
      (freq-freq').natAbs ≤ freq.natAbs+freq'.natAbs :=
        Int.natAbs_sub_le freq freq'
      _ ≤ B+B := Nat.add_le_add hd he
      _ = (2*(2*R)*M)*k.natAbs := by
        dsimp [B]
        ring
  have hstrict :
      (2*(2*R)*M)*k.natAbs <
        sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs :=
    Nat.mul_lt_mul_of_pos_right hwindow hk
  by_contra hneq
  have hdiv := source_original_TRUE_CANONICAL_MATCH_DIRTY_FULL_SMALL_times_k434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hk hkBound
    p q freq freq' hstarts hends hnp hnq
  have hpos : 0 < (freq-freq').natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hneq)
  have hlower :
      sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs ≤
        (freq-freq').natAbs := Nat.le_of_dvd hpos hdiv
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03RelativeKCancelledNoReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Without matching ANY physical starting or ending SMALL torus,
equality of genuine RELATIVE S+Ts torus displacement forces the
difference of the two TRUE signed first-DIRTY chronological modes
into the FULL SMALL times |k| integer lattice, provided canonical
source prime groups and original moving arc k are used. -/
theorem source_original_TRUE_CANONICAL_MATCH_DIRTY_relative_SMALL_times_k434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hrelative : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R p = sourceOriginalActualSourceDIRTYRelativeTorus434
        u J ell R q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) :
    sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs ∣
      (freq-freq').natAbs := by
  have hQ := source_original_ACTUAL_SOURCE_DIRTY_equal_relative_ALL_SMALL_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    p q freq freq' hrelative hnp hnq
  have hk1 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T p freq hnp
  have hk2 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T q freq' hnq
  have hkd : k.natAbs ∣ (freq-freq').natAbs :=
    (Int.natAbs_dvd_natAbs).mpr (dvd_sub hk1 hk2)
  exact (source_original_TRUE_CANONICAL_MATCH_ALL_SMALL_coprime_k434
    z u hmatch k hk hkBound).mul_dvd_of_dvd_of_dvd hQ hkd
/-- ACTUAL source03 same-relative-torus paths cannot support
different total frequencies once the S+Ts modulus dominates the
genuine physical 2R-step E-divisor radius, with |k| CANCELLED.
Unlike the earlier matched-endpoint theorem, start and end torus
states may differ ARBITRARILY between the two Fock×seen paths. -/
theorem source_original_TRUE_CANONICAL_MATCH_DIRTY_relative_k_cancelled_no_return434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hwindow :
      2*(2*R)*sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k <
          sourceOriginalActualSourceALLSmallModulus434 u)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq freq' : ℤ)
    (hrelative : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R p = sourceOriginalActualSourceDIRTYRelativeTorus434
        u J ell R q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' ≠ 0) :
    freq = freq' := by
  let M := sourceOriginalActualSourceGEDualDivisorCap434
    u blockA blockB J ell m hmJ k
  let B := (2*R)*(k.natAbs*M)
  have hd : freq.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq hnp
  have he : freq'.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q freq' hnq
  have hsmall : (freq-freq').natAbs ≤
      (2*(2*R)*M)*k.natAbs := by
    calc
      _ ≤ freq.natAbs+freq'.natAbs := Int.natAbs_sub_le freq freq'
      _ ≤ B+B := Nat.add_le_add hd he
      _ = (2*(2*R)*M)*k.natAbs := by dsimp [B]; ring
  have hstrict :
      (2*(2*R)*M)*k.natAbs <
        sourceOriginalActualSourceALLSmallModulus434 u*k.natAbs :=
    Nat.mul_lt_mul_of_pos_right hwindow hk
  by_contra hneq
  have hdiv := source_original_TRUE_CANONICAL_MATCH_DIRTY_relative_SMALL_times_k434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hk hkBound
    p q freq freq' hrelative hnp hnq
  have hpos : 0 < (freq-freq').natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hneq)
  have hlower :
      sourceOriginalActualSourceALLSmallModulus434 u * k.natAbs ≤
        (freq-freq').natAbs := Nat.le_of_dvd hpos hdiv
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03UnmarkedEventualCapacity -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Elementary genuine source03 growth, with NO Mertens .olean:
for every positive exponent a and true vmin, exp(L^a)*vmin
eventually dominates any FIXED multiple of log L.
This will discharge the actual chronological shared-mark budget. -/
theorem eventually_source_original_exp_rpow_dominates_log_budget434
    (a vmin C0 : ℝ) (ha : 0 < a) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) (H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (C0*Real.log L+1)*(H:ℝ) < Real.exp (L^a)*vmin := by
  let C : ℝ := ((H:ℝ)+1)*(C0+1)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by positivity) (by linarith)
  let c : ℝ := vmin/(4*C)
  have hc : 0 < c := div_pos hv (mul_pos (by norm_num) hC)
  filter_upwards [(isLittleO_log_rpow_atTop ha).bound hc,
    eventually_ge_atTop (Real.exp 1)] with L hlogbd hL
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa using hh
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hLp : 0 ≤ L := le_trans (Real.exp_pos 1).le hL
  have hp0 : 0 ≤ L^a := Real.rpow_nonneg hLp _
  have hlogle : Real.log L ≤ c * L^a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hp0] using hlogbd
  have hA : C0*Real.log L+1 ≤ (C0+1)*(Real.log L+1) := by
    nlinarith [mul_nonneg hC0 hlog0]
  have hA0 : 0 ≤ (C0+1)*(Real.log L+1) := by positivity
  have hB : (0:ℝ) ≤ (H:ℝ) := Nat.cast_nonneg _
  have hB' : (H:ℝ) ≤ (H:ℝ)+1 := by linarith
  have hcoeff : (C0*Real.log L+1)*(H:ℝ) ≤
      C*(Real.log L+1) := by
    have h1 := mul_le_mul_of_nonneg_right hA hB
    have h2 := mul_le_mul_of_nonneg_left hB' hA0
    dsimp [C]
    nlinarith [h1,h2]
  have htwolog : Real.log L+1 ≤ 2*Real.log L := by linarith
  have htwoc : C*(Real.log L+1) ≤ 2*C*Real.log L := by
    convert mul_le_mul_of_nonneg_left htwolog hC.le using 1 <;> ring
  have hbound : 2*C*Real.log L ≤ (vmin/2)*L^a := by
    have hh := mul_le_mul_of_nonneg_left hlogle (by positivity : 0 ≤ 2*C)
    dsimp [c] at hh
    have hid : (2*C)*(vmin/(4*C)) = vmin/2 := by
      field_simp
      ring
    nlinarith [hh]
  have hExp := Real.add_one_le_exp (L^a)
  have hmul := mul_le_mul_of_nonneg_left hExp hv.le
  have hstrict : (vmin/2)*L^a < vmin*Real.exp (L^a) := by
    have ht : (vmin/2)*L^a < vmin*(L^a+1) := by
      nlinarith [mul_nonneg hv.le hp0]
    exact lt_of_lt_of_le ht (by simpa [mul_comm] using hmul)
  exact lt_of_le_of_lt (le_trans hcoeff (le_trans htwoc hbound))
    (by simpa only [mul_comm (Real.exp (L^a)) vmin] using hstrict)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TrueUnmarkedEventual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- For fixed ORIGINAL J,ell the true source03 distinguished S
has eventually MORE distinct primes than the entire physical
shared-SMALL mark capacity of ALL (1+n) moving groups.
This follows from Chebyshev-certified true harmonic mass,
rather than any invented prime cardinality axiom. -/
theorem eventually_source_original_TRUE_source03_shared_SMALL_spare434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
      (z : SourceOriginalSource03CanonicalPrimeSlice434
        n cfg L d vmax c0),
      (n+1)*(J+ell) < z.S.card := by
  filter_upwards [eventually_source_original_exp_rpow_dominates_log_budget434
    cfg.aexp cfg.vmin cfg.C0 cfg.haexp cfg.hv cfg.hC0 (J+ell)]
    with L hL
  intro n d vmax c0 z
  have hn := z.hSmallLog
  have hJ : 0 ≤ ((J+ell:ℕ):ℝ) := Nat.cast_nonneg _
  have hN : (((n+1)*(J+ell):ℕ):ℝ) ≤
      (cfg.C0*Real.log L+1)*((J+ell:ℕ):ℝ) := by
    convert (mul_le_mul_of_nonneg_right (add_le_add_right hn 1) hJ) using 1 <;> push_cast <;> ring
  have hS : Real.exp (L^cfg.aexp)*cfg.vmin ≤ (z.S.card:ℝ) := by
    exact source_original_CANONICAL_true_SMALL_card_lower434 z none
  have hReal : (((n+1)*(J+ell):ℕ):ℝ) < (z.S.card:ℝ) :=
    lt_of_le_of_lt hN (lt_of_lt_of_le (hL) hS)
  exact_mod_cast hReal

/-- UNCONDITIONAL eventual uniform true-prime lower bound
on every physical source03 path-conditioned SMALL modulus:
for each fixed J,ell and all sufficiently large L, EVERY
canonical prime source slice and EVERY actual oriented SMALL
endpoint permutation has Q_unmarked >= exp(L^cfg.aexp).
No preassigned prime subset outside the shared marks is assumed. -/
theorem eventually_source_original_TRUE_source03_PHYSICAL_unmarked_lower434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
      (z : SourceOriginalSource03CanonicalPrimeSlice434
        n cfg L d vmax c0)
      (cap : Fin n → ℕ)
      (x : FullPhysicalState
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) (J+ell) cap)
      (ss : GroupPermFamily (G := Option (Fin n)) (J+ell)),
      Real.exp (L^cfg.aexp) ≤
        (sourceOriginalSource03UNMARKEDModulus434 z
          (sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ss):ℝ) := by
  filter_upwards [eventually_source_original_TRUE_source03_shared_SMALL_spare434
    cfg J ell] with L hL
  intro n d vmax c0 z cap x ss
  exact source_original_TRUE_SOURCE03_PHYSICAL_unmarked_modulus_lower434
    z J ell cap x ss (hL n d vmax c0 z)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalUnmarkedCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Cardinal accounting in the ACTUAL source03 SMALL sector:
at most (n+1)*(J+ell) true S primes can divide the complete
shared-SMALL physical product, even with repeated source marks.
All other S primes remain inside the true conditional modulus. -/
theorem source_original_TRUE_source03_PHYSICAL_unmarked_S_card434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell : ℕ) (cap : Fin n → ℕ)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ss : GroupPermFamily (G := Option (Fin n)) (J+ell)) :
    z.S.card ≤
      (z.S.filter (fun q => ¬q ∣
        sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ss)).card +
      (n+1)*(J+ell) := by
  classical
  let SP := sourceOriginalSource03CanonicalSmallCarrier434 z
  let BP := sourceOriginalSource03CanonicalBigCarrier434 z
  let small := sourceOriginalPhysicalSourceSMALLFactor434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap x ss
  let used := sourceOriginalActualSharedSmallPrimeLabels434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap x ss
  have hselected : (z.S.filter (fun q => q ∣ small)) ⊆ used := by
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    have hqDiv := (Finset.mem_filter.mp hq).2
    have hprime : q.Prime := (z.hSmallBand none q hqS).1
    have htyped : ∀ g (p : SP g), (p.val).Prime :=
      fun g p => (z.hSmallBand g p.val p.property).1
    exact (source_original_ACTUAL_shared_SMALL_prime_dvd_iff_selected434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ss htyped q hprime).mp hqDiv
  have hUsed : used.card ≤ (n+1)*(J+ell) := by
    have hh := source_original_ACTUAL_shared_SMALL_prime_support_card_le434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ss
    simpa [used] using hh
  have hMarked : (z.S.filter (fun q => q ∣ small)).card ≤
      (n+1)*(J+ell) :=
    (Finset.card_le_card hselected).trans hUsed
  have hSplit := z.S.card_filter_add_card_filter_not
    (fun q => q ∣ small)
  change z.S.card ≤ (z.S.filter (fun q => ¬q∣small)).card +
    (n+1)*(J+ell)
  omega

/-- For every fixed J,ell, at least HALF the true reciprocal
S-mass cardinal lower bound survives shared-mark removal,
uniformly over ALL genuine source03 SMALL permutations.
The remaining prime LABEL COUNT is exponentially large
in L^cfg.aexp, not just nonempty. -/
theorem eventually_source_original_TRUE_source03_PHYSICAL_unmarked_half_S434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
      (z : SourceOriginalSource03CanonicalPrimeSlice434
        n cfg L d vmax c0)
      (cap : Fin n → ℕ)
      (x : FullPhysicalState
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) (J+ell) cap)
      (ss : GroupPermFamily (G := Option (Fin n)) (J+ell)),
      Real.exp (L^cfg.aexp)*(cfg.vmin/2) <
        ((z.S.filter (fun q => ¬q ∣
          sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ss)).card:ℝ) := by
  filter_upwards [eventually_source_original_exp_rpow_dominates_log_budget434
    cfg.aexp (cfg.vmin/2) cfg.C0 cfg.haexp (half_pos cfg.hv)
    cfg.hC0 (J+ell)] with L hL
  intro n d vmax c0 z cap x ss
  have hJ : 0 ≤ ((J+ell:ℕ):ℝ) := Nat.cast_nonneg _
  have hN : (((n+1)*(J+ell):ℕ):ℝ) ≤
      (cfg.C0*Real.log L+1)*((J+ell:ℕ):ℝ) := by
    convert (mul_le_mul_of_nonneg_right
      (add_le_add_right z.hSmallLog 1) hJ) using 1 <;> push_cast <;> ring
  have hBudget : (((n+1)*(J+ell):ℕ):ℝ) <
      Real.exp (L^cfg.aexp)*(cfg.vmin/2) :=
    lt_of_le_of_lt hN hL
  have hMass := source_original_CANONICAL_true_SMALL_card_lower434 z none
  have hCard := source_original_TRUE_source03_PHYSICAL_unmarked_S_card434
    z J ell cap x ss
  have hCardReal : (z.S.card:ℝ) ≤
      ((z.S.filter (fun q => ¬q ∣
        sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ss)).card:ℝ) +
      (((n+1)*(J+ell):ℕ):ℝ) := by
    exact_mod_cast hCard
  change Real.exp (L^cfg.aexp)*cfg.vmin ≤ (z.S.card:ℝ) at hMass
  nlinarith [hMass,hBudget,hCardReal]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03UnmarkedProductLower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- TRUE quantitative LOWER bound for the WHOLE path-conditioned
unmarked SMALL modulus, not merely one surviving true prime.
Every retained prime from the original distinguished S contributes
its full magnitude >= exp(L^cfg.aexp), and ALL genuine unmarked
S primes divide the actual conditional modulus. -/
theorem source_original_TRUE_source03_PHYSICAL_unmarked_product_lower434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell : ℕ) (cap : Fin n → ℕ)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ss : GroupPermFamily (G := Option (Fin n)) (J+ell)) :
    let s := sourceOriginalPhysicalSourceSMALLFactor434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell cap x ss
    let U := z.S.filter (fun q => ¬q ∣ s)
    (Real.exp (L^cfg.aexp))^(U.card) ≤
       (sourceOriginalSource03UNMARKEDModulus434 z s:ℝ) := by
  dsimp only
  let s := sourceOriginalPhysicalSourceSMALLFactor434
    (sourceOriginalSource03CanonicalSmallCarrier434 z)
    (fun _ p => p.val)
    (sourceOriginalSource03CanonicalBigCarrier434 z)
    (fun _ p => p.val) J ell cap x ss
  let U := z.S.filter (fun q => ¬q ∣ s)
  let Q := sourceOriginalSource03UNMARKEDModulus434 z s
  have hsubset : U ⊆
      (sourceOriginalSource03AllSmall434 z).filter (fun q => ¬q ∣ s) := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union.mpr (Or.inl hh.1),hh.2⟩
  have hdiv : (U.prod id) ∣ Q := by
    unfold Q sourceOriginalSource03UNMARKEDModulus434
    exact Finset.prod_dvd_prod_of_subset U
      ((sourceOriginalSource03AllSmall434 z).filter (fun q => ¬q ∣ s))
      id hsubset
  have hQpos : 0 < Q :=
    source_original_TRUE_source03_UNMARKED_modulus_pos434 z s
  have hProdLe : U.prod id ≤ Q := Nat.le_of_dvd hQpos hdiv
  have hRealProdLe : ((U.prod id:ℕ):ℝ) ≤ (Q:ℝ) := by
    exact_mod_cast hProdLe
  have hProduct : (Real.exp (L^cfg.aexp))^U.card ≤
      ((U.prod id:ℕ):ℝ) := by
    calc
      _ = ∏ p ∈ U, Real.exp (L^cfg.aexp) := by
        simp only [Finset.prod_const]
      _ ≤ ∏ p ∈ U, (p:ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact (Real.exp_pos _).le
        · intro p hp
          exact (z.hSmallBand none p (Finset.mem_filter.mp hp).1).2.1
      _ = ((U.prod id:ℕ):ℝ) := by
        simp only [Nat.cast_prod]
        rfl
  exact hProduct.trans hRealProdLe
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGUpper -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- All genuinely supported canonical BIG prime-label products
in one physical Tb group lie below the exact original upper
source03 exp(L^d) prime band raised to the NUMBER of labels.
No independent product-atom law or surrogate integer draws. -/
theorem source_original_TRUE_source03_BIG_finite_product_upper434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (g : Fin n) {ι : Type} [DecidableEq ι]
    (A : Finset ι) (f : ι → {p : ℕ // p ∈ z.Tb g}) :
    (((A.prod (fun t => (f t).val)):ℕ):ℝ) ≤
       (Real.exp (L^d))^A.card := by
  rw [Nat.cast_prod]
  calc
    (∏ a ∈ A, ((f a).val:ℝ)) ≤
        ∏ a ∈ A, Real.exp (L^d) := by
      apply Finset.prod_le_prod₀
      · intro a ha
        exact Nat.cast_nonneg _
      · intro a ha
        exact (z.hBigBand g (f a).val (f a).property).2.2
    _ = _ := by simp
/-- Upper bound for TRUE original physical BIG shared + auxiliary
factor. There are at most J+ell permuted BIG shared slots and at
most J auxiliary slots PER genuine Tb group. Does not suppose
distinct primes: duplicate BIG marks are counted with multiplicity. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_upper434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (hL : 0 ≤ L) :
    ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
       z J ell m cap patterns x ch:ℕ):ℝ) ≤
      (Real.exp (L^d))^((2*J+ell)*n) := by
  let U := Real.exp (L^d)
  have hU : (1:ℝ) ≤ U := by
    dsimp [U]
    exact Real.one_le_exp (Real.rpow_nonneg hL _)
  unfold sourceOriginalSource03CanonicalPhysicalBIGFactor434
  rw [Nat.cast_prod]
  calc
    (∏ g : Fin n, (((∏ i ∈ sourceBigShared J ell m
         (patterns ch.1) g, ((x.2 g).1
           (ch.2.2.1.sigmaBig g i)).val) *
       (∏ j : ↥((patterns ch.1).free g),
           (ch.2.1 g j).val):ℕ):ℝ)) ≤
       ∏ _g : Fin n, U ^ (2*J+ell) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact Nat.cast_nonneg _
      · intro g hg
        have hshare := source_original_TRUE_source03_BIG_finite_product_upper434
          z g (sourceBigShared J ell m (patterns ch.1) g)
          (fun i => (x.2 g).1 (ch.2.2.1.sigmaBig g i))
        have hSC : (sourceBigShared J ell m (patterns ch.1) g).card
            ≤ J+ell := by
          simpa using (Finset.card_le_card
            (Finset.subset_univ
              (sourceBigShared J ell m (patterns ch.1) g)))
        have hshare' :
          (((∏ i ∈ sourceBigShared J ell m (patterns ch.1) g,
            ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val):ℕ):ℝ) ≤
          U ^ (J+ell) := by
          exact hshare.trans (pow_le_pow_right₀ hU hSC)
        have hfree := source_original_TRUE_source03_BIG_finite_product_upper434
          z g (Finset.univ : Finset ↥((patterns ch.1).free g))
          (fun j => ch.2.1 g j)
        have hFC : (Finset.univ : Finset ↥((patterns ch.1).free g)).card
            ≤ J := by
          have hh : ((patterns ch.1).free g).card ≤ J := by
            simpa only [Finset.card_univ, Fintype.card_fin] using
              (Finset.card_le_card (Finset.subset_univ ((patterns ch.1).free g)))
          simpa only [Finset.card_univ, Fintype.card_coe] using hh
        have hfree' :
          (((∏ j : ↥((patterns ch.1).free g),
              (ch.2.1 g j).val):ℕ):ℝ) ≤ U ^ J := by
          exact hfree.trans (pow_le_pow_right₀ hU hFC)
        calc
          _ = (((∏ i ∈ sourceBigShared J ell m (patterns ch.1) g,
              ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val):ℕ):ℝ) *
              (((∏ j : ↥((patterns ch.1).free g),
                  (ch.2.1 g j).val):ℕ):ℝ) := by push_cast; rfl
          _ ≤ U ^ (J+ell) * U ^ J := by
            apply mul_le_mul hshare' hfree'
            · exact Nat.cast_nonneg _
            · positivity
          _ = U ^ (2*J+ell) := by
            rw [← pow_add]
            congr 1
            omega
    _ = U ^ ((2*J+ell)*n) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGExactCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Exact arithmetic: small integer residues cannot collide mod Q
except by actual equality. Unlike an unqualified modular
diagonalization, BOTH product upper bounds are explicit. -/
theorem source_original_TRUE_SMALL_modulus_bounded_collision_iff434
    (Q a b : ℕ) (ha : a < Q) (hb : b < Q) :
    ((a : ZMod Q) = (b : ZMod Q)) ↔ a = b := by
  have hQ : 0 < Q := lt_of_le_of_lt (Nat.zero_le a) ha
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using hv
  · rintro rfl
    rfl

/-- Under the explicit TRUE source03 numerical capacity test, an
ACTUAL oriented physical BIG product is strictly smaller than the
path-conditioned SMALL modulus. This uses the FULL BIG endpoint
and auxiliary prime product, and the proven genuine U-prime count.
No unproved analytic estimate is assumed here. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_BIG_lt_UNMARKED434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (hL : 0 ≤ L)
    (hGrowth : (Real.exp (L^d))^((2*J+ell)*n) <
        (Real.exp (L^cfg.aexp)) ^
        ((z.S.filter (fun q => ¬q ∣
          sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ch.2.2.2.1)).card)) :
    sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch <
    sourceOriginalSource03UNMARKEDModulus434 z
      (sourceOriginalPhysicalSourceSMALLFactor434
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell cap x ch.2.2.2.1) := by
  have hB := source_original_TRUE_source03_PHYSICAL_BIG_upper434
    z J ell m cap patterns x ch hL
  have hQ := source_original_TRUE_source03_PHYSICAL_unmarked_product_lower434
    z J ell cap x ch.2.2.2.1
  dsimp only at hQ
  have hlt : ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
          z J ell m cap patterns x ch : ℕ):ℝ) <
     (sourceOriginalSource03UNMARKEDModulus434 z
      (sourceOriginalPhysicalSourceSMALLFactor434
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell cap x ch.2.2.2.1):ℝ) :=
    lt_of_le_of_lt hB (lt_of_lt_of_le hGrowth hQ)
  exact_mod_cast hlt

/-- Under the SAME finite, verifiable numerical TRUE-prime product
budget, congruence of two genuine BIG physical source products in
one shared-SMALL fibre reduces to EQUALITY AS NATURAL INTEGERS.
The collision Gram retains exact integer-product multiplicities,
including duplicates and permutation collisions. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_BIG_collision_integer434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell m : ℕ) (cap : Fin n → ℕ)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (Fin n) J m)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (ch ch' : FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x)
    (hL : 0 ≤ L)
    (hSame : sourceOriginalPhysicalSourceSMALLFactor434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell cap x ch'.2.2.2.1 =
      sourceOriginalPhysicalSourceSMALLFactor434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell cap x ch.2.2.2.1)
    (hGrowth : (Real.exp (L^d))^((2*J+ell)*n) <
        (Real.exp (L^cfg.aexp)) ^
        ((z.S.filter (fun q => ¬q ∣
          sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ch.2.2.2.1)).card)) :
    let Q := sourceOriginalSource03UNMARKEDModulus434 z
      (sourceOriginalPhysicalSourceSMALLFactor434
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell cap x ch.2.2.2.1)
    ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch:ℕ):ZMod Q) =
      ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch':ℕ):ZMod Q) ↔
    sourceOriginalSource03CanonicalPhysicalBIGFactor434
       z J ell m cap patterns x ch =
    sourceOriginalSource03CanonicalPhysicalBIGFactor434
       z J ell m cap patterns x ch' := by
  dsimp only
  have hA := source_original_TRUE_SOURCE03_PHYSICAL_BIG_lt_UNMARKED434
      z J ell m cap patterns x ch hL hGrowth
  have hGrowth' : (Real.exp (L^d))^((2*J+ell)*n) <
        (Real.exp (L^cfg.aexp)) ^
        ((z.S.filter (fun q => ¬q ∣
          sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ch'.2.2.2.1)).card) := by
    simpa only [hSame] using hGrowth
  have hB' := source_original_TRUE_SOURCE03_PHYSICAL_BIG_lt_UNMARKED434
      z J ell m cap patterns x ch' hL hGrowth'
  have hB :
     sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch' <
     sourceOriginalSource03UNMARKEDModulus434 z
      (sourceOriginalPhysicalSourceSMALLFactor434
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell cap x ch.2.2.2.1) := by
    simpa only [hSame] using hB'
  exact source_original_TRUE_SMALL_modulus_bounded_collision_iff434
    _ _ _ hA hB
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03GrowthOverSquare -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Genuine superpolynomial source03 scale: for EVERY fixed a>0
and c>0, L² = o(exp(L^a)). This uses Mathlib's genuine
rpow-vs-exp asymptotic, not a synthetic Mertens or prime estimate. -/
theorem eventually_source_original_exp_rpow_dominates_square434
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, L^2 < c * Real.exp (L^a) := by
  have hv : 0 < c/2 := half_pos hc
  have hEXP : (fun x : ℝ => x ^ (2/a)) =o[atTop]
      (fun x : ℝ => Real.exp x) := by
    simpa only [one_mul] using
      (isLittleO_rpow_exp_pos_mul_atTop (2/a) (b := 1) (by norm_num))
  filter_upwards [(tendsto_rpow_atTop ha).eventually (hEXP.bound hv),
    eventually_ge_atTop (1:ℝ)] with L hbound hL
  have hp : (0:ℝ) ≤ L^a := Real.rpow_nonneg (by linarith) _
  have hp2 : (0:ℝ) ≤ (L^a)^(2/a) := Real.rpow_nonneg hp _
  have hEq : (L^a)^(2/a) = L^2 := by
    have hL0 : 0 ≤ L := by linarith
    calc
      _ = L^(a*(2/a)) := (Real.rpow_mul hL0 a (2/a)).symm
      _ = L^(2:ℝ) := by
        congr 1
        field_simp
      _ = L^2 := Real.rpow_natCast L 2
  have hh : L^2 ≤ (c/2)*Real.exp (L^a) := by
    have hsq : (0:ℝ) ≤ L^2 := sq_nonneg L
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp2,
      abs_of_nonneg (Real.exp_pos _).le, hEq,
      abs_of_nonneg hsq] using hbound
  have hs : (c/2)*Real.exp (L^a) < c*Real.exp (L^a) := by
    have he := Real.exp_pos (L^a)
    nlinarith
  exact lt_of_le_of_lt hh hs
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TrueBIGGrowth -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Quantitative SOURCE growth at the actual two-window scale:
the genuine M*n BIG labels, n<=C0*log L and d<=1, consume
less total logarithmic mass than exp(L^a)*vmin/2.
M is FIXED BEFORE the eventual threshold, unlike growing n. -/
theorem eventually_source_original_TRUE_BIG_budget_under_SMALL_growth434
    (a vmin C0 : ℝ) (ha : 0 < a) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) (M : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d : ℝ),
        (n : ℝ) ≤ C0*Real.log L → d ≤ 1 →
        (((M*n:ℕ):ℝ))*L^d < Real.exp (L^a)*(vmin/2) := by
  let C : ℝ := ((M+1:ℕ):ℝ)*(C0+1)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by exact_mod_cast Nat.succ_pos M)
      (by linarith)
  let c : ℝ := vmin/(2*C)
  have hc : 0 < c := div_pos hv (mul_pos (by norm_num) hC)
  filter_upwards [eventually_source_original_exp_rpow_dominates_square434
    a c ha hc, eventually_ge_atTop (1:ℝ)] with L hg hL
  intro n d hn hd
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L := Real.log_le_self hL0
  have hld : L^d ≤ L := by
    calc
      _ ≤ L^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hL hd
      _ = L := by simp
  have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg _
  have hnL : (n:ℝ) ≤ (C0+1)*L := by
    have hn2 := mul_le_mul_of_nonneg_left hlog hC0
    nlinarith [hn,hn2]
  have hMle : (M:ℝ) ≤ ((M+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ M
  have hcoeff : (((M*n:ℕ):ℝ)) ≤ C*L := by
    calc
      _ = (M:ℝ)*(n:ℝ) := by push_cast; ring
      _ ≤ (M:ℝ)*((C0+1)*L) := mul_le_mul_of_nonneg_left hnL hM0
      _ = ((M:ℝ)*(C0+1))*L := by ring
      _ ≤ (((M+1:ℕ):ℝ)*(C0+1))*L := by
        apply mul_le_mul_of_nonneg_right _ hL0
        exact mul_le_mul_of_nonneg_right hMle (by linarith)
      _ = C*L := rfl
  have hbig : (((M*n:ℕ):ℝ))*L^d ≤ C*L^2 := by
    calc
      _ ≤ (((M*n:ℕ):ℝ))*L :=
        mul_le_mul_of_nonneg_left hld (Nat.cast_nonneg _)
      _ ≤ (C*L)*L := mul_le_mul_of_nonneg_right hcoeff hL0
      _ = C*L^2 := by ring
  have hCgrowth : C*L^2 < (vmin/2)*Real.exp (L^a) := by
    have h := mul_lt_mul_of_pos_left hg hC
    have hcEq : C*c = vmin/2 := by
      dsimp [c]
      field_simp
    calc
      _ < C*(c*Real.exp (L^a)) := h
      _ = (vmin/2)*Real.exp (L^a) := by
        rw [← mul_assoc,hcEq]
  exact lt_of_le_of_lt hbig (by
    simpa only [mul_comm (Real.exp (L^a)) (vmin/2)] using hCgrowth)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TrueEventuallyExactBIG -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- TRUE UNCONDITIONAL comparison of genuine source03 source-window
physical BIG products to the full path-conditioned SMALL modulus.
The former has logarithm O(L^d log L); the latter contains at least
~exp(L^a) authentic unmarked prime labels each >=exp(L^a).
All n,d,canonical slices and physical SMALL states are uniform
after a FIXED J,ell threshold. -/
theorem eventually_source_original_TRUE_SOURCE03_BIG_numerical_capacity434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
      (z : SourceOriginalSource03CanonicalPrimeSlice434
        n cfg L d vmax c0) (hd : d < (1/2:ℝ))
      (cap : Fin n → ℕ)
      (x : FullPhysicalState
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) (J+ell) cap)
      (ss : GroupPermFamily (G := Option (Fin n)) (J+ell)),
      (Real.exp (L^d))^((2*J+ell)*n) <
      (Real.exp (L^cfg.aexp))^
        ((z.S.filter (fun q => ¬q ∣
          sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ss)).card) := by
  let M := 2*J+ell
  filter_upwards
    [eventually_source_original_TRUE_BIG_budget_under_SMALL_growth434
      cfg.aexp cfg.vmin cfg.C0 cfg.haexp cfg.hv cfg.hC0 M,
    eventually_source_original_TRUE_source03_PHYSICAL_unmarked_half_S434 cfg J ell,
    eventually_ge_atTop (1:ℝ)] with L hBudget hCount hL
  intro n d vmax c0 z hd cap x ss
  let s := sourceOriginalPhysicalSourceSMALLFactor434
    (sourceOriginalSource03CanonicalSmallCarrier434 z)
    (fun _ p => p.val)
    (sourceOriginalSource03CanonicalBigCarrier434 z)
    (fun _ p => p.val) J ell cap x ss
  let U := z.S.filter (fun q => ¬q ∣ s)
  have hU : Real.exp (L^cfg.aexp)*(cfg.vmin/2) < (U.card:ℝ) := by
    exact hCount n d vmax c0 z cap x ss
  have hb : (((M*n:ℕ):ℝ))*L^d <
      Real.exp (L^cfg.aexp)*(cfg.vmin/2) :=
    hBudget n d z.hSmallLog (by linarith)
  have hpowA : 1 ≤ L^cfg.aexp := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL cfg.haexp.le
    simpa only [Real.rpow_zero] using hh
  have hUle : (U.card:ℝ) ≤ (U.card:ℝ)*L^cfg.aexp := by
    calc
      _ = (U.card:ℝ)*1 := by ring
      _ ≤ (U.card:ℝ)*L^cfg.aexp :=
        mul_le_mul_of_nonneg_left hpowA (Nat.cast_nonneg _)
  have hPowBudget : (((M*n:ℕ):ℝ))*L^d <
      (U.card:ℝ)*L^cfg.aexp :=
    (hb.trans hU).trans_le hUle
  change (Real.exp (L^d))^(M*n) <
    (Real.exp (L^cfg.aexp))^U.card
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  exact Real.exp_lt_exp.mpr hPowBudget

/-- UNCONDITIONAL eventual numerical separation for the
ACTUAL oriented source03 physical BIG product (shared and auxiliary)
from the genuine path-conditioned SMALL modulus. No artificial
hGrowth premise survives. Fixed J,ell,m precede the threshold. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_BIG_lt_UNMARKED434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
      (z : SourceOriginalSource03CanonicalPrimeSlice434
        n cfg L d vmax c0) (hd : d < (1/2:ℝ))
      (cap : Fin n → ℕ)
      {Nu : Type} [Fintype Nu]
      (patterns : Nu → SourcePattern (Fin n) J m)
      (x : FullPhysicalState
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) (J+ell) cap)
      (ch : FullOrientedSourceChoice
        (sourceOriginalSource03CanonicalSmallCarrier434 z)
        (fun _ p => p.val)
        (sourceOriginalSource03CanonicalBigCarrier434 z)
        (fun _ p => p.val) J ell m cap patterns x),
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch <
      sourceOriginalSource03UNMARKEDModulus434 z
        (sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ch.2.2.2.1) := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_BIG_numerical_capacity434 cfg J ell,
      eventually_ge_atTop (1:ℝ)] with L hgrowth hL
  intro n d vmax c0 z hd cap Nu _ patterns x ch
  exact source_original_TRUE_SOURCE03_PHYSICAL_BIG_lt_UNMARKED434
    z J ell m cap patterns x ch (by linarith : 0 ≤ L)
    (hgrowth n d vmax c0 z hd cap x ch.2.2.2.1)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TruePhysicalIntegerBIGCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Unconditional EVENTUAL conversion of a true physical
BIG-product congruence into EQUALITY OF NATURAL INTEGERS.
The only pair hypothesis is shared SMALL state equality, which
is exactly the conditioning used in the true physical character
Gram. The collision multiplicities are NOT assumed trivial. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_BIG_collision_iff_integer434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0) (hd : d < (1/2:ℝ))
        (cap : Fin n → ℕ)
        {Nu : Type} [Fintype Nu]
        (patterns : Nu → SourcePattern (Fin n) J m)
        (x : FullPhysicalState
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) (J+ell) cap)
        (ch ch' : FullOrientedSourceChoice
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell m cap patterns x)
        (hSame : sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ch'.2.2.2.1 =
          sourceOriginalPhysicalSourceSMALLFactor434
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) J ell cap x ch.2.2.2.1),
        let Q := sourceOriginalSource03UNMARKEDModulus434 z
          (sourceOriginalPhysicalSourceSMALLFactor434
            (sourceOriginalSource03CanonicalSmallCarrier434 z)
            (fun _ p => p.val)
            (sourceOriginalSource03CanonicalBigCarrier434 z)
            (fun _ p => p.val) J ell cap x ch.2.2.2.1)
        ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
          z J ell m cap patterns x ch : ℕ) : ZMod Q) =
        ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
          z J ell m cap patterns x ch' : ℕ) : ZMod Q) ↔
        sourceOriginalSource03CanonicalPhysicalBIGFactor434
          z J ell m cap patterns x ch =
        sourceOriginalSource03CanonicalPhysicalBIGFactor434
          z J ell m cap patterns x ch' := by
  filter_upwards [
    eventually_source_original_TRUE_SOURCE03_BIG_numerical_capacity434 cfg J ell,
    eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro n d vmax c0 z hd cap Nu _ patterns x ch ch' hSame
  exact source_original_TRUE_SOURCE03_PHYSICAL_BIG_collision_integer434
    z J ell m cap patterns x ch ch' (by linarith) hSame
    (hbudget n d vmax c0 z hd cap x ch.2.2.2.1)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TruePhysicalIntegerBIGGram -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The complete actual source03 PHYSICAL E character Gram,
on every legal fixed shared-SMALL fibre, reduces EVENTUALLY to
the EXACT INTEGER equality of two physical shared+aux BIG
products. The weights contain the genuine joint complex source
Knu, permutation masses, Fock/OLD transitions and future test.
All exact-integer off-diagonal collisions remain; no saving yet. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_INTEGER_BIG_Gram434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0) (hd : d < (1/2:ℝ))
        (cap : Fin n → ℕ)
        {Nu : Type} [Fintype Nu]
        (patterns : Nu → SourcePattern (Fin n) J m)
        (x : FullPhysicalState
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) (J+ell) cap)
        (q rho : ℝ) (Vs : Option (Fin n) → ℝ)
        (Vb : Fin n → ℝ)
        (mu : (g : Fin n) →
          sourceOriginalSource03CanonicalBigCarrier434 z g → ℝ)
        (Knu : SourcePatternK
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          J ell m patterns)
        (zeta theta : ℝ)
        (o k : ℤ) (ho : o = 1 ∨ o = -1)
        (hk : 0 < k.natAbs)
        (hK : (k.natAbs:ℝ) ≤ L^cfg.Carc)
        (hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp))
        (future : FullPhysicalOutput
          (sourceOriginalSource03CanonicalSmallCarrier434 z)
          (fun _ p => p.val)
          (sourceOriginalSource03CanonicalBigCarrier434 z)
          (fun _ p => p.val) (J+ell) → ℂ)
        (s : ℕ),
        let SP := sourceOriginalSource03CanonicalSmallCarrier434 z
        let BP := sourceOriginalSource03CanonicalBigCarrier434 z
        let Q := sourceOriginalSource03UNMARKEDModulus434 z s
        let F := sourceOriginalPhysicalSameSharedChoices434
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x o k s
        let v : FullOrientedSourceChoice
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x → ZMod Q := fun ch =>
          (sourceOrientedStep SP (fun _ p => p.val)
            BP (fun _ p => p.val) J ell m cap
            (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
            ch.2.2.2.1 o k : ZMod Q)
        let B : FullOrientedSourceChoice
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x → ℕ := fun ch =>
          sourceOriginalSource03CanonicalPhysicalBIGFactor434
            z J ell m cap patterns x ch
        let w : FullOrientedSourceChoice
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x → ℂ := fun ch =>
          sourceOriginalPhysicalFutureWeight434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell m cap patterns q rho Vs Vb mu Knu
            zeta theta o k x future ch
        (∑ χ : DirichletCharacter ℂ Q,
          ∑ ch ∈ F, ∑ ch' ∈ F,
            (star (w ch)*w ch') *
              (χ ((v ch)⁻¹)*χ (v ch'))) =
        (Q.totient : ℂ) *
          (∑ ch ∈ F, ∑ ch' ∈ F,
            if B ch = B ch' then star (w ch)*w ch' else 0) := by
  filter_upwards [
    eventually_source_original_TRUE_SOURCE03_BIG_numerical_capacity434 cfg J ell,
    eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro n d vmax c0 z hd cap Nu _ patterns x q rho Vs Vb mu Knu
    zeta theta o k ho hk hK hOrigSmall future s
  let SP := sourceOriginalSource03CanonicalSmallCarrier434 z
  let BP := sourceOriginalSource03CanonicalBigCarrier434 z
  have hbig : ∀ (g : Fin n) (p : BP g),
        ∃ i : Fin n, (p.val : ℕ) ∈ z.Tb i :=
    fun g p => ⟨g,p.property⟩
  have hGram := source_original_TRUE_SOURCE03_PHYSICAL_future_BIG_collision_Gram434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns z hbig x q rho Vs Vb mu Knu
    zeta theta o k ho hk hK hOrigSmall future s
  dsimp only at hGram ⊢
  rw [hGram]
  congr 1
  apply Finset.sum_congr rfl
  intro ch hch
  apply Finset.sum_congr rfl
  intro ch' hch'
  have hs : sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ch.2.2.2.1 = s :=
    (Finset.mem_filter.mp hch).2
  have hs' : sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ch'.2.2.2.1 = s :=
    (Finset.mem_filter.mp hch').2
  have hSame : sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ch'.2.2.2.1 =
      sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ch.2.2.2.1 := hs'.trans hs.symm
  have hiff := source_original_TRUE_SOURCE03_PHYSICAL_BIG_collision_integer434
    z J ell m cap patterns x ch ch' (by linarith) hSame
    (hbudget n d vmax c0 z hd cap x ch.2.2.2.1)
  dsimp only at hiff
  have hB : ∀ t : FullOrientedSourceChoice
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x,
      sourceOriginalPhysicalSourceBIGFactor434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m cap (patterns t.1) t.2.1 x t.2.2.1.sigmaBig =
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x t := by
    intro t
    rfl
  by_cases he : sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch =
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch'
  · have hv := hiff.mpr he
    rw [hs] at hv
    simp only [hB, hv, he, if_pos]
    rfl
  · have hv : ¬ ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch : ℕ) : ZMod
        (sourceOriginalSource03UNMARKEDModulus434 z
          (sourceOriginalPhysicalSourceSMALLFactor434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell cap x ch.2.2.2.1))) =
      ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch' : ℕ) : ZMod
        (sourceOriginalSource03UNMARKEDModulus434 z
          (sourceOriginalPhysicalSourceSMALLFactor434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell cap x ch.2.2.2.1))) := by
      exact fun h => he (hiff.mp h)
    rw [hs] at hv
    simp only [hB, hv, he, if_neg, ite_false]
end Green64Analytic.CorrelationSquare

end

end

