module

public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part020
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Prod
public import Green64.Library.Sieve.Foundations.Part004
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part015

@[expose] public section

/-!
# Correlation / Part034

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGroupProductDetermined -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- In the TRUE SOURCE03 labelled prime model, disjoint group
prime supports make the product of a SELECTED set of prime
slots uniquely determined by the complete integer product.
Both prime tuples may have arbitrary numerical repetitions,
and each labelled slot may have a different true prime support.
The only required arithmetic conditions are:
  * every selected slot has a prime in the group support S;
  * every unselected slot has a prime OUTSIDE S.
Thus the statement does not assume a false bijection with
unordered squarefree products, and it is a key group-factor
uniqueness lemma for the original C6 atom law. -/
theorem source_original_selected_group_product_determined434
    {I : Type} [Fintype I] [DecidableEq I]
    (a b : I → ℕ)
    (ha : ∀ i, (a i).Prime)
    (hb : ∀ i, (b i).Prime)
    (T : Finset I) (S : Finset ℕ)
    (hinA : ∀ i, i ∈ T → a i ∈ S)
    (hinB : ∀ i, i ∈ T → b i ∈ S)
    (houtA : ∀ i, i ∉ T → a i ∉ S)
    (houtB : ∀ i, i ∉ T → b i ∉ S)
    (hTotal : (∏ i : I, a i) = ∏ i : I, b i) :
    (∏ i ∈ T, a i) = ∏ i ∈ T, b i := by
  have hPosA : 0 < ∏ i ∈ T, a i := by
    apply Finset.prod_pos
    intro i hi
    exact (ha i).pos
  have hPosB : 0 < ∏ i ∈ T, b i := by
    apply Finset.prod_pos
    intro i hi
    exact (hb i).pos
  apply Nat.eq_of_factorization_eq' hPosA.ne' hPosB.ne'
  ext p
  by_cases hp : p ∈ S
  · rw [source_original_prime_selected_factorization_eq434
       a ha T S houtA p hp,
       source_original_prime_selected_factorization_eq434
       b hb T S houtB p hp,
       hTotal]
  · rw [source_original_prime_selected_factorization_outside434
       a ha T S hinA p hp,
       source_original_prime_selected_factorization_outside434
       b hb T S hinB p hp]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDisjointGroupPrimeProduct -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Disjoint ORIGINAL GROUP prime supports guarantee the
genuine coordinate-by-coordinate full product determines
every group's selected integer prime product, including
repeated numerical primes INSIDE the same group.
The original group map on labelled physical slots is kept,
with no artificial group-uniform prime model. This is the
arithmetic uniqueness step needed to count true SOURCE03
prime-tuple integer-product fibres by independent groups. -/
theorem source_original_disjoint_group_product_determined434
    {I γ : Type} [Fintype I] [DecidableEq I] [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (grp : I → γ)
    (hGrp : ∀ i, grp i ∈ G)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h → Disjoint (S g) (S h))
    (a b : I → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S (grp i))
    (hb : ∀ i, (b i).Prime ∧ b i ∈ S (grp i))
    (g : γ) (hg : g ∈ G)
    (hProd : (∏ i : I, a i) = (∏ i : I, b i)) :
    (∏ i ∈ (Finset.univ.filter (fun i : I => grp i = g)), a i) =
    (∏ i ∈ (Finset.univ.filter (fun i : I => grp i = g)), b i) := by
  classical
  let T : Finset I := Finset.univ.filter (fun i => grp i = g)
  have hT (i : I) : i ∈ T ↔ grp i = g := by
    simp [T]
  have hinA (i : I) (hi : i ∈ T) : a i ∈ S g := by
    rw [←(hT i).mp hi]
    exact (ha i).2
  have hinB (i : I) (hi : i ∈ T) : b i ∈ S g := by
    rw [←(hT i).mp hi]
    exact (hb i).2
  have houtA (i : I) (hi : i ∉ T) : a i ∉ S g := by
    have hne : grp i ≠ g := by
      intro hEq
      exact hi ((hT i).mpr hEq)
    have hD : Disjoint (S (grp i)) (S g) :=
      hDisjoint (grp i) (hGrp i) g hg hne
    exact (Finset.disjoint_left.mp hD) (ha i).2
  have houtB (i : I) (hi : i ∉ T) : b i ∉ S g := by
    have hne : grp i ≠ g := by
      intro hEq
      exact hi ((hT i).mpr hEq)
    have hD : Disjoint (S (grp i)) (S g) :=
      hDisjoint (grp i) (hGrp i) g hg hne
    exact (Finset.disjoint_left.mp hD) (hb i).2
  exact source_original_selected_group_product_determined434
    a b (fun i => (ha i).1) (fun i => (hb i).1)
    T (S g) hinA hinB houtA houtB hProd
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualGroupPrimeSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- True indexed physical prime products have no prime factors
outside the union of their ACTUAL group support sets.
Every labelled slot retains its original group map, different
groups need NOT have disjoint supports for this basic lemma.
It is the exact prime-support clause of the C6 atom validity,
rather than an artificial promise about all integers. -/
theorem source_original_actual_group_prime_product_support434
    {I γ : Type} [Fintype I] [DecidableEq I] [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (grp : I → γ) (hGrp : ∀ i, grp i ∈ G)
    (a : I → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S (grp i))
    (p : ℕ) (hp : p ∈ (∏ i : I, a i).primeFactors) :
    p ∈ G.biUnion S := by
  classical
  by_contra hn
  have hOutside (i : I) : a i ∈ G.biUnion S := by
    exact Finset.mem_biUnion.mpr
      ⟨grp i,hGrp i,(ha i).2⟩
  have hFactorZero :=
    source_original_prime_tuple_factorization_outside434
      (G.biUnion S) a
      (fun i => ⟨(ha i).1,hOutside i⟩) p hn
  have hNonzero : (∏ i : I, a i).factorization p ≠ 0 := by
    have hp' : p ∈ (∏ i : I, a i).factorization.support := by
      simpa only [Nat.support_factorization] using hp
    exact (Finsupp.mem_support_iff).mp hp'
  exact hNonzero hFactorZero
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualGroupPrimeMultiplicity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- In the original physical indexed prime tuple, the
sum of all multiplicities of prime factors from one TRUE
group support S_g is EXACTLY the number of indexed slots
assigned to that group. This includes repeated primes.
The only arithmetic separation input is pairwise disjoint
prime supports for different original BIG groups.
It verifies the multiplicity COUNT clause of the literal
C6 sourceAtomValid; no synthetic count law is assumed. -/
theorem source_original_actual_group_factorization_sum434
    {I γ : Type} [Fintype I] [DecidableEq I] [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (grp : I → γ) (hGrp : ∀ i, grp i ∈ G)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h → Disjoint (S g) (S h))
    (a : I → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S (grp i))
    (g : γ) (hg : g ∈ G) :
    (∑ p ∈ S g, (∏ i : I, a i).factorization p) =
      ((Finset.univ : Finset I).filter
        (fun i => grp i = g)).card := by
  classical
  have hSelect (i : I) :
      a i ∈ S g ↔ grp i = g := by
    constructor
    · intro hmem
      by_contra hne
      have hD : Disjoint (S (grp i)) (S g) :=
        hDisjoint (grp i) (hGrp i) g hg hne
      exact (Finset.disjoint_left.mp hD) (ha i).2 hmem
    · intro eq
      simpa only [eq] using (ha i).2
  have hInner (i : I) :
      (∑ p ∈ S g, if a i = p then (1:ℕ) else 0) =
        (if grp i = g then 1 else 0) := by
    by_cases hs : a i ∈ S g
    · have hg' : grp i = g := (hSelect i).mp hs
      simp [hs,hg',Finset.sum_ite_eq']
    · have hg' : grp i ≠ g := fun hh => hs ((hSelect i).mpr hh)
      simp [hs,hg',Finset.sum_ite_eq']
  calc
    _ = ∑ p ∈ S g, ∑ i : I,
          (if a i = p then (1:ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact source_original_prime_tuple_factorization_count434
        a (fun i => (ha i).1) p
    _ = ∑ i : I, ∑ p ∈ S g,
          (if a i = p then (1:ℕ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ i : I, (if grp i = g then (1:ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hInner i
    _ = ((Finset.univ : Finset I).filter
           (fun i => grp i = g)).card := by
      rw [Finset.sum_ite]
      simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalAtomPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- EXACT arithmetic SOURCE03 two-GLOBAL product-atom
reindexing of the physical bilinear exponential kernel,
with actual independently labelled A/B prime supports and
true harmonic weights. The original source and target tests
may each depend arbitrarily on ALL their own prime labels:
fA(a) and fB(b) need not factor through the integer product.
This is an exact finite pushforward, not a cancellation
claim. The resulting integer amplitudes are the actual
conditional product-atom coefficients of C211/C213.
This is a necessary bridge to the existing source03
q>Q product-atom minor-arc exponential bound. -/
theorem source_original_physical_two_global_atom_pushforward434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (F : ℕ → ℂ) :
    (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
              SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
       (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
         fA ab.1 * fB ab.2 *
         F (sourceOriginalGramPrimeProduct434 SA ab.1 *
            sourceOriginalGramPrimeProduct434 SB ab.2)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 SA,
      ∑ m ∈ sourceOriginalPhysicalProductAtomSupport434 SB,
        sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA n *
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB m *
        F (n*m) := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let prodA : XA → ℕ := sourceOriginalGramPrimeProduct434 SA
  let prodB : XB → ℕ := sourceOriginalGramPrimeProduct434 SB
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let TA : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 SB
  let aCoeff := sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA
  let bCoeff := sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB
  have hCollapseA (m : ℕ) :
      (∑ a : XA, (wA a:ℂ)*fA a*F (prodA a*m)) =
      ∑ n ∈ TA, aCoeff n*F (n*m) := by
    exact source_original_physical_product_atom_test_pushforward434
      SA muA fA (fun n => F (n*m))
  have hCollapseB (a : XA) :
      (∑ b : XB, (wB b:ℂ)*fB b*F (prodA a*prodB b)) =
      ∑ m ∈ TB, bCoeff m*F (prodA a*m) := by
    exact source_original_physical_product_atom_test_pushforward434
      SB muB fB (fun m => F (prodA a*m))
  change (∑ ab : XA × XB,
    ((wA ab.1:ℂ)*(wB ab.2:ℂ))*fA ab.1*fB ab.2*
      F (prodA ab.1*prodB ab.2)) =
    ∑ n ∈ TA, ∑ m ∈ TB, aCoeff n*bCoeff m*F (n*m)
  calc
    _ = ∑ a : XA, ∑ b : XB,
          ((wA a:ℂ)*fA a)*((wB b:ℂ)*fB b*
              F (prodA a*prodB b)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
    _ = ∑ a : XA, ((wA a:ℂ)*fA a)*
          (∑ b : XB, (wB b:ℂ)*fB b*
              F (prodA a*prodB b)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
    _ = ∑ a : XA, ((wA a:ℂ)*fA a)*
          (∑ m ∈ TB, bCoeff m*F (prodA a*m)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hCollapseB a]
    _ = ∑ m ∈ TB, bCoeff m*
          (∑ a : XA, (wA a:ℂ)*fA a*
              F (prodA a*m)) := by
        calc
          _ = ∑ a : XA, ∑ m ∈ TB,
                bCoeff m*((wA a:ℂ)*fA a*
                  F (prodA a*m)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = ∑ m ∈ TB, ∑ a : XA,
                bCoeff m*((wA a:ℂ)*fA a*
                  F (prodA a*m)) := by
            rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
    _ = ∑ m ∈ TB, bCoeff m*
          (∑ n ∈ TA, aCoeff n*F (n*m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hCollapseA m]
    _ = ∑ n ∈ TA, ∑ m ∈ TB,
          aCoeff n*bCoeff m*F (n*m) := by
        calc
          _ = ∑ m ∈ TB, ∑ n ∈ TA,
                aCoeff n*bCoeff m*F (n*m) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = _ := by
            rw [Finset.sum_comm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoWindowMinorFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The exact source03 double original physical-prime-tuple
bilinear sum on arbitrary finite integer dyad windows is the
DOUBLE integer-product atom sum used by the true C6 estimate.
Both endpoint observables f_A,f_B may depend on their ENTIRE
factorization/mark tuple, rather than on the integer products.
No artificial independent integer law and no injectivity of
the prime product map. The original source and target physical
measures are kept exactly, including repeated numerical primes.
This exact identity is the algebraic prerequisite to identify
the C271 grouped C6 minor term with a true physical bilinear
source03 expression; identifying its grouped indices with
the original ν-signed RAW operator is still a separate task. -/
theorem source_original_physical_two_window_minor_exact_fubini434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (A B : Finset ℕ) (K : ℕ → ℕ → ℂ) :
    (∑ a : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA a ∈ A then
        (sourceOriginalGramPrimeMass434 SA muA a:ℂ)*fA a*
        (∑ b : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB b ∈ B then
            (sourceOriginalGramPrimeMass434 SB muB b:ℂ)*fB b*
              K (sourceOriginalGramPrimeProduct434 SA a)
                (sourceOriginalGramPrimeProduct434 SB b)
          else 0)
      else 0) =
    ∑ n ∈ A, sourceOriginalPhysicalProductAtomCoefficient434
      SA muA fA n*
      (∑ m ∈ B, sourceOriginalPhysicalProductAtomCoefficient434
        SB muB fB m*K n m) := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let pa : XA → ℕ := sourceOriginalGramPrimeProduct434 SA
  let pb : XB → ℕ := sourceOriginalGramPrimeProduct434 SB
  let wa : XA → ℂ := fun a =>
    (sourceOriginalGramPrimeMass434 SA muA a:ℂ)*fA a
  let wb : XB → ℂ := fun b =>
    (sourceOriginalGramPrimeMass434 SB muB b:ℂ)*fB b
  have hInner (n : ℕ) :
      (∑ b : XB, if pb b ∈ B then wb b*K n (pb b) else 0) =
      ∑ m ∈ B, sourceOriginalPhysicalProductAtomCoefficient434
        SB muB fB m*K n m := by
    exact (source_original_physical_atom_finite_window_pullback434
      SB muB fB B (K n)).symm
  have hOuter :=
    source_original_physical_atom_finite_window_pullback434
      SA muA fA A
      (fun n => ∑ m ∈ B,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB m*K n m)
  calc
    _ = ∑ a : XA,
      if pa a ∈ A then wa a*
        (∑ m ∈ B, sourceOriginalPhysicalProductAtomCoefficient434
          SB muB fB m*K (pa a) m)
      else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hpa : pa a ∈ A
        · simp only [show sourceOriginalGramPrimeProduct434 SA a ∈ A from hpa,
            if_pos, wa, pb, wb]
          rw [hInner (pa a)]
          simp [hpa]
        · simp [pa,hpa]
    _ = _ := hOuter.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalShiftedWindowFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact ORIGINAL source03 physical two-BIG-block sum on
dyadic NATURAL windows M+[0,P) and N+[0,Q) as the literal
shifted integer atom bilinear sum used by source03 C6.
This is valid for arbitrary complex prime-mark-dependent
endpoint tests and any integer-product phase K.
No product-map injectivity, group distribution proxy,
or equality between SMALL and BIG group factors.
It is a genuine algebraic identity on the exact windows,
with the original finite harmonic prime tuple masses. -/
theorem source_original_physical_two_shifted_window_fubini434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N P Q : ℕ) (K : ℕ → ℕ → ℂ) :
    let AW : Finset ℕ :=
      (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ :=
      (Finset.range Q).image (fun j => N+j)
    (∑ a : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA a ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA a:ℂ)*fA a*
        (∑ b : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB b ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB b:ℂ)*fB b*
              K (sourceOriginalGramPrimeProduct434 SA a)
                (sourceOriginalGramPrimeProduct434 SB b)
          else 0)
      else 0) =
    ∑ i ∈ Finset.range P,
      sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
      (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          K (M+i) (N+j)) := by
  classical
  let AW : Finset ℕ :=
    (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ :=
    (Finset.range Q).image (fun j => N+j)
  have hInjA : Set.InjOn (fun i : ℕ => M+i) (Finset.range P) :=
    fun i _ j _ h => Nat.add_left_cancel h
  have hInjB : Set.InjOn (fun j : ℕ => N+j) (Finset.range Q) :=
    fun i _ j _ h => Nat.add_left_cancel h
  have hShiftA (F : ℕ → ℂ) :
      (∑ n ∈ AW, F n) = ∑ i ∈ Finset.range P, F (M+i) := by
    exact Finset.sum_image hInjA
  have hShiftB (F : ℕ → ℂ) :
      (∑ n ∈ BW, F n) = ∑ j ∈ Finset.range Q, F (N+j) := by
    exact Finset.sum_image hInjB
  have hFub := source_original_physical_two_window_minor_exact_fubini434
    SA muA SB muB fA fB AW BW K
  let atomA := sourceOriginalPhysicalProductAtomCoefficient434
    SA muA fA
  let atomB := sourceOriginalPhysicalProductAtomCoefficient434
    SB muB fB
  change _ = ∑ i ∈ Finset.range P,
      atomA (M+i)*(∑ j ∈ Finset.range Q,
        atomB (N+j)*K (M+i) (N+j))
  calc
    _ = ∑ n ∈ AW, atomA n*
      (∑ m ∈ BW, atomB m*K n m) := hFub
    _ = ∑ i ∈ Finset.range P, atomA (M+i)*
      (∑ m ∈ BW, atomB m*K (M+i) m) :=
      hShiftA (fun n => atomA n*(∑ m ∈ BW, atomB m*K n m))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hShiftB (fun m => atomB m*K (M+i) m)]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveCellGramSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Split the ACTUAL original finite prime-supported index tuple at
one distinguished BIG mark, retaining all other index-dependent
prime supports without replacing them by a common prime space. -/
noncomputable def sourceOriginalGramPrimeSplit434
    {ι : Type} [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι) :
    SourceOriginalGramPrimeTuple434 S ≃
      ({p : ℕ // p ∈ S i} ×
       ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})) :=
  Equiv.piSplitAt i (fun k => {p : ℕ // p ∈ S k})

/-- Genuine product of ALL marked prime numbers decomposes
at the chosen source coordinate into p times original R. -/
theorem source_original_gram_prime_product_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι)
    (a : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalGramPrimeProduct434 S a =
    (a i).val *
      (∏ k : {k : ι // k ≠ i}, (a k.val).val) := by
  unfold sourceOriginalGramPrimeProduct434
  calc
    _ = (a i).val *
        ∏ k ∈ (Finset.univ : Finset ι).erase i, (a k).val :=
      (Finset.mul_prod_erase (Finset.univ : Finset ι)
        (fun k => (a k).val) (Finset.mem_univ i)).symm
    _ = _ := by
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase i)
        (by intro k; simp) (fun k => (a k).val)

/-- The ORIGINAL product of REAL reciprocal-prime weights
has the same exact split at one chosen source prime label. -/
theorem source_original_gram_prime_mass_split434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (i : ι) (a : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalGramPrimeMass434 S mu a =
    mu i (a i).val *
      (∏ k : {k : ι // k ≠ i},
           mu k.val (a k.val).val) := by
  unfold sourceOriginalGramPrimeMass434
  calc
    _ = mu i (a i).val *
      ∏ k ∈ (Finset.univ : Finset ι).erase i,
        mu k (a k).val :=
      (Finset.mul_prod_erase (Finset.univ : Finset ι)
        (fun k => mu k (a k).val) (Finset.mem_univ i)).symm
    _ = _ := by
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase i)
        (by intro k; simp) (fun k => mu k (a k).val)

/-- Exact Fubini identity on literal original product of
potentially DIFFERENT finite BIG prime sets; test F arbitrary. -/
theorem source_original_gram_one_prime_fubini434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι)
    (F : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ a : SourceOriginalGramPrimeTuple434 S, F a) =
    ∑ r : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
      ∑ p : {p : ℕ // p ∈ S i},
        F ((sourceOriginalGramPrimeSplit434 S i).symm (p,r)) := by
  let e := sourceOriginalGramPrimeSplit434 S i
  calc
    _ = ∑ t : ({p : ℕ // p ∈ S i} ×
         ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})),
        F (e.symm t) := by
      exact Fintype.sum_equiv e F (fun t => F (e.symm t))
        (by intro a; simp)
    _ = ∑ p : {p : ℕ // p ∈ S i},
         ∑ r : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
           F (e.symm (p,r)) := by rw [Fintype.sum_prod_type]
    _ = _ := by rw [Finset.sum_comm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramPhysicalSlice -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- REAL original source BIG product of all OTHER prime labels. -/
noncomputable def sourceOriginalGramOtherPrimeProduct434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι)
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) : ℕ :=
  ∏ k : {k : ι // k ≠ i}, (r k).val

/-- REAL original harmonic mass of the OTHER labelled primes. -/
noncomputable def sourceOriginalGramOtherPrimeMass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (i : ι)
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) : ℝ :=
  ∏ k : {k : ι // k ≠ i}, mu k.val (r k).val

/-- ACTUAL source03 product of the real original marked BIG
prime labels, exactly one new selected prime p times R. -/
theorem source_original_gram_physical_prime_slice434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι)
    (p : {p : ℕ // p ∈ S i})
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) :
    sourceOriginalGramPrimeProduct434 S
      ((sourceOriginalGramPrimeSplit434 S i).symm (p,r)) =
    p.val * sourceOriginalGramOtherPrimeProduct434 S i r := by
  let e := sourceOriginalGramPrimeSplit434 S i
  have he := e.apply_symm_apply (p,r)
  have hfirst : (e.symm (p,r)) i = p := congrArg Prod.fst he
  have hrest : (fun k : {k : ι // k ≠ i} =>
      (e.symm (p,r)) k.val) = r := congrArg Prod.snd he
  rw [source_original_gram_prime_product_split434]
  unfold sourceOriginalGramOtherPrimeProduct434
  rw [hfirst]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg Subtype.val (congrFun hrest k)

/-- ACTUAL source03 reciprocal-prime probability for p and all
other source marks, with true coordinate-dependent supports. -/
theorem source_original_gram_physical_mass_slice434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (i : ι) (p : {p : ℕ // p ∈ S i})
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) :
    sourceOriginalGramPrimeMass434 S mu
      ((sourceOriginalGramPrimeSplit434 S i).symm (p,r)) =
    mu i p.val * sourceOriginalGramOtherPrimeMass434 S mu i r := by
  let e := sourceOriginalGramPrimeSplit434 S i
  have he := e.apply_symm_apply (p,r)
  have hfirst : (e.symm (p,r)) i = p := congrArg Prod.fst he
  have hrest : (fun k : {k : ι // k ≠ i} =>
      (e.symm (p,r)) k.val) = r := congrArg Prod.snd he
  rw [source_original_gram_prime_mass_split434]
  unfold sourceOriginalGramOtherPrimeMass434
  rw [hfirst]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [congrFun hrest k]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveCellGramReduction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The literal source03 global log-cell one-prime slice of
the Gram pairing of two characters, after all OTHER true BIG
prime labels have been fixed. This is the actual weighted
prime-character sum; no mean zero or SW is inserted. -/
noncomputable def sourceOriginalGramLocalPrimeSlice434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (χ ψ : ℕ → ℂ)
    (i : ι)
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) : ℂ :=
  ∑ p : {p : ℕ // p ∈ S i},
    (mu i p.val : ℂ) *
      (if sourceOriginalLiteralLogCell434 h j
        (p.val * sourceOriginalGramOtherPrimeProduct434 S i r)
       then star (χ p.val) * ψ p.val else 0)

/-- EXACT arithmetic identity for the GENUINE source03
GLOBAL product log cell and TWO characters of potentially
different primitive conductors: its offdiagonal Gram entry
is a weighted average of true one-prime sums on the MOVING
interval determined by all other marked BIG prime labels.
All nontrivial cell/character correlation resides in the
one-prime slice; the rest character factor has norm ≤1
when instantiated as genuine Dirichlet characters.
No independence of global cell membership is assumed. -/
theorem source_original_gram_global_cell_one_prime_reduction434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (χ ψ : ℕ → ℂ)
    (hχ : ∀ u v : ℕ, χ (u*v) = χ u * χ v)
    (hψ : ∀ u v : ℕ, ψ (u*v) = ψ u * ψ v)
    (i : ι) :
    sourceOriginalGramCellEntry434 S mu h j χ ψ =
    ∑ r : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
      ((sourceOriginalGramOtherPrimeMass434 S mu i r : ℝ):ℂ) *
      star (χ (sourceOriginalGramOtherPrimeProduct434 S i r)) *
      ψ (sourceOriginalGramOtherPrimeProduct434 S i r) *
      sourceOriginalGramLocalPrimeSlice434 S mu h j χ ψ i r := by
  classical
  let e := sourceOriginalGramPrimeSplit434 S i
  let R : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) → ℕ :=
    sourceOriginalGramOtherPrimeProduct434 S i
  let W : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}) → ℝ :=
    sourceOriginalGramOtherPrimeMass434 S mu i
  have hPoint (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})
      (p : {p : ℕ // p ∈ S i}) :
      ((sourceOriginalGramPrimeMass434 S mu (e.symm (p,r)) : ℝ):ℂ) *
        (if sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
         then star (χ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))) *
            ψ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
         else 0) =
      ((W r:ℝ):ℂ) * star (χ (R r)) * ψ (R r) *
      ((mu i p.val:ℝ):ℂ) *
        (if sourceOriginalLiteralLogCell434 h j (p.val * R r)
         then star (χ p.val) * ψ p.val else 0) := by
    rw [source_original_gram_physical_mass_slice434,
        source_original_gram_physical_prime_slice434]
    simp only [R,W,Complex.ofReal_mul]
    by_cases hc : sourceOriginalLiteralLogCell434 h j
        (p.val * sourceOriginalGramOtherPrimeProduct434 S i r)
    · simp only [if_pos hc, hχ, hψ, star_mul]
      ring
    · simp only [if_neg hc]
      ring
  have hfubini := source_original_gram_one_prime_fubini434 S i
    (fun a => ((sourceOriginalGramPrimeMass434 S mu a : ℝ):ℂ) *
      (if sourceOriginalLiteralLogCell434 h j
         (sourceOriginalGramPrimeProduct434 S a)
       then star (χ (sourceOriginalGramPrimeProduct434 S a)) *
         ψ (sourceOriginalGramPrimeProduct434 S a) else 0))
  unfold sourceOriginalGramCellEntry434
  calc
    _ = ∑ r : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
        ∑ p : {p : ℕ // p ∈ S i},
          ((sourceOriginalGramPrimeMass434 S mu (e.symm (p,r)):ℝ):ℂ) *
          (if sourceOriginalLiteralLogCell434 h j
             (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
           then star (χ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))) *
             ψ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
           else 0) := hfubini
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      change (∑ p : {p : ℕ // p ∈ S i},
          ((sourceOriginalGramPrimeMass434 S mu (e.symm (p,r)):ℝ):ℂ) *
            (if sourceOriginalLiteralLogCell434 h j
               (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
             then star (χ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))) *
                ψ (sourceOriginalGramPrimeProduct434 S (e.symm (p,r)))
             else 0)) =
          ((W r:ℝ):ℂ) * star (χ (R r)) * ψ (R r) *
            sourceOriginalGramLocalPrimeSlice434 S mu h j χ ψ i r
      unfold sourceOriginalGramLocalPrimeSlice434
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simpa only [R, mul_assoc] using hPoint r p
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveGram -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The ACTUAL SOURCE03 two-primitive-character GLOBAL cell Gram
entry: conductors may differ and are represented at their real
original levels, with all source prime indices and probabilities
kept literal. -/
noncomputable def sourceOriginalActualPrimitiveGramEntry434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) : ℂ :=
  sourceOriginalGramCellEntry434 S mu h j
    (fun n => c.2 (n : ZMod (c.1.val+1)))
    (fun n => d.2 (n : ZMod (d.1.val+1)))

/-- First ACTUAL arithmetic reduction of the SOURCE03 offdiagonal
global cell Gram for two ORIGINAL primitive Dirichlet characters
(with distinct possible moduli). Unlike a generic independent
character-mean argument, the global product cell has been
conditioned EXACTLY on all other marked BIG prime labels.
The remaining one-prime character sum lives in its genuine
MOVING cell interval; no Siegel–Walfisz saving is assumed. -/
theorem source_original_actual_primitive_global_gram_slice434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (i : ι) :
    sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d =
    ∑ r : ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
      ((sourceOriginalGramOtherPrimeMass434 S mu i r : ℝ):ℂ) *
      star (c.2 ((sourceOriginalGramOtherPrimeProduct434 S i r :
        ℕ) : ZMod (c.1.val+1))) *
      d.2 ((sourceOriginalGramOtherPrimeProduct434 S i r :
        ℕ) : ZMod (d.1.val+1)) *
      sourceOriginalGramLocalPrimeSlice434 S mu h j
        (fun n => c.2 (n : ZMod (c.1.val+1)))
        (fun n => d.2 (n : ZMod (d.1.val+1))) i r := by
  have hχ (u v : ℕ) :
      c.2 ((u*v : ℕ) : ZMod (c.1.val+1)) =
        c.2 (u : ZMod (c.1.val+1)) *
        c.2 (v : ZMod (c.1.val+1)) := by
    simpa only [Nat.cast_mul] using
      (map_mul c.2 (u : ZMod (c.1.val+1))
        (v : ZMod (c.1.val+1)))
  have hψ (u v : ℕ) :
      d.2 ((u*v : ℕ) : ZMod (d.1.val+1)) =
        d.2 (u : ZMod (d.1.val+1)) *
        d.2 (v : ZMod (d.1.val+1)) := by
    simpa only [Nat.cast_mul] using
      (map_mul d.2 (u : ZMod (d.1.val+1))
        (v : ZMod (d.1.val+1)))
  exact source_original_gram_global_cell_one_prime_reduction434
    S mu h j
    (fun n => c.2 (n : ZMod (c.1.val+1)))
    (fun n => d.2 (n : ZMod (d.1.val+1)))
    hχ hψ i
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramRestLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Exact source03 marginal probability on the TRUE indexed
collection of all OTHER marked prime slots, with possibly
different prime support S_i and real reciprocal-prime mu_i. -/
theorem source_original_gram_other_prime_law_one434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i, ∑ p ∈ S i, mu i p = 1)
    (i : ι) :
    (∑ r : ((k : {k : ι // k ≠ i}) →
        {p : ℕ // p ∈ S k.val}),
      sourceOriginalGramOtherPrimeMass434 S mu i r) = 1 := by
  classical
  have hrow (k : {k : ι // k ≠ i}) :
      (∑ p : {p : ℕ // p ∈ S k.val}, mu k.val p.val) = 1 := by
    simpa using (Finset.sum_attach (S k.val)
      (fun p : ℕ => mu k.val p)).trans (hmu k.val)
  unfold sourceOriginalGramOtherPrimeMass434
  calc
    (∑ r : ((k : {k : ι // k ≠ i}) →
        {p : ℕ // p ∈ S k.val}),
       ∏ k : {k : ι // k ≠ i}, mu k.val (r k).val) =
     ∏ k : {k : ι // k ≠ i},
       ∑ p : {p : ℕ // p ∈ S k.val}, mu k.val p.val :=
        (Fintype.prod_sum
          (fun (k : {k : ι // k ≠ i})
               (p : {p : ℕ // p ∈ S k.val}) => mu k.val p.val)).symm
    _ = 1 := by
      have hk (k : {k : ι // k ≠ i}) :
          (∑ p ∈ (S k.val).attach, mu k.val p.val) = 1 := by
        rw [Finset.sum_attach]
        exact hmu k.val
      change (∏ k : {k : ι // k ≠ i},
        ∑ p : {p : ℕ // p ∈ S k.val}, mu k.val p.val) = 1
      simp only [hrow, Finset.prod_const_one]

/-- Every TRUE source03 other-prime labelled tuple receives
nonnegative probability under the real harmonic product law. -/
theorem source_original_gram_other_prime_law_nonneg434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (i : ι)
    (r : (k : {k : ι // k ≠ i}) →
      {p : ℕ // p ∈ S k.val}) :
    0 ≤ sourceOriginalGramOtherPrimeMass434 S mu i r := by
  unfold sourceOriginalGramOtherPrimeMass434
  apply Finset.prod_nonneg
  intro k _
  exact hmu k.val (r k).val (r k).property
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramOffdiagBound -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A quantitatively exact transfer for ACTUAL original
source03 GLOBAL log-cell primitive-character Gram entries.
The ONLY remaining source analytic input is a genuine bound
on every harmonic weighted ONE-PRIME character sum in the
moving source interval, not a fake zero-mean assumption.
The other original physical prime marks have total mass ONE,
and the exterior characters have modulus at most ONE. -/
theorem source_original_actual_primitive_gram_offdiag_from_one_prime434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hPrime : ∀ r :
       ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val}),
       ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
          (fun n => c.2 (n:ZMod (c.1.val+1)))
          (fun n => d.2 (n:ZMod (d.1.val+1))) i r‖ ≤ ε) :
    ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d‖ ≤ ε := by
  rw [source_original_actual_primitive_global_gram_slice434
    S mu h j Q c d hc hd i]
  have hbound (r :
     ((k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})) :
    ‖((sourceOriginalGramOtherPrimeMass434 S mu i r:ℝ):ℂ) *
      star (c.2 ((sourceOriginalGramOtherPrimeProduct434 S i r:ℕ):
         ZMod (c.1.val+1))) *
      d.2 ((sourceOriginalGramOtherPrimeProduct434 S i r:ℕ):
         ZMod (d.1.val+1)) *
      sourceOriginalGramLocalPrimeSlice434 S mu h j
         (fun n => c.2 (n:ZMod (c.1.val+1)))
         (fun n => d.2 (n:ZMod (d.1.val+1))) i r‖ ≤
    sourceOriginalGramOtherPrimeMass434 S mu i r * ε := by
    have hMass := source_original_gram_other_prime_law_nonneg434
       S mu hmuPos i r
    have hcNorm := (c.2).norm_le_one
       ((sourceOriginalGramOtherPrimeProduct434 S i r:ℕ):
         ZMod (c.1.val+1))
    have hdNorm := (d.2).norm_le_one
       ((sourceOriginalGramOtherPrimeProduct434 S i r:ℕ):
         ZMod (d.1.val+1))
    simp only [norm_mul, norm_star, Complex.norm_real,
       Real.norm_eq_abs, abs_of_nonneg hMass]
    have hmul : ‖c.2 ((sourceOriginalGramOtherPrimeProduct434
       S i r:ℕ):ZMod (c.1.val+1))‖ *
       ‖d.2 ((sourceOriginalGramOtherPrimeProduct434
       S i r:ℕ):ZMod (d.1.val+1))‖ ≤ 1 := by
       nlinarith [mul_le_mul hcNorm hdNorm
          (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [mul_le_mul_of_nonneg_left
       (mul_le_mul hmul (hPrime r)
          (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)) hMass]
  calc
    _ ≤ ∑ r : ((k : {k : ι // k ≠ i}) →
        {p : ℕ // p ∈ S k.val}),
         ‖((sourceOriginalGramOtherPrimeMass434 S mu i r:ℝ):ℂ) *
           star (c.2 ((sourceOriginalGramOtherPrimeProduct434
             S i r:ℕ):ZMod (c.1.val+1))) *
           d.2 ((sourceOriginalGramOtherPrimeProduct434
             S i r:ℕ):ZMod (d.1.val+1)) *
           sourceOriginalGramLocalPrimeSlice434 S mu h j
             (fun n => c.2 (n:ZMod (c.1.val+1)))
             (fun n => d.2 (n:ZMod (d.1.val+1))) i r‖ :=
         norm_sum_le _ _
    _ ≤ ∑ r : ((k : {k : ι // k ≠ i}) →
         {p : ℕ // p ∈ S k.val}),
         sourceOriginalGramOtherPrimeMass434 S mu i r * ε :=
         Finset.sum_le_sum (fun r hr => hbound r)
    _ = ε := by
         rw [← Finset.sum_mul]
         rw [source_original_gram_other_prime_law_one434 S mu hmu i]
         ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCanonicalKnuCellMassInputs -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- SOURCE03's true finite primitive-Knu active log-cell lists,
with the ACTUAL labelled prime-group harmonic probability,
automatically meet the BOTH independent original active
cell-mass lower and total-mass upper restrictions needed
for true C6 four-dyad selected arithmetic. These are not
separately supplied "spectral" or normalizing hypotheses.
The ν-selected A/B prime supports remain unchanged. -/
theorem source_original_true_canonical_Knu_cell_mass_inputs434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p∈P g,1/(p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (hPrime : ∀ g p,p∈P g → p.Prime)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi) :
    let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let massA := sourceOriginalProbeCellA434 m P V ν hA
    let massB := sourceOriginalProbeCellB434 m P V ν hB
    (∀ j ∈ JA,xi ≤ massA j) ∧
    (∀ j ∈ JB,xi ≤ massB j) ∧
    (∑ j∈JA,massA j) ≤ 1 ∧
    (∑ j∈JB,massB j) ≤ 1 := by
  classical
  dsimp only
  let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let massA := sourceOriginalProbeCellA434 m P V ν hA
  let massB := sourceOriginalProbeCellB434 m P V ν hB
  have hLowA : ∀ j∈JA,xi ≤ massA j := by
    intro j hj
    exact (source_original_probe_active_cell_A_mem_iff434
      m P V ν hA xi hhA hxi j).mp hj
  have hLowB : ∀ j∈JB,xi ≤ massB j := by
    intro j hj
    exact (source_original_probe_active_cell_B_mem_iff434
      m P V ν hB xi hhB hxi j).mp hj
  have hTotalA : (∑ j∈JA,massA j) ≤ 1 := by
    exact source_original_true_prime_cell_probability_total434
      (fun z : ν.1 => P z.val.1)
      (fun z : ν.1 => V z.val.1)
      hA hhA JA
      (fun z => hV z.val.1)
      (fun z => hVpos z.val.1)
      (fun z p hp => hPrime z.val.1 p hp)
  have hTotalB : (∑ j∈JB,massB j) ≤ 1 := by
    exact source_original_true_prime_cell_probability_total434
      (fun z : ν.2 => P z.val.1)
      (fun z : ν.2 => V z.val.1)
      hB hhB JB
      (fun z => hV z.val.1)
      (fun z => hVpos z.val.1)
      (fun z p hp => hPrime z.val.1 p hp)
  exact ⟨hLowA,hLowB,hTotalA,hTotalB⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalProductSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Every ORIGINAL source03 free SOURCE mark state selects a
genuine attainable B-block integer prime product, rather
than a synthetic product outside the true prime law.
The selected ν.2 BIG marked slots retain their original
distinct coordinate labels and exact prime support. -/
theorem source_original_true_source_B_product_atom_supported434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (s : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val) ∈
    sourceOriginalPhysicalProductAtomSupport434
      (fun z : ν.2 => P z.val.1) := by
  classical
  let eB := sourceOriginalProbeSourceBFreeEmbedding434
    J ell m hmJ ν
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let selected : SourceOriginalGramPrimeTuple434 SB :=
    fun z => ⟨(s (eB z).1 (eB z).2).val,
              (s (eB z).1 (eB z).2).property⟩
  have hEq :
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val) =
      sourceOriginalGramPrimeProduct434 SB selected := by
    rfl
  rw [hEq]
  exact Finset.mem_image.mpr ⟨selected,Finset.mem_univ _,rfl⟩

/-- Original TARGET-end ν.1 prime products also have exact
finite attainable integer atom support after all unselected
free target marks are retained. -/
theorem source_original_true_target_A_product_atom_supported434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (t : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (t g i).val) ∈
    sourceOriginalPhysicalProductAtomSupport434
      (fun z : ν.1 => P z.val.1) := by
  classical
  let eA := sourceOriginalProbeTargetAFreeEmbedding434
    J ell m hmJ ν
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let selected : SourceOriginalGramPrimeTuple434 SA :=
    fun z => ⟨(t (eA z).1 (eA z).2).val,
              (t (eA z).1 (eA z).2).property⟩
  have hEq :
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (t g i).val) =
      sourceOriginalGramPrimeProduct434 SA selected := by
    rfl
  rw [hEq]
  exact Finset.mem_image.mpr ⟨selected,Finset.mem_univ _,rfl⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedPhysicalAtomMarginalA -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact original SOURCE03 target physical free-mark harmonic marginal
at EACH selected integer product atom. ALL other ν-dependent
physical marks are integrated out with their original masses:
the result is LITERALLY the independent TARGET-A reciprocal
prime product atom probability (not a synthetic uniform law).
This equality is for each integer n, including zero mass and
unattainable n, and preserves duplicate prime numerical values. -/
theorem source_original_true_target_A_physical_atom_marginal434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g) (n : ℕ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let S : ν.1 → Finset ℕ := fun z => P z.val.1
    let muT : ν.1 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let prodT : X → ℕ := fun s =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (s g i).val)
    (∑ s : X, if prodT s=n then w s else 0) =
      sourceOriginalPhysicalProductAtom434 S muT n := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let S : ν.1 → Finset ℕ := fun z => P z.val.1
  let muT : ν.1 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let prodT : X → ℕ := fun s =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (s g i).val)
  let e := sourceOriginalProbeTargetAFreeEmbedding434
    J ell m hmJ ν
  let F : (∀ z : ν.1, BP z.val.1) → ℝ := fun a =>
    if (∏ z : ν.1, (a z).val)=n then 1 else 0
  have hMarg := source_original_probe_true_target_A_marginal434
    J ell m hmJ ν P V hV hVpos F
  have hMargEq :
      (∑ s : X,
        w s*(if prodT s=n then (1:ℝ) else 0)) =
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S muT a *
        (if sourceOriginalGramPrimeProduct434 S a=n
         then (1:ℝ) else 0)) := by
    convert hMarg using 1
    · apply Finset.sum_congr rfl
      intro s hs
      rfl
    · apply Finset.sum_congr rfl
      intro a ha
      rfl
  have hLHS :
      (∑ s : X, if prodT s=n then w s else 0) =
      (∑ s : X,
        w s*(if prodT s=n then (1:ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hh : prodT s=n <;> simp [hh]
  have hRHS :
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S muT a *
        (if sourceOriginalGramPrimeProduct434 S a=n
         then (1:ℝ) else 0)) =
      sourceOriginalPhysicalProductAtom434 S muT n := by
    unfold sourceOriginalPhysicalProductAtom434
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hh : sourceOriginalGramPrimeProduct434 S a=n
    · simp [hh]
    · simp [hh]
  exact hLHS.trans (hMargEq.trans hRHS)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedPhysicalAtomMarginalB -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact original SOURCE03 physical free-mark harmonic marginal
at EACH selected integer product atom. ALL other ν-dependent
physical marks are integrated out with their original masses:
the result is LITERALLY the independent SOURCE-B reciprocal
prime product atom probability (not a synthetic uniform law).
This equality is for each integer n, including zero mass and
unattainable n, and preserves duplicate prime numerical values. -/
theorem source_original_true_source_B_physical_atom_marginal434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g) (n : ℕ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let S : ν.2 → Finset ℕ := fun z => P z.val.1
    let muS : ν.2 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let prodS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)
    (∑ s : X, if prodS s=n then w s else 0) =
      sourceOriginalPhysicalProductAtom434 S muS n := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let S : ν.2 → Finset ℕ := fun z => P z.val.1
  let muS : ν.2 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let prodS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val)
  let e := sourceOriginalProbeSourceBFreeEmbedding434
    J ell m hmJ ν
  let F : (∀ z : ν.2, BP z.val.1) → ℝ := fun a =>
    if (∏ z : ν.2, (a z).val)=n then 1 else 0
  have hMarg := source_original_probe_true_source_B_marginal434
    J ell m hmJ ν P V hV hVpos F
  have hMargEq :
      (∑ s : X,
        w s*(if prodS s=n then (1:ℝ) else 0)) =
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S muS a *
        (if sourceOriginalGramPrimeProduct434 S a=n
         then (1:ℝ) else 0)) := by
    convert hMarg using 1
    · apply Finset.sum_congr rfl
      intro s hs
      rfl
    · apply Finset.sum_congr rfl
      intro a ha
      rfl
  have hLHS :
      (∑ s : X, if prodS s=n then w s else 0) =
      (∑ s : X,
        w s*(if prodS s=n then (1:ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hh : prodS s=n <;> simp [hh]
  have hRHS :
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S muS a *
        (if sourceOriginalGramPrimeProduct434 S a=n
         then (1:ℝ) else 0)) =
      sourceOriginalPhysicalProductAtom434 S muS n := by
    unfold sourceOriginalPhysicalProductAtom434
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hh : sourceOriginalGramPrimeProduct434 S a=n
    · simp [hh]
    · simp [hh]
  exact hLHS.trans (hMargEq.trans hRHS)
end Green64Analytic.CorrelationSquare

end

/-! ## ActualPrimitiveColumnL1 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact one-column harmonic L1 bound for the LITERAL original full
primitive kernel. The cell masses are the actual pushforward masses
of the same finite law used in the integral. The threshold xi and
number of active cells do not enter the bound. -/
theorem b584_actual_primitive_column_l1
    {I : Type} (S : Finset I) (mu : I → ℝ) (X : I → ℕ)
    (Q : ℕ) (active : Finset ℤ) (h : ℝ) (hh : 0<h)
    (mass : ℤ → ℝ) (D : ℕ)
    (hmu : ∀ x∈S,0 ≤ mu x)
    (hMass : ∀ j∈active, mass j=∑ x∈S,
      if sourceOriginalLiteralLogCell434 h j (X x) then mu x else 0)
    (hPos : ∀ j∈active,0 < mass j) :
    (∑ x∈S,mu x*‖sourceOriginalActualPrimitiveGlobalKernel434
      Q active h mass D (X x)‖) ≤
      ((sourceOriginalActualPrimitiveCharacters434 Q).card:ℝ) := by
  classical
  let C : ℝ := (sourceOriginalActualPrimitiveCharacters434 Q).card
  have hC : 0≤C := Nat.cast_nonneg _
  by_cases he : ∃ j∈active,sourceOriginalLiteralLogCell434 h j D
  · obtain ⟨j,hj,hjD⟩ := he
    have hEq (x : I) :
        sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D (X x) =
        if sourceOriginalLiteralLogCell434 h j (X x) then
          (mass j:ℂ)⁻¹ * ∑ c∈sourceOriginalActualPrimitiveCharacters434 Q,
            star (c.2 (D:ZMod (c.1.val+1))) *
              c.2 (X x:ZMod (c.1.val+1)) else 0 := by
      unfold sourceOriginalActualPrimitiveGlobalKernel434
        sourceOriginalCharacterCellKernel434
      rw [Finset.sum_eq_single j]
      · simp only [hjD,true_and]
      · intro k hk hkj
        have hkD : ¬sourceOriginalLiteralLogCell434 h k D := by
          intro hkD
          exact hkj (source_original_literal_log_cells_unique434
            h hh D k j hkD hjD)
        simp only [hkD,false_and,ite_false]
      · exact fun hn => False.elim (hn hj)
    have hBound (x : I) :
        ‖sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D (X x)‖ ≤
        if sourceOriginalLiteralLogCell434 h j (X x) then (mass j)⁻¹*C else 0 := by
      rw [hEq]
      split_ifs with hx
      · rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (hPos j hj)]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hPos j hj).le)
        exact source_original_character_sum_bound434
          (sourceOriginalActualPrimitiveCharacters434 Q)
          (fun c n => c.2 (n:ZMod (c.1.val+1))) D (X x)
          (fun c _ => ⟨c.2.norm_le_one _,c.2.norm_le_one _⟩)
      · simp
    calc
      _ ≤ ∑ x∈S, mu x*(if sourceOriginalLiteralLogCell434 h j (X x)
          then (mass j)⁻¹*C else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hBound x) (hmu x hx)
      _ = (∑ x∈S,if sourceOriginalLiteralLogCell434 h j (X x)
          then mu x else 0)*((mass j)⁻¹*C) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      _ = C := by rw [← hMass j hj]; field_simp [(hPos j hj).ne']
  · have hZero (x : I) :
        sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D (X x)=0 := by
      unfold sourceOriginalActualPrimitiveGlobalKernel434
        sourceOriginalCharacterCellKernel434
      apply Finset.sum_eq_zero
      intro j hj
      have hn : ¬sourceOriginalLiteralLogCell434 h j D :=
        fun hd => he ⟨j,hj,hd⟩
      simp only [hn,false_and,ite_false]
    simp only [hZero,norm_zero,mul_zero,Finset.sum_const_zero]
    exact hC

/-- The same exact column estimate for the true independent product
law, its literal logarithmic cell probabilities, and its ORIGINAL
finite active family. No external mass-normalization premise. -/
theorem b584_actual_product_law_column_l1
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i n,n∈S i → 0 ≤ mu i n)
    (Q : ℕ) (h xi : ℝ) (hh : 0<h) (hxi : 0<xi) (D : ℕ) :
    (∑ a∈Fintype.piFinset S,sourceSharedLaw434 mu a *
      ‖sourceOriginalActualPrimitiveGlobalKernel434 Q
        (sourceOriginalFiniteActiveLogCells434 S mu h xi) h
        (sourceOriginalActualCellProbability434 S mu h) D (∏ i,a i)‖) ≤
      (Q:ℝ)^2 := by
  have hOne := b584_actual_primitive_column_l1
    (Fintype.piFinset S) (sourceSharedLaw434 mu) (fun a => ∏ i,a i)
    Q (sourceOriginalFiniteActiveLogCells434 S mu h xi) h hh
    (sourceOriginalActualCellProbability434 S mu h) D ?_ ?_ ?_
  · have hc : ((sourceOriginalActualPrimitiveCharacters434 Q).card:ℝ)≤(Q:ℝ)^2 := by
      exact_mod_cast source_original_actual_primitive_count434 Q
    exact hOne.trans hc
  · intro a ha
    unfold sourceSharedLaw434
    apply Finset.prod_nonneg
    intro i hi
    exact hmu i (a i) ((Fintype.mem_piFinset.mp ha) i)
  · intro j hj
    rfl
  · intro j hj
    exact hxi.trans_le ((source_original_finite_active_log_cell_mem_iff434
      S mu h xi hh hxi j).mp hj)
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualTwoBlockHarmonicL1 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The complete signed two-block primitive kernel, averaged in BOTH
original independent selected-prime laws. Sign is kept inside its
norm; the estimate has no inverse active-cell mass. -/
theorem b584_actual_two_block_product_l1
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (muA : ιA → ℕ → ℝ) (muB : ιB → ℕ → ℝ)
    (hmuA : ∀ i n,n∈SA i → 0 ≤ muA i n)
    (hmuB : ∀ i n,n∈SB i → 0 ≤ muB i n)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB)
    (hxi : 0<xi) (DA DB r : ℕ) :
    (∑ a∈Fintype.piFinset SA,sourceSharedLaw434 muA a *
      ∑ b∈Fintype.piFinset SB,sourceSharedLaw434 muB b *
        ‖sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalFiniteActiveLogCells434 SA muA hA xi)
          (sourceOriginalFiniteActiveLogCells434 SB muB hB xi)
          hA hB (sourceOriginalActualCellProbability434 SA muA hA)
          (sourceOriginalActualCellProbability434 SB muB hB)
          DA (∏i,a i) DB (∏i,b i) r‖) ≤ (Q:ℝ)^4 := by
  let KA := fun a : ιA → ℕ => sourceOriginalActualPrimitiveGlobalKernel434 Q
    (sourceOriginalFiniteActiveLogCells434 SA muA hA xi) hA
    (sourceOriginalActualCellProbability434 SA muA hA) DA (∏i,a i)
  let KB := fun b : ιB → ℕ => sourceOriginalActualPrimitiveGlobalKernel434 Q
    (sourceOriginalFiniteActiveLogCells434 SB muB hB xi) hB
    (sourceOriginalActualCellProbability434 SB muB hB) DB (∏i,b i)
  have hOneA := b584_actual_product_law_column_l1 SA muA hmuA Q hA xi hhA hxi DA
  have hOneB := b584_actual_product_law_column_l1 SB muB hmuB Q hB xi hhB hxi DB
  have hBn : 0 ≤ ∑ b∈Fintype.piFinset SB,sourceSharedLaw434 muB b * ‖KB b‖ := by
    apply Finset.sum_nonneg
    intro b hb
    exact mul_nonneg (source_shared_law_nonneg434 SB muB hmuB b hb) (norm_nonneg _)
  calc
    _ = (∑ a∈Fintype.piFinset SA,sourceSharedLaw434 muA a * ‖KA a‖) *
        (∑ b∈Fintype.piFinset SB,sourceSharedLaw434 muB b * ‖KB b‖) := by
      simp only [sourceOriginalActualPrimitiveComparisonKernel434,
        norm_mul,norm_neg,norm_pow,norm_one,one_pow,one_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [KA,KB]
      ring
    _ ≤ (Q:ℝ)^2*(Q:ℝ)^2 := mul_le_mul hOneA hOneB hBn (sq_nonneg _)
    _ = _ := by ring

/-- This is only an abbreviation for the literal finite sum: the
auxiliary law, both selected laws, original DA/DB, both actual active
families, and the signed physical comparison kernel occur verbatim. -/
def b584OriginalProbeHarmonicComparisonMass
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) : ℝ :=
  ∑ a∈Fintype.piFinset (fun z : nu.1 => P z.val.1),
    sourceSharedLaw434 (fun z : nu.1 => sourcePrimeSharedAtom434 (V z.val.1)) a *
      ∑ b∈Fintype.piFinset (fun z : nu.2 => P z.val.1),
        sourceSharedLaw434 (fun z : nu.2 => sourcePrimeSharedAtom434 (V z.val.1)) b *
          ‖sourceOriginalActualPrimitiveComparisonKernel434 Q
            (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
            (sourceOriginalProbeActiveCellsB434 m P V nu hB xi)
            hA hB (sourceOriginalProbeCellA434 m P V nu hA)
            (sourceOriginalProbeCellB434 m P V nu hB)
            (sourceOriginalProbeDA434 m nu aux) (∏z,a z)
            (sourceOriginalProbeDB434 m nu aux) (∏z,b z)
            (nu.1.card+nu.2.card)‖

theorem b584_original_probe_two_block_l1
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ) (hV : ∀g,0 < V g)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    b584OriginalProbeHarmonicComparisonMass m nu P V Q hA hB xi aux ≤ (Q:ℝ)^4 := by
  apply b584_actual_two_block_product_l1
    (fun z : nu.1 => P z.val.1) (fun z : nu.2 => P z.val.1)
    (fun z : nu.1 => sourcePrimeSharedAtom434 (V z.val.1))
    (fun z : nu.2 => sourcePrimeSharedAtom434 (V z.val.1))
    _ _ Q hA hB xi hhA hhB hxi
  · intro i n hn
    dsimp only [sourcePrimeSharedAtom434]
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (hV i.val.1).le)
  · intro i n hn
    dsimp only [sourcePrimeSharedAtom434]
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (hV i.val.1).le)

/-- The original independent auxiliary law stays OUTSIDE the two
column averages. Its exact mass is one, including repeated primes. -/
theorem b584_original_auxiliary_joint_l1
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀g,V g=∑p∈P g,1/(p:ℝ)) (hVp : ∀g,0 < V g)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    (∑ aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      sourceSharedLaw434
        (fun z => sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu V z)) aux *
      b584OriginalProbeHarmonicComparisonMass m nu P V Q hA hB xi aux) ≤ (Q:ℝ)^4 := by
  have hAux : ∀aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      0 ≤ sourceSharedLaw434
        (fun z => sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu V z)) aux := by
    apply source_shared_law_nonneg434
    intro z p hp
    have hv : 0 < sourceOriginalProbeAuxV434 m nu V z := by
      cases z with
      | inl z => exact hVp z.val.1
      | inr z => exact hVp z.val.1
    dsimp only [sourcePrimeSharedAtom434]
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg p) hv.le)
  calc
    _ ≤ ∑ aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
        sourceSharedLaw434
          (fun z => sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu V z)) aux *
          (Q:ℝ)^4 := by
      apply Finset.sum_le_sum
      intro aux ha
      exact mul_le_mul_of_nonneg_left
        (b584_original_probe_two_block_l1 m nu P V hVp Q hA hB xi hhA hhB hxi aux)
        (hAux aux ha)
    _ = (Q:ℝ)^4 := by
      rw [←Finset.sum_mul,source_original_probe_aux_law_total434 m nu P V hV hVp,one_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualCellCoordinateReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {I G : Type}

/-- Coordinate transport for the original independent raw prime law.
Numerical repetitions are retained; no divisor or distinctness filter is added. -/
def b607RawPrimeEquiv434 (e : I ≃ G) : (I → ℕ) ≃ (G → ℕ) :=
  e.arrowCongr (Equiv.refl ℕ)

@[simp] theorem b607_raw_prime_equiv_apply434
    (e : I ≃ G) (a : I → ℕ) (i : I) :
    b607RawPrimeEquiv434 e a (e i)=a i := by
  simp [b607RawPrimeEquiv434,Equiv.arrowCongr_apply]

variable [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- Exact product-law carrier transport, including all repeated values. -/
theorem b607_raw_prime_mem_reindex434
    (e : I ≃ G) (S : G → Finset ℕ) (a : I → ℕ) :
    b607RawPrimeEquiv434 e a ∈ Fintype.piFinset S ↔
      a ∈ Fintype.piFinset (fun i => S (e i)) := by
  simp only [Fintype.mem_piFinset]
  constructor
  · intro h i
    simpa only [b607_raw_prime_equiv_apply434] using h (e i)
  · intro h g
    obtain ⟨i,rfl⟩ := e.surjective g
    simpa only [b607_raw_prime_equiv_apply434] using h i

omit [DecidableEq I] [DecidableEq G] in
/-- The numerical product defining the actual physical log cell is unchanged. -/
theorem b607_raw_prime_product_reindex434
    (e : I ≃ G) (a : I → ℕ) :
    (∏i,a i)=∏g,b607RawPrimeEquiv434 e a g := by
  exact Fintype.prod_equiv e _ _ (fun i => (b607_raw_prime_equiv_apply434 e a i).symm)

/-- Exact mass transport for the supplied ORIGINAL independent law. It
applies in particular to 1/(p V_g), without conditioning or renormalizing. -/
theorem b607_shared_law_reindex434
    (e : I ≃ G) (mu : G → ℕ → ℝ) (a : I → ℕ) :
    sourceSharedLaw434 (fun i => mu (e i)) a =
      sourceSharedLaw434 mu (b607RawPrimeEquiv434 e a) := by
  unfold sourceSharedLaw434
  exact Fintype.prod_equiv e _ _ (fun i => by rw [b607_raw_prime_equiv_apply434])

/-- Finite raw-law coordinate reindex for any test, with the full carrier. -/
theorem b607_raw_prime_sum_reindex434
    {A : Type} [AddCommMonoid A]
    (e : I ≃ G) (S : G → Finset ℕ) (f : (G → ℕ) → A) :
    (∑a∈Fintype.piFinset (fun i => S (e i)),f (b607RawPrimeEquiv434 e a)) =
      ∑b∈Fintype.piFinset S,f b := by
  let E := b607RawPrimeEquiv434 e
  apply Finset.sum_bij (fun a _ => E a)
  · intro a ha
    exact (b607_raw_prime_mem_reindex434 e S a).mpr ha
  · intro a ha b hb hab
    exact E.injective hab
  · intro b hb
    refine ⟨E.symm b,?_,E.apply_symm_apply b⟩
    apply (b607_raw_prime_mem_reindex434 e S (E.symm b)).mp
    change E (E.symm b) ∈ Fintype.piFinset S
    rw [E.apply_symm_apply]
    exact hb
  · intro a ha
    rfl

/-- The ORIGINAL half-open log-cell probability is exactly invariant
under the supplied coordinate equivalence, for every actual cell j.
No positivity or mass-floor hypothesis is needed for this identity. -/
theorem b607_actual_cell_probability_reindex434
    (e : I ≃ G) (S : G → Finset ℕ) (mu : G → ℕ → ℝ) (h : ℝ) (j : ℤ) :
    sourceOriginalActualCellProbability434 (fun i => S (e i)) (fun i => mu (e i)) h j =
      sourceOriginalActualCellProbability434 S mu h j := by
  unfold sourceOriginalActualCellProbability434
  calc
    _ = ∑a∈Fintype.piFinset (fun i => S (e i)),
        if sourceOriginalLiteralLogCell434 h j (∏g,b607RawPrimeEquiv434 e a g) then
          sourceSharedLaw434 mu (b607RawPrimeEquiv434 e a) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [b607_raw_prime_product_reindex434 e a,b607_shared_law_reindex434 e mu a]
    _ = _ := b607_raw_prime_sum_reindex434 e S
      (fun a => if sourceOriginalLiteralLogCell434 h j (∏g,a g) then
        sourceSharedLaw434 mu a else 0)

/-- The candidate-cell carrier itself is transported exactly; active
cells are not compared merely modulo zero mass or an enlarged cutoff. -/
theorem b607_candidate_log_cells_reindex434
    (e : I ≃ G) (S : G → Finset ℕ) (h : ℝ) :
    sourceOriginalCandidateLogCells434 (fun i => S (e i)) h =
      sourceOriginalCandidateLogCells434 S h := by
  ext j
  simp only [sourceOriginalCandidateLogCells434,Finset.mem_image]
  constructor
  · rintro ⟨a,ha,hj⟩
    refine ⟨b607RawPrimeEquiv434 e a,
      (b607_raw_prime_mem_reindex434 e S a).mpr ha,?_⟩
    rw [←b607_raw_prime_product_reindex434 e a]
    exact hj
  · rintro ⟨b,hb,hj⟩
    let a := (b607RawPrimeEquiv434 e).symm b
    have he : b607RawPrimeEquiv434 e a=b := (b607RawPrimeEquiv434 e).apply_symm_apply b
    refine ⟨a,(b607_raw_prime_mem_reindex434 e S a).mp (by rw [he]; exact hb),?_⟩
    rw [b607_raw_prime_product_reindex434 e a,he]
    exact hj

/-- Actual active cells, with the SAME xi threshold and true probabilities. -/
theorem b607_finite_active_log_cells_reindex434
    (e : I ≃ G) (S : G → Finset ℕ) (mu : G → ℕ → ℝ) (h xi : ℝ) :
    sourceOriginalFiniteActiveLogCells434 (fun i => S (e i)) (fun i => mu (e i)) h xi =
      sourceOriginalFiniteActiveLogCells434 S mu h xi := by
  unfold sourceOriginalFiniteActiveLogCells434
  rw [b607_candidate_log_cells_reindex434 e S h]
  congr 1
  funext j
  rw [b607_actual_cell_probability_reindex434 e S mu h j]

/-- The full original primitive-character/cell column survives coordinate
transport exactly, with its true active set and true mass denominator.
The conductor cutoff, arithmetic endpoints and cell width are unchanged. -/
theorem b607_actual_global_kernel_reindex434
    (e : I ≃ G) (S : G → Finset ℕ) (mu : G → ℕ → ℝ)
    (Q : ℕ) (h xi : ℝ) (D X : ℕ) :
    sourceOriginalActualPrimitiveGlobalKernel434 Q
      (sourceOriginalFiniteActiveLogCells434 (fun i => S (e i)) (fun i => mu (e i)) h xi)
      h (sourceOriginalActualCellProbability434 (fun i => S (e i)) (fun i => mu (e i)) h) D X =
    sourceOriginalActualPrimitiveGlobalKernel434 Q
      (sourceOriginalFiniteActiveLogCells434 S mu h xi)
      h (sourceOriginalActualCellProbability434 S mu h) D X := by
  rw [b607_finite_active_log_cells_reindex434 e S mu h xi]
  have hm : sourceOriginalActualCellProbability434 (fun i => S (e i)) (fun i => mu (e i)) h =
      sourceOriginalActualCellProbability434 S mu h := by
    funext j
    exact b607_actual_cell_probability_reindex434 e S mu h j
  rw [hm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualC6AtomValidity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Every TRUE SOURCE03 labelled prime tuple, with its actual
group-dependent support, gives an integer product satisfying
ALL THREE exact conditions of the source C6 atom model:
nonzero product, precisely k_g prime factors (with
multiplicity) from each group g, and no factors outside
the union of the actual group prime supports.
No squarefreeness, no fake independent integer law and no
hypothetical sourceAtomValid premise: group disjointness
and the ACTUAL number of labels per group imply it. -/
theorem source_original_actual_prime_product_C6_atom_valid434
    {I γ : Type} [Fintype I] [DecidableEq I] [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (grp : I → γ) (hGrp : ∀ i, grp i ∈ G)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (k : γ → ℕ)
    (hCount : ∀ g∈G,
      ((Finset.univ : Finset I).filter
        (fun i => grp i = g)).card = k g)
    (a : I → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S (grp i)) :
    Green64SourceC6.sourceAtomValid G S k (∏ i : I, a i) := by
  classical
  have hPos : 0 < ∏ i : I, a i := by
    apply Finset.prod_pos
    intro i hi
    exact (ha i).1.pos
  refine ⟨Nat.ne_of_gt hPos,?_,?_⟩
  · intro g hg
    rw [source_original_actual_group_factorization_sum434
      G S grp hGrp hDisjoint a ha g hg]
    exact hCount g hg
  · intro p hp
    exact source_original_actual_group_prime_product_support434
      G S grp hGrp a ha p hp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6SigmaSlotCard -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact number of ORIGINAL ordered prime-labelled slots
assigned to a specific genuine group g in the sigma model
I = (g:G) × Fin(k_g). This is a counting equality,
not an extra multiplicity premise for the C6 group atom. -/
theorem source_original_c6_sigma_group_slot_count434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (g : G) :
    ((Finset.univ : Finset (Σ h : G, Fin (k h.val))).filter
        (fun z => z.1 = g)).card = k g.val := by
  classical
  let I := Σ h : G, Fin (k h.val)
  let P : I → Prop := fun z => z.1 = g
  let E : {z : I // P z} ≃ Fin (k g.val) := {
    toFun := fun z => by
      rcases z with ⟨⟨h,i⟩,heq⟩
      cases heq
      exact i
    invFun := fun i => ⟨⟨g,i⟩,rfl⟩
    left_inv := by
      intro z
      rcases z with ⟨⟨h,i⟩,heq⟩
      cases heq
      rfl
    right_inv := by intro i; rfl
  }
  calc
    _ = Fintype.card {z : I // P z} := by
      have h := Finset.card_subtype P (Finset.univ : Finset I)
      simpa only [Finset.subtype_univ, Finset.card_univ] using h.symm
    _ = Fintype.card (Fin (k g.val)) := Fintype.card_congr E
    _ = k g.val := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6SigmaAtomValid -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine SOURCE03 ordered prime-label multigroup space
I=Σg∈G Fin(k_g) has exactly the ACTUAL source C6 atom
support/multiplicity validity, NOT merely an abstract
hypothesis about the distribution on integers.
The factorization group clauses are deduced from the
concrete labelled slots and DISJOINT original prime
supports. Repeated primes inside one group are allowed.
This is a precise arithmetic bridge between the real
physical independently labelled law and C6's literal
sourceAtomValid G S k n predicate. -/
theorem source_original_actual_sigma_prime_product_C6_atom_valid434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (a : (Σ g : G, Fin (k g.val)) → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S i.1.val) :
    Green64SourceC6.sourceAtomValid G S k
      (∏ i : Σ g : G, Fin (k g.val), a i) := by
  classical
  let I := Σ g : G, Fin (k g.val)
  let grp : I → γ := fun i => i.1.val
  have hGrp (i : I) : grp i ∈ G := i.1.property
  have hCount (g : γ) (hg : g ∈ G) :
      ((Finset.univ : Finset I).filter
        (fun i => grp i=g)).card = k g := by
    let z : G := ⟨g,hg⟩
    have heq :
        ((Finset.univ : Finset I).filter
          (fun i => grp i = g)) =
        ((Finset.univ : Finset I).filter
          (fun i => i.1 = z)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hh
        exact Subtype.ext hh
      · intro hh
        exact congrArg Subtype.val hh
    rw [heq]
    exact source_original_c6_sigma_group_slot_count434 G k z
  exact source_original_actual_prime_product_C6_atom_valid434
    G S grp hGrp hDisjoint k hCount a ha
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6SigmaGroupProduct -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The ACTUAL SOURCE03 group-slice product, selected from
the true sigma-indexed ordered labelled prime tuple, equals
the plain ordered product within that group. This is the
necessary exact arithmetic identity to apply the C229
disjoint-group product determination theorem at the original
source C6 group indices. No uniform tuple substitution. -/
theorem source_original_c6_sigma_group_product434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ)
    (a : (Σ h : G, Fin (k h.val)) → ℕ)
    (g : G) :
    (∏ z ∈ (Finset.univ : Finset (Σ h : G, Fin (k h.val))).filter
        (fun z => z.1 = g), a z) =
      ∏ i : Fin (k g.val), a ⟨g,i⟩ := by
  classical
  have hRearrange :
      (∏ z ∈ (Finset.univ : Finset (Σ h : G, Fin (k h.val))).filter
          (fun z => z.1 = g), a z) =
      ∏ z : (Σ h : G, Fin (k h.val)),
        (if z.1 = g then a z else 1) := by
      rw [Finset.prod_filter]
  rw [hRearrange]
  calc
    _ = (∏ h : G, ∏ i : Fin (k h.val),
       (if h = g then a ⟨h,i⟩ else 1)) := by
      exact Fintype.prod_sigma
        (fun z : Σ h : G, Fin (k h.val) =>
          if z.1 = g then a z else 1)
    _ =
      ∏ h : G, (if h = g then (∏ i : Fin (k h.val), a ⟨h,i⟩) else 1) := by
        apply Finset.prod_congr rfl
        intro h hh
        by_cases heq : h = g
        · simp [heq]
        · simp [heq]
    _ = ∏ i : Fin (k g.val), a ⟨g,i⟩ := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6SigmaGroupDetermination -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Genuine original SOURCE03 sigma-indexed GROUP prime-product
uniqueness: two independently labelled prime tuples of type
  ∀(g:G), Fin(k_g)→prime(S_g)
with the SAME full integer product necessarily have the SAME
integer product IN EVERY GROUP g. The only arithmetic input is
pairwise disjoint actual group prime supports; all within-group
prime repetitions are permitted. This is the exact arithmetic
separation required for a product-of-factorials fibre envelope. -/
theorem source_original_c6_sigma_group_product_determined434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (a b : (Σ g : G, Fin (k g.val)) → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S i.1.val)
    (hb : ∀ i, (b i).Prime ∧ b i ∈ S i.1.val)
    (hTotal :
      (∏ i : Σ g : G, Fin (k g.val), a i) =
      (∏ i : Σ g : G, Fin (k g.val), b i))
    (g : G) :
    (∏ i : Fin (k g.val), a ⟨g,i⟩) =
      (∏ i : Fin (k g.val), b ⟨g,i⟩) := by
  classical
  let I := Σ g : G, Fin (k g.val)
  let grp : I → G := fun i => i.1
  let Sg : G → Finset ℕ := fun g => S g.val
  have hDisjoint' :
      ∀ g∈(Finset.univ : Finset G),
      ∀ h∈(Finset.univ : Finset G),
       g ≠ h → Disjoint (Sg g) (Sg h) := by
    intro x hx y hy hne
    exact hDisjoint x.val x.property y.val y.property
      (fun hh => hne (Subtype.ext hh))
  have hGroup :=
    source_original_disjoint_group_product_determined434
      (Finset.univ : Finset G) Sg grp
      (fun _ => Finset.mem_univ _)
      hDisjoint' a b ha hb g (Finset.mem_univ _) hTotal
  have hSelectA := source_original_c6_sigma_group_product434
    G k a g
  have hSelectB := source_original_c6_sigma_group_product434
    G k b g
  exact hSelectA.symm.trans (hGroup.trans hSelectB)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6GroupFibreFactorial -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- SHARP, true SOURCE03 C6 multi-GROUP integer-product FIBRE
envelope: for arbitrary ordered, independently labelled PRIME
draws in each actual group g, the number of physical tuples
with the same overall integer product is at most
       ∏_{g ∈ G} (k_g)!,
NOT (∑_g k_g)!.
This uses genuine distinct-group disjoint prime supports,
within-group factorial fibre counting, and the exact global
product→each group product determination. Repetition inside
one group is explicitly allowed. This removes the
super-polynomial number-of-groups factorial loss that
prevented C217 / C223 Hilbert minor-arc application when
|G| can grow logarithmically with L. -/
theorem source_original_actual_c6_group_fibre_card_le_factorial434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hPrime : ∀ g ∈ G, ∀ p ∈ S g, p.Prime)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (n : ℕ) :
    let X : G → Type := fun g =>
      SourceOriginalGramPrimeTuple434
        (fun _ : Fin (k g.val) => S g.val)
    let F : (g : G) → X g → ℕ := fun g a =>
      sourceOriginalGramPrimeProduct434
        (fun _ : Fin (k g.val) => S g.val) a
    ((Finset.univ : Finset (∀ g : G, X g)).filter
      (fun a => (∏ g : G, F g (a g)) = n)).card ≤
      ∏ g : G, (k g.val).factorial := by
  classical
  let X : G → Type := fun g =>
    SourceOriginalGramPrimeTuple434
      (fun _ : Fin (k g.val) => S g.val)
  let F : (g : G) → X g → ℕ := fun g a =>
    sourceOriginalGramPrimeProduct434
      (fun _ : Fin (k g.val) => S g.val) a
  let T : Finset (∀ g : G, X g) :=
    Finset.univ.filter (fun a => (∏ g : G, F g (a g)) = n)
  let cap : G → ℕ := fun g => (k g.val).factorial
  change T.card ≤ ∏ g : G, cap g
  by_cases hT : T.Nonempty
  · obtain ⟨a0, ha0⟩ := hT
    have hA0 : (∏ g : G, F g (a0 g)) = n :=
      (Finset.mem_filter.mp ha0).2
    let flat : (∀ g : G, X g) →
       (Σ g : G, Fin (k g.val)) → ℕ :=
       fun a z => (a z.1 z.2).val
    have hPrimeFlat (a : ∀ g : G, X g)
        (z : Σ g : G, Fin (k g.val)) :
        (flat a z).Prime ∧ flat a z ∈ S z.1.val :=
      ⟨hPrime z.1.val z.1.property
        (a z.1 z.2).val (a z.1 z.2).property,
       (a z.1 z.2).property⟩
    have hFull (a : ∀ g : G, X g) :
        (∏ z : Σ g : G, Fin (k g.val), flat a z) =
        ∏ g : G, F g (a g) := by
      exact Fintype.prod_sigma
        (fun z : Σ g : G, Fin (k g.val) => flat a z)
    have hFibre (a : ∀ g : G, X g) (ha : a ∈ T)
        (g : G) : F g (a g) = F g (a0 g) := by
      have haN : (∏ g : G, F g (a g)) = n :=
        (Finset.mem_filter.mp ha).2
      have hEq :
          (∏ z : Σ g : G, Fin (k g.val), flat a z) =
          (∏ z : Σ g : G, Fin (k g.val), flat a0 z) := by
        rw [hFull a, hFull a0, haN, hA0]
      have hg :=
        source_original_c6_sigma_group_product_determined434
          G S k hDisjoint (flat a) (flat a0)
          (hPrimeFlat a) (hPrimeFlat a0) hEq g
      exact hg
    have hCap (g : G) :
        ((Finset.univ : Finset (X g)).filter
          (fun x => F g x = F g (a0 g))).card ≤ cap g := by
      have hc := source_original_indexed_prime_fibre_card_le_factorial434
        (fun _ : Fin (k g.val) => S g.val)
        (fun i p hp =>
          hPrime g.val g.property p hp)
        (F g (a0 g))
      simpa only [Fintype.card_fin, cap, F, X] using hc
    exact source_original_finite_independent_fibre_card434
      X F T a0 cap hFibre hCap
  · have heq : T=∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hT
    rw [heq]
    exact Nat.zero_le _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6PhysicalFibreSharp -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT SOURCE03 physical SIGMA-indexed prime-label integer
product fibre bounded by PRODUCT OF PER-GROUP FACTORIALS,
not factorial of all slots. This is the missing quantitative
disjoint-group structure in the physical atom model:
  # {labelled tuples p : ∏_{g,i} p_{g,i}=n}
      <= ∏_{g∈G} (k_g)!.
The selected labels are true independent group-specific
prime draws; same numerical prime may occur repeatedly
INSIDE any group, but supports are pairwise disjoint
BETWEEN groups. The proof uses the authentic dependent
Sigma ↔ Pi-curry equivalence, C237 and C238.
No assumption of a synthetic uniform integer-product law. -/
theorem source_original_c6_physical_group_fibre_sharp434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hPrime : ∀ g ∈ G, ∀ p ∈ S g, p.Prime)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (n : ℕ) :
    let P : (Σ g : G, Fin (k g.val)) → Finset ℕ :=
      fun z => S z.1.val
    ((Finset.univ :
        Finset (SourceOriginalGramPrimeTuple434 P)).filter
        (fun a => sourceOriginalGramPrimeProduct434 P a=n)).card ≤
      ∏ g : G, (k g.val).factorial := by
  classical
  let I := Σ g : G, Fin (k g.val)
  let P : I → Finset ℕ := fun z => S z.1.val
  let X := SourceOriginalGramPrimeTuple434 P
  let Xg : G → Type := fun g =>
    SourceOriginalGramPrimeTuple434
      (fun _ : Fin (k g.val) => S g.val)
  let F : (g : G) → Xg g → ℕ := fun g a =>
    sourceOriginalGramPrimeProduct434
      (fun _ : Fin (k g.val) => S g.val) a
  let E : X ≃ (∀ g : G, Xg g) :=
    Equiv.piCurry
      (fun (g : G) (i : Fin (k g.val)) =>
        {p : ℕ // p∈S g.val})
  let T : Finset X := Finset.univ.filter
    (fun a => sourceOriginalGramPrimeProduct434 P a=n)
  let U : Finset (∀ g : G, Xg g) := Finset.univ.filter
    (fun b => (∏ g : G, F g (b g))=n)
  change T.card ≤ ∏ g : G, (k g.val).factorial
  have hProd (a : X) :
      sourceOriginalGramPrimeProduct434 P a =
      ∏ g : G, F g (E a g) := by
    unfold sourceOriginalGramPrimeProduct434
    exact Fintype.prod_sigma
      (fun z : I => (a z).val)
  have hSubset : T.image E ⊆ U := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    have hProdN :
        sourceOriginalGramPrimeProduct434 P a=n :=
      (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [←hProd]
    exact hProdN
  have hGroupCap : U.card ≤ ∏ g : G, (k g.val).factorial :=
    source_original_actual_c6_group_fibre_card_le_factorial434
      G S k hPrime hDisjoint n
  calc
    _ = T.card := rfl
    _ = (T.image E).card :=
      (Finset.card_image_of_injective T E.injective).symm
    _ ≤ U.card := Finset.card_le_card hSubset
    _ ≤ ∏ g : G, (k g.val).factorial := hGroupCap
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalC6AtomEnvelopeSharp -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The true SOURCE03 sigma-group harmonic normalization
identity. The product over ALL labelled prime slots of
V_group^-1 equals the product over TRUE groups of
V_g^(-k_g). Combined with per-group factorial counts,
this is EXACTLY the C6 sourceProductAtomPrefactor; there
is no super-polynomial factorial(total-slot-count) cost.
No analytical axioms or fabricated group probabilities. -/
theorem source_original_c6_sigma_normalizer_factor434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (V : γ → ℝ) :
    ((∏ g : G, (((k g.val).factorial:ℕ):ℝ)) *
      (∏ z : Σ g : G, Fin (k g.val), (V z.1.val)⁻¹)) =
       Green64SourceC6.sourceProductAtomPrefactor G k V := by
  have hSigma :
      (∏ z : Σ g : G, Fin (k g.val), (V z.1.val)⁻¹) =
      ∏ g : G, ((V g.val)⁻¹)^(k g.val) := by
    calc
      _ = ∏ g : G, ∏ i : Fin (k g.val), (V g.val)⁻¹ := by
        exact Fintype.prod_sigma
          (fun z : Σ g : G, Fin (k g.val) => (V z.1.val)⁻¹)
      _ = _ := by simp
  have hPref :
      (∏ g : G, ((((k g.val).factorial:ℕ):ℝ)/
        (V g.val)^(k g.val))) =
      Green64SourceC6.sourceProductAtomPrefactor G k V := by
    unfold Green64SourceC6.sourceProductAtomPrefactor
    simpa only [Finset.univ_eq_attach] using
      (Finset.prod_attach G
        (fun g => ((((k g).factorial:ℕ):ℝ)/(V g)^(k g))))
  rw [hSigma, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ g : G, ((((k g.val).factorial:ℕ):ℝ)/
        (V g.val)^(k g.val)) := by
      apply Finset.prod_congr rfl
      intro g hg
      rw [div_eq_mul_inv, inv_pow]
    _ = Green64SourceC6.sourceProductAtomPrefactor G k V := hPref
/-- TRUE original SOURCE03 physical harmonic product atom
has the SHARP C6 factorial envelope:
   µ_original(n) <= (1/n)*∏_{g∈G} k_g!/V_g^k_g .
The loss is ∏ k_g! and not (∑ k_g)!, even when the
number of original moving BIG groups grows as O(log L).
All actual independently labelled prime coordinates,
group-specific supports and repeated within-group
prime values are retained. The result uses authentic
pairwise DISJOINT prime supports, and it does not claim
exact equality with synthetic C6 atom mass at this stage.
This DISCHARGES the original C223 per-window atom-envelope
input with rho=sourceProductAtomPrefactor/M at n>=M>0. -/
theorem source_original_c6_physical_atom_sharp_envelope434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hPrime : ∀ g ∈ G, ∀ p ∈ S g, p.Prime)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (hV : ∀ g ∈ G, 0 < V g)
    (n : ℕ) :
    let P : (Σ g : G, Fin (k g.val)) → Finset ℕ :=
      fun z => S z.1.val
    let Vs : (Σ g : G, Fin (k g.val)) → ℝ :=
      fun z => V z.1.val
    sourceOriginalPhysicalProductAtom434 P
      (fun z p => (1/(p:ℝ))/Vs z) n ≤
      (1/(n:ℝ)) *
        Green64SourceC6.sourceProductAtomPrefactor G k V := by
  classical
  let I := Σ g : G, Fin (k g.val)
  let P : I → Finset ℕ := fun z => S z.1.val
  let Vs : I → ℝ := fun z => V z.1.val
  let X := SourceOriginalGramPrimeTuple434 P
  let fibre : Finset X :=
    Finset.univ.filter
      (fun a => sourceOriginalGramPrimeProduct434 P a=n)
  have hCap :
      fibre.card ≤ ∏ g : G, (k g.val).factorial :=
    source_original_c6_physical_group_fibre_sharp434
      G S k hPrime hDisjoint n
  have hReal :
      (fibre.card:ℝ) ≤
      ((∏ g : G, (k g.val).factorial : ℕ):ℝ) := by
    exact_mod_cast hCap
  have hWeightNonneg :
      0 ≤ (1/(n:ℝ))*(∏ z : I, (Vs z)⁻¹) := by
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro z hz
    exact inv_nonneg.mpr (hV z.1.val z.1.property).le
  change sourceOriginalPhysicalProductAtom434 P
      (fun z p => (1/(p:ℝ))/Vs z) n ≤
      (1/(n:ℝ)) *
        Green64SourceC6.sourceProductAtomPrefactor G k V
  rw [source_original_actual_physical_atom_card_formula434]
  calc
    _ ≤ ((∏ g : G, (k g.val).factorial : ℕ):ℝ) *
       ((1/(n:ℝ))*(∏ z : I, (Vs z)⁻¹)) :=
         mul_le_mul_of_nonneg_right hReal hWeightNonneg
    _ = (1/(n:ℝ))*
          (((∏ g : G, (k g.val).factorial : ℕ):ℝ) *
           (∏ z : I, (Vs z)⁻¹)) := by ring
    _ = (1/(n:ℝ))*
         Green64SourceC6.sourceProductAtomPrefactor G k V := by
       have hh := source_original_c6_sigma_normalizer_factor434
         G k V
       simpa only [Nat.cast_prod, I, Vs] using
         congrArg (fun x : ℝ => (1/(n:ℝ))*x) hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalC6AtomInterval -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- On any original C6 integer dyad [M,M+P) with M>0, the
ACTUAL labelled prime-product atom is at most the
TRUE C6 source factorial prefactor divided by M.
No extra physical rho-envelope hypothesis. This is the
precise arithmetic input to the already checked true
physical C223 integer bilinear L² minor-arc inequality. -/
theorem source_original_c6_physical_atom_interval_cap434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (V : γ → ℝ)
    (hPrime : ∀ g ∈ G, ∀ p ∈ S g, p.Prime)
    (hDisjoint : ∀ g∈G, ∀ h∈G, g≠h →
      Disjoint (S g) (S h))
    (hV : ∀ g ∈ G, 0 < V g)
    (M P n : ℕ) (hM : 0 < M)
    (hn : n ∈ Finset.Ico M (M+P)) :
    let Sslot : (Σ g : G, Fin (k g.val)) → Finset ℕ :=
      fun z => S z.1.val
    let Vs : (Σ g : G, Fin (k g.val)) → ℝ :=
      fun z => V z.1.val
    sourceOriginalPhysicalProductAtom434 Sslot
      (fun z p => (1/(p:ℝ))/Vs z) n ≤
      (1/(M:ℝ))*
        Green64SourceC6.sourceProductAtomPrefactor G k V := by
  classical
  let Sslot : (Σ g : G, Fin (k g.val)) → Finset ℕ :=
    fun z => S z.1.val
  let Vs : (Σ g : G, Fin (k g.val)) → ℝ :=
    fun z => V z.1.val
  let pref : ℝ := Green64SourceC6.sourceProductAtomPrefactor G k V
  have hPrefNN : 0 ≤ pref := by
    unfold pref Green64SourceC6.sourceProductAtomPrefactor
    apply Finset.prod_nonneg
    intro g hg
    have hvp : 0 < V g := hV g hg
    exact div_nonneg (by positivity) (pow_nonneg hvp.le _)
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hNM : (M:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hNpos : (0:ℝ) < (n:ℝ) :=
    lt_of_lt_of_le hMpos hNM
  have hInv : (n:ℝ)⁻¹ ≤ (M:ℝ)⁻¹ :=
    (inv_le_inv₀ hNpos hMpos).2 hNM
  have hRaw :=
    source_original_c6_physical_atom_sharp_envelope434
      G S k V hPrime hDisjoint hV n
  change sourceOriginalPhysicalProductAtom434 Sslot
    (fun z p => (1/(p:ℝ))/Vs z) n ≤ (1/(M:ℝ))*pref
  calc
    _ ≤ (1/(n:ℝ))*pref := hRaw
    _ ≤ (1/(M:ℝ))*pref := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using hInv) hPrefNN
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6MinorPhysicalEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE ORIGINAL labelled group-BIG prime laws in the
SOURCE03 two independent primitive blocks satisfy the actual
C6 integer exponential bilinear bound for ARBITRARY
physical complex L² endpoint tests. The integer atom
envelopes rhoA = prefA/M and rhoB = prefB/N are
UNCONDITIONALLY proved from unique prime factorization
and the TRUE per-group factorial cost, not assumed.
No arbitrary test H(p) is fed into prime SW.
This is still an exact C6 arithmetic inequality, not by
itself a completed logarithmic minor-arc saving, which
requires the authentic source03 interval scales. -/
theorem source_original_actual_C6_minor_physical_energy434
    {γA γB : Type} [DecidableEq γA] [DecidableEq γB]
    (GA : Finset γA) (SA : γA → Finset ℕ)
    (kA : γA → ℕ) (VA : γA → ℝ)
    (GB : Finset γB) (SB : γB → Finset ℕ)
    (kB : γB → ℕ) (VB : γB → ℝ)
    (hPrimeA : ∀ g∈GA, ∀ p∈SA g, p.Prime)
    (hPrimeB : ∀ g∈GB, ∀ p∈SB g, p.Prime)
    (hDisjointA : ∀ g∈GA, ∀ h∈GA, g≠h →
        Disjoint (SA g) (SA h))
    (hDisjointB : ∀ g∈GB, ∀ h∈GB, g≠h →
        Disjoint (SB g) (SB h))
    (hVA : ∀ g∈GA, 0 < VA g)
    (hVB : ∀ g∈GB, 0 < VB g)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GA, Fin (kA g.val) => SA z.1.val) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GB, Fin (kB g.val) => SB z.1.val) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
      fun z => SA z.1.val
    let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
      fun z => SB z.1.val
    let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VA z.1.val)
    let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VB z.1.val)
    let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
    let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
    let EA : ℝ := ∑ x : SourceOriginalGramPrimeTuple434 PA,
      sourceOriginalGramPrimeMass434 PA muA x * ‖fA x‖^2
    let EB : ℝ := ∑ y : SourceOriginalGramPrimeTuple434 PB,
      sourceOriginalGramPrimeMass434 PB muB y * ‖fB y‖^2
    ‖(∑ i ∈ Finset.range P,
        sourceOriginalPhysicalProductAtomCoefficient434 PA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 PB muB fB (N+j) *
        Green64SourceC6.integerPhase
          (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ)) ((M+i:ℕ):ℤ)))‖ ≤
      5*Real.sqrt (((1/(M:ℝ))*prefA)*EA)*
         Real.sqrt (((1/(N:ℝ))*prefB)*EB)*
         Real.sqrt ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
          ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := by
  classical
  let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
    fun z => SA z.1.val
  let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
    fun z => SB z.1.val
  let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VA z.1.val)
  let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VB z.1.val)
  let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
  let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
  have hmuA (i : Σ g : GA, Fin (kA g.val))
      (p : ℕ) (hp : p∈PA i) : 0 ≤ muA i p := by
    dsimp [muA]
    exact div_nonneg (by positivity) (hVA i.1.val i.1.property).le
  have hmuB (i : Σ g : GB, Fin (kB g.val))
      (p : ℕ) (hp : p∈PB i) : 0 ≤ muB i p := by
    dsimp [muB]
    exact div_nonneg (by positivity) (hVB i.1.val i.1.property).le
  have hPrefA : 0 ≤ prefA := by
    dsimp [prefA, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVA g hg).le _)
  have hPrefB : 0 ≤ prefB := by
    dsimp [prefB, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVB g hg).le _)
  have hRA : 0 ≤ (1/(M:ℝ))*prefA :=
    mul_nonneg (by positivity) hPrefA
  have hRB : 0 ≤ (1/(N:ℝ))*prefB :=
    mul_nonneg (by positivity) hPrefB
  have hAtomA (n : ℕ) (hn : n∈Finset.Ico M (M+P)) :
      sourceOriginalPhysicalProductAtom434 PA muA n ≤
        (1/(M:ℝ))*prefA := by
    exact source_original_c6_physical_atom_interval_cap434
      GA SA kA VA hPrimeA hDisjointA hVA M P n hM hn
  have hAtomB (n : ℕ) (hn : n∈Finset.Ico N (N+Q)) :
      sourceOriginalPhysicalProductAtom434 PB muB n ≤
        (1/(N:ℝ))*prefB := by
    exact source_original_c6_physical_atom_interval_cap434
      GB SB kB VB hPrimeB hDisjointB hVB N Q n hN hn
  exact source_original_physical_integer_minor_C6_energy434
    PA muA hmuA PB muB hmuB fA fB
    M N P Q a r beta hr hcop hbeta
    ((1/(M:ℝ))*prefA) ((1/(N:ℝ))*prefB)
    hRA hRB hAtomA hAtomB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPositiveSelectedAtom -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Every numerically attainable ORIGINAL integer product of
positively weighted labelled prime tuples has STRICTLY POSITIVE
product-atom mass. In particular the zero-mass branch of the
conditional L2 pushforward never occurs on true source03
prime-band support, even with repeated numerical primes. -/
theorem source_original_physical_product_atom_pos_on_support434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 < mu i p)
    (n : ℕ)
    (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 S) :
    0 < sourceOriginalPhysicalProductAtom434 S mu n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  obtain ⟨a, ha, hProd⟩ := Finset.mem_image.mp hn
  have hA : 0 < w a := by
    unfold w sourceOriginalGramPrimeMass434
    apply Finset.prod_pos
    intro i hi
    exact hmu i (a i).val (a i).property
  have hNonneg (x : X) :
      0 ≤ (if prod x = n then w x else 0) := by
    by_cases hx : prod x=n
    · simp only [if_pos hx]
      unfold w sourceOriginalGramPrimeMass434
      exact (Finset.prod_pos (fun i hi =>
        hmu i (x i).val (x i).property)).le
    · simp [hx]
  have hSingle := Finset.single_le_sum
    (s := (Finset.univ : Finset X))
    (f := fun x : X => if prod x = n then w x else 0)
    (by intro x hx; exact hNonneg x)
    (Finset.mem_univ a)
  have hBound : w a ≤
      ∑ x : X, if prod x=n then w x else 0 := by
    have hp : prod a = n := hProd
    simpa only [if_pos hp] using hSingle
  have hPos := hA.trans_le hBound
  simpa only [sourceOriginalPhysicalProductAtom434, w, prod, X]
    using hPos

/-- SOURCE03 actual group-normalized 1/(p V_g) law has
strictly positive mass on every truly attainable selected
integer-product atom, provided the group support consists
of real primes and the same exact positive normalization V. -/
theorem source_original_true_prime_harmonic_atom_pos434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ)
    (hV : ∀ i, 0 < V i)
    (hPrime : ∀ i p, p ∈ P i → p.Prime)
    (n : ℕ)
    (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 P) :
    0 < sourceOriginalPhysicalProductAtom434 P
      (fun i p => (1/(p:ℝ))/(V i)) n := by
  apply source_original_physical_product_atom_pos_on_support434
    P (fun i p => (1/(p:ℝ))/(V i)) ?_ n hn
  intro i p hp
  have hpp : (0:ℝ) < (p:ℝ) := by
    exact_mod_cast (hPrime i p hp).pos
  exact div_pos (div_pos zero_lt_one hpp) (hV i)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomInverseL2Lift -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine SOURCE03 inverse-atom lift of ANY complex
integer coefficient sequence. It assigns each original
labelled prime tuple the value of its exact product coefficient
divided by the actual harmonic product-atom probability.
No synthetic uniform product measure or exceptional fibre. -/
noncomputable def sourceOriginalPhysicalProductAtomInverseLift434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (a : ℕ → ℂ) (v : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  a (sourceOriginalGramPrimeProduct434 S v) /
    (sourceOriginalPhysicalProductAtom434 S mu
      (sourceOriginalGramPrimeProduct434 S v):ℂ)

/-- Any integer sequence is recovered EXACTLY as the
product-atom coefficient of its original labelled-prime
inverse lift on EVERY attainable atom of the real source03
positive-mass law. This is the missing reverse passage from
arbitrary selected two-integer L2 vectors to the genuine
prime tuple C6 theorem, without supposing product injectivity. -/
theorem source_original_physical_atom_inverse_lift_recovers434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 < mu i p)
    (a : ℕ → ℂ) (n : ℕ)
    (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 S) :
    sourceOriginalPhysicalProductAtomCoefficient434 S mu
      (sourceOriginalPhysicalProductAtomInverseLift434 S mu a) n =
    a n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let mass : ℕ → ℝ := sourceOriginalPhysicalProductAtom434 S mu
  have hp : 0 < mass n :=
    source_original_physical_product_atom_pos_on_support434
      S mu hmu n hn
  have hmne : (mass n:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hCast :
      (∑ v : X, if prod v=n then (w v:ℂ) else 0) = (mass n:ℂ) := by
    have hReal : mass n =
        ∑ v : X, if prod v=n then w v else 0 := rfl
    rw [hReal, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : prod v=n
    · simp [h]
    · simp [h]
  have hTerm (v : X) :
      (if prod v=n then (w v:ℂ)*
        (a (prod v)/(mass (prod v):ℂ)) else 0) =
      (if prod v=n then (w v:ℂ) else 0) *
        (a n/(mass n:ℂ)) := by
    by_cases h : prod v=n
    · simp [h]
    · simp [h]
  change (∑ v : X, if prod v=n then
      (w v:ℂ) * (a (prod v)/(mass (prod v):ℂ)) else 0) = a n
  calc
    _ = ∑ v : X, (if prod v=n then (w v:ℂ) else 0) *
        (a n/(mass n:ℂ)) := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hTerm v
    _ = (∑ v : X, if prod v=n then (w v:ℂ) else 0) *
          (a n/(mass n:ℂ)) := by rw [Finset.sum_mul]
    _ = (mass n:ℂ) * (a n/(mass n:ℂ)) := by rw [hCast]
    _ = a n := by field_simp [hmne]

/-- The inverse-atom lift has EXACTLY the correct physical
weighted L2 energy. There is no cardinality/fibre-factor loss,
and no separate unit-test assumption. All original harmonic
prime tuple weights are preserved. -/
theorem source_original_physical_atom_inverse_lift_energy434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 < mu i p)
    (a : ℕ → ℂ) :
    (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v *
        ‖sourceOriginalPhysicalProductAtomInverseLift434 S mu a v‖^2) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
       ‖a n‖^2 / sourceOriginalPhysicalProductAtom434 S mu n := by
  classical
  let mass : ℕ → ℝ := sourceOriginalPhysicalProductAtom434 S mu
  have hPush :=
    source_original_physical_atom_real_pushforward434
      S mu (fun n => ‖a n/(mass n:ℂ)‖^2)
  change (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v *
        ‖a (sourceOriginalGramPrimeProduct434 S v) /
          (mass (sourceOriginalGramPrimeProduct434 S v):ℂ)‖^2) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      ‖a n‖^2 / mass n
  calc
    _ = ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
          mass n * ‖a n/(mass n:ℂ)‖^2 := hPush
    _ = ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
          ‖a n‖^2 / mass n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hp : 0 < mass n :=
        source_original_physical_product_atom_pos_on_support434
          S mu hmu n hn
      calc
        mass n * ‖a n/(mass n:ℂ)‖^2 =
          mass n * (‖a n‖/mass n)^2 := by
            rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
              abs_of_pos hp]
        _ = ‖a n‖^2 / mass n := by
          field_simp [ne_of_gt hp]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomWindowInverseL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Inverse lift of a genuine selected INTEGER coefficient,
restricted to one ACTUAL C6 product window. This is the
original harmonic labelled-prime law, not a uniform model. -/
noncomputable def sourceOriginalPhysicalProductAtomWindowInverseLift434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (W : Finset ℕ) (a : ℕ → ℂ)
    (v : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  sourceOriginalPhysicalProductAtomInverseLift434 S mu
    (fun n => if n ∈ W then a n else 0) v

/-- TRUE SOURCE03 integer coefficient recovery, WITH the
original dyadic C6 output window W. Nothing is lost at
product atoms containing repeated numerical prime values. -/
theorem source_original_physical_atom_window_inverse_recovers434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 < mu i p)
    (W : Finset ℕ) (a : ℕ → ℂ)
    (n : ℕ)
    (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 S) :
    sourceOriginalPhysicalProductAtomCoefficient434 S mu
      (sourceOriginalPhysicalProductAtomWindowInverseLift434 S mu W a) n =
      if n ∈ W then a n else 0 := by
  classical
  exact source_original_physical_atom_inverse_lift_recovers434
    S mu hmu (fun n => if n ∈ W then a n else 0) n hn

/-- The source03 window inverse lift is an EXACT ISOMETRIC
coefficient embedding for the atom-weighted L2 norm. The
inequality fed to the original C6 minor theorem therefore
incurs NO extraneous factor counting physical prime tuples. -/
theorem source_original_physical_atom_window_inverse_energy434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 < mu i p)
    (W : Finset ℕ) (a : ℕ → ℂ) :
    (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v *
      ‖sourceOriginalPhysicalProductAtomWindowInverseLift434
          S mu W a v‖^2) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      if n ∈ W then
        ‖a n‖^2 / sourceOriginalPhysicalProductAtom434 S mu n
      else 0 := by
  classical
  have hEnergy :=
    source_original_physical_atom_inverse_lift_energy434
      S mu hmu (fun n => if n ∈ W then a n else 0)
  change (∑ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu v *
      ‖sourceOriginalPhysicalProductAtomWindowInverseLift434
          S mu W a v‖^2) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      ‖(if n ∈ W then a n else 0)‖^2 /
        sourceOriginalPhysicalProductAtom434 S mu n at hEnergy
  calc
    _ = ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      ‖(if n ∈ W then a n else 0)‖^2 /
        sourceOriginalPhysicalProductAtom434 S mu n := hEnergy
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : n ∈ W
      · simp [h]
      · simp [h]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalMatchedAtomOperator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- SOURCE03 original physical full-free-mark weighted L2
operator from the TRUE joint two-integer selected product C6
bound, with EXACT B-source/A-target atomic harmonic masses.
The newly verified physical ν marginal identities show that
every selected product mass is exactly the true full-free-mark
fibre mass; the generic matched-mass conditional L2 theorem
then preserves arbitrary COMPLEX mark-sensitive endpoint tests
and JOINT coupled H(B,A), with no fibre-count/cardinality loss.
Arithmetic C6 saving is the explicit selected-kernel premise. -/
theorem source_original_true_physical_matched_atom_operator434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (hPrime : ∀ g, ∀ p ∈ P g, p.Prime)
    (H : ℕ → ℕ → ℂ)
    (budget : ℝ) (hBudget : 0 ≤ budget) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let muB : ν.2 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let muA : ν.1 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)
    (∀ a b : ℕ → ℂ,
      ‖(∑ ij ∈ TB.product TA,
        a ij.1*b ij.2*H ij.1 ij.2)‖^2 ≤
      budget *
        (∑ n ∈ TB,
          ‖a n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n) *
        (∑ n ∈ TA,
          ‖b n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n)) →
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        H (projS ab.1) (projT ab.2))‖^2 ≤
      budget*(∑ s : X, w s*‖sourceTest s‖^2) *
             (∑ v : X, w v*‖targetTest v‖^2) := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let muB : ν.2 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let muA : ν.1 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val)
  intro hSelected sourceTest targetTest
  have hCoverS (s : X) : projS s ∈ TB :=
    source_original_true_source_B_product_atom_supported434
      J ell m hmJ ν P s
  have hCoverT (v : X) : projT v ∈ TA :=
    source_original_true_target_A_product_atom_supported434
      J ell m hmJ ν P v
  have hW (s : X) : 0 ≤ w s := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun q : BP g => prime g q) (V g) (hVpos g) p
  have hMargS (n : ℕ) (hn : n ∈ TB) :
      (∑ s : X, if projS s=n then w s else 0) =
      sourceOriginalPhysicalProductAtom434 SB muB n := by
    exact source_original_true_source_B_physical_atom_marginal434
      J ell m hmJ ν P V hV hVpos n
  have hMargT (n : ℕ) (hn : n ∈ TA) :
      (∑ v : X, if projT v=n then w v else 0) =
      sourceOriginalPhysicalProductAtom434 SA muA n := by
    exact source_original_true_target_A_physical_atom_marginal434
      J ell m hmJ ν P V hV hVpos n
  have hPosS (n : ℕ) (hn : n ∈ TB) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n :=
    source_original_true_prime_harmonic_atom_pos434
      SB (fun z : ν.2 => V z.val.1)
      (fun z => hVpos z.val.1)
      (fun z p hp => hPrime z.val.1 p hp) n hn
  have hPosT (n : ℕ) (hn : n ∈ TA) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n :=
    source_original_true_prime_harmonic_atom_pos434
      SA (fun z : ν.1 => V z.val.1)
      (fun z => hVpos z.val.1)
      (fun z p hp => hPrime z.val.1 p hp) n hn
  exact source_original_finite_matched_mass_operator_upgrade434
    TB TA projS projT hCoverS hCoverT
    w w hW hW
    (sourceOriginalPhysicalProductAtom434 SB muB)
    (sourceOriginalPhysicalProductAtom434 SA muA)
    hMargS hMargT hPosS hPosT
    H budget hBudget hSelected sourceTest targetTest
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6DyadicSpectralRatio -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The EXACT C6 integer bilinear norm factor on TRUE dyadic
windows P≤M, Q≤N has the sharp expected large-denominator
spectral saving 1/r plus explicit boundary remainders:
  T/(MN) ≤ 1/r + 2/N + log(2r)/M + r log(2r)/(MN).
No factor depending on prime atom support count.
This is unconditional elementary algebra under the original
integer dyadic-size hypotheses; it does not assume the
target log-power saving as a premise. -/
theorem source_original_c6_dyadic_spectral_ratio434
    (M N P Q r : ℕ)
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hP : P ≤ M) (hQ : Q ≤ N) :
    let logR : ℝ := Real.log (2*(r:ℝ))
    let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
      ((P:ℝ)+(r:ℝ)*logR)
    T / ((M:ℝ)*(N:ℝ)) ≤
      1/(r:ℝ) + 2/(N:ℝ) +
        logR/(M:ℝ) +
        (r:ℝ)*logR/((M:ℝ)*(N:ℝ)) := by
  let mr : ℝ := M
  let nr : ℝ := N
  let pr : ℝ := P
  let qr : ℝ := Q
  let rr : ℝ := r
  let lr : ℝ := Real.log (2*rr)
  let T : ℝ := pr+(1+qr/rr)*(pr+rr*lr)
  have hmp : 0 < mr := by simpa only [mr] using (by exact_mod_cast hM : (0:ℝ) < (M:ℝ))
  have hnp : 0 < nr := by simpa only [nr] using (by exact_mod_cast hN : (0:ℝ) < (N:ℝ))
  have hrp : 0 < rr := by simpa only [rr] using (by exact_mod_cast hr : (0:ℝ) < (r:ℝ))
  have hpr : 0 ≤ pr := Nat.cast_nonneg _
  have hqr : 0 ≤ qr := Nat.cast_nonneg _
  have hpm : pr ≤ mr := by simpa only [pr,mr] using (by exact_mod_cast hP : (P:ℝ) ≤ (M:ℝ))
  have hqn : qr ≤ nr := by simpa only [qr,nr] using (by exact_mod_cast hQ : (Q:ℝ) ≤ (N:ℝ))
  have hrl : (1:ℝ) ≤ rr := by
    have hNat : 1 ≤ r := by omega
    simpa only [rr] using (by exact_mod_cast hNat : (1:ℝ) ≤ (r:ℝ))
  have hlr : 0 ≤ lr := by
    dsimp [lr]
    apply Real.log_nonneg
    nlinarith
  have hdiv : 0 ≤ qr/rr := div_nonneg hqr hrp.le
  have hQR : qr/rr ≤ nr/rr :=
    div_le_div_of_nonneg_right hqn hrp.le
  have hPr : (qr/rr)*pr ≤ (nr/rr)*mr := by
    exact mul_le_mul hQR hpm hpr (div_nonneg (Nat.cast_nonneg _) hrp.le)
  have hLog : qr*lr ≤ nr*lr :=
    mul_le_mul_of_nonneg_right hqn hlr
  have hT :
      T ≤ 2*mr+(mr*nr)/rr+(rr+nr)*lr := by
    dsimp [T]
    have hExact :
        pr+(1+qr/rr)*(pr+rr*lr) =
        2*pr+(qr/rr)*pr+rr*lr+qr*lr := by
      field_simp
      ring
    rw [hExact]
    have hExpr : (nr/rr)*mr = (mr*nr)/rr := by ring
    rw [← hExpr]
    nlinarith [hPr,hLog]
  have hmnp : 0 < mr*nr := mul_pos hmp hnp
  have hRatio :
      T/(mr*nr) ≤
        (2*mr+(mr*nr)/rr+(rr+nr)*lr)/(mr*nr) :=
    div_le_div_of_nonneg_right hT hmnp.le
  have hExpr :
      (2*mr+(mr*nr)/rr+(rr+nr)*lr)/(mr*nr) =
        1/rr + 2/nr + lr/mr + rr*lr/(mr*nr) := by
    field_simp
    ring
  change T/(mr*nr) ≤
    1/rr + 2/nr + lr/mr + rr*lr/(mr*nr)
  exact hRatio.trans (le_of_eq hExpr)
end Green64Analytic.CorrelationSquare

end

