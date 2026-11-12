module

public import Green64.Library.Correlation.Part054
public import Mathlib.Data.Nat.Factors
public import Green64.Library.Weights.Part073
public import Green64.Library.Weights.Part071
public import Mathlib.Data.Multiset.Filter
public import Green64.Library.Weights.Part075
public import Green64.Library.Weights.Part070
public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part072

@[expose] public section

/-!
# Correlation / Part055

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSource03PhysicalBIGPrimeMultiset -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Arithmetic uniqueness of a MULTISET of genuine primes, even
with arbitrary repetitions: a product collision is precisely a
prime multiset collision, not a fictitious path uniqueness claim. -/
theorem source_original_TRUE_prime_multiset_prod_injective434
    (a b : Multiset ℕ)
    (ha : ∀ q ∈ a, q.Prime) (hb : ∀ q ∈ b, q.Prime) :
    a.prod = b.prod ↔ a = b := by
  constructor
  · intro h
    have hpa : a.toList.Perm (a.prod).primeFactorsList :=
      Nat.primeFactorsList_unique (Multiset.prod_toList a)
        (by intro q hq; exact ha q (Multiset.mem_toList.mp hq))
    have hpb : b.toList.Perm (b.prod).primeFactorsList :=
      Nat.primeFactorsList_unique (Multiset.prod_toList b)
        (by intro q hq; exact hb q (Multiset.mem_toList.mp hq))
    have hperm : a.toList.Perm b.toList := by
      rw [h] at hpa
      exact hpa.trans hpb.symm
    have hms : (a.toList : Multiset ℕ) = b.toList :=
      Multiset.coe_eq_coe.mpr hperm
    simpa only [Multiset.coe_toList] using hms
  · rintro rfl
    rfl

/-- The complete ACTUAL canonical physical source BIG prime multiset:
all permuted shared BIG endpoint labels and ALL auxiliary free
draws, with multiplicity and with original source-pattern slots.
No independent product atom or positivity envelope. -/
noncomputable def sourceOriginalSource03PhysicalBIGPrimeMultiset434
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
      (fun _ p => p.val) J ell m cap patterns x) : Multiset ℕ :=
  ∑ g : Fin n, (
    Multiset.map (fun i =>
      ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val)
      (sourceBigShared J ell m (patterns ch.1) g).val +
    Multiset.map (fun j : ↥((patterns ch.1).free g) =>
      (ch.2.1 g j).val)
      (Finset.univ : Finset ↥((patterns ch.1).free g)).val)

/-- EXACT product identity of genuine BIG source labels, preserving
all repeated labels and the same original state/pattern/auxiliary. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_multiset_product434
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
      (fun _ p => p.val) J ell m cap patterns x) :
    (sourceOriginalSource03PhysicalBIGPrimeMultiset434
      z J ell m cap patterns x ch).prod =
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch := by
  unfold sourceOriginalSource03PhysicalBIGPrimeMultiset434
    sourceOriginalSource03CanonicalPhysicalBIGFactor434
  rw [Multiset.prod_sum]
  apply Finset.prod_congr rfl
  intro g hg
  rw [Multiset.prod_add]
  congr 1

/-- Every member of the ACTUAL BIG source multiset is a genuine
canonical prime from the corresponding source03 Tb interval. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_multiset_all_prime434
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
      (fun _ p => p.val) J ell m cap patterns x) :
    ∀ q ∈ sourceOriginalSource03PhysicalBIGPrimeMultiset434
      z J ell m cap patterns x ch, q.Prime := by
  intro q hq
  unfold sourceOriginalSource03PhysicalBIGPrimeMultiset434 at hq
  obtain ⟨g,hg,hgq⟩ := Multiset.mem_sum.mp hq
  rcases Multiset.mem_add.mp hgq with ha | hb
  · obtain ⟨i,hi,hEq⟩ := Multiset.mem_map.mp ha
    have hp := (z.hBigBand g
      ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val
      ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).property).1
    simpa only [← hEq] using hp
  · obtain ⟨j,hj,hEq⟩ := Multiset.mem_map.mp hb
    have hp := (z.hBigBand g (ch.2.1 g j).val
      (ch.2.1 g j).property).1
    simpa only [← hEq] using hp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGPrimeCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3800000

/-- Two ORIGINAL source03 physical BIG products agree precisely
when their genuine multisets of prime labels (all physical shared
and auxiliary slots, retaining arbitrary multiplicity) coincide.
No prime labels, Fock paths or source choices are assumed unique. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_BIG_product_iff_prime_multiset434
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
      (fun _ p => p.val) J ell m cap patterns x) :
    (sourceOriginalSource03CanonicalPhysicalBIGFactor434
       z J ell m cap patterns x ch =
     sourceOriginalSource03CanonicalPhysicalBIGFactor434
       z J ell m cap patterns x ch') ↔
    (sourceOriginalSource03PhysicalBIGPrimeMultiset434
       z J ell m cap patterns x ch =
     sourceOriginalSource03PhysicalBIGPrimeMultiset434
       z J ell m cap patterns x ch') := by
  have hA := source_original_TRUE_source03_PHYSICAL_BIG_multiset_product434
    z J ell m cap patterns x ch
  have hB := source_original_TRUE_source03_PHYSICAL_BIG_multiset_product434
    z J ell m cap patterns x ch'
  have hPA := source_original_TRUE_source03_PHYSICAL_BIG_multiset_all_prime434
    z J ell m cap patterns x ch
  have hPB := source_original_TRUE_source03_PHYSICAL_BIG_multiset_all_prime434
    z J ell m cap patterns x ch'
  rw [←hA, ←hB]
  exact source_original_TRUE_prime_multiset_prod_injective434
    _ _ hPA hPB

/-- New FULL source03 large-L characterization: same-fibre BIG
modular collisions correspond exactly to true prime MULTISETS.
No extra numerical, cardinality or source independence premise:
the eventual bound uses the actual Chebyshev prime geometry. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_mod_BIG_iff_multiset434
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
         z J ell m cap patterns x ch:ℕ):ZMod Q) =
      ((sourceOriginalSource03CanonicalPhysicalBIGFactor434
         z J ell m cap patterns x ch':ℕ):ZMod Q) ↔
      sourceOriginalSource03PhysicalBIGPrimeMultiset434
         z J ell m cap patterns x ch =
      sourceOriginalSource03PhysicalBIGPrimeMultiset434
         z J ell m cap patterns x ch' := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_PHYSICAL_BIG_collision_iff_integer434
      cfg J ell m] with L hL
  intro n d vmax c0 z hd cap Nu _ patterns x ch ch' hSame
  dsimp only
  exact (hL n d vmax c0 z hd cap patterns x ch ch' hSame).trans
    (source_original_TRUE_SOURCE03_PHYSICAL_BIG_product_iff_prime_multiset434
      z J ell m cap patterns x ch ch')
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ExactPrimeFiberGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Exact coherent Gram grouping by ACTUAL prime multiset,
without falsely asserting path uniqueness or discarding
off-diagonal coherent collisions INSIDE a prime-multiset fibre.
This finite theorem holds for arbitrary COMPLEX signed weights. -/
theorem source_original_TRUE_prime_multiset_fiber_Gram434
    {I K : Type} [DecidableEq I] [DecidableEq K]
    (F : Finset I) (key : I → K) (w : I → ℂ) :
    (∑ i ∈ F, ∑ j ∈ F,
      if key i = key j then star (w i) * w j else 0) =
    ∑ v ∈ F.image key,
      (star (∑ i ∈ F.filter (fun i => key i = v), w i)) *
      (∑ j ∈ F.filter (fun j => key j = v), w j) := by
  classical
  let T := F.image key
  have hmap : ∀ i ∈ F, key i ∈ T :=
    fun i hi => Finset.mem_image_of_mem key hi
  calc
    (∑ i ∈ F, ∑ j ∈ F,
      if key i = key j then star (w i) * w j else 0) =
      ∑ v ∈ T, ∑ i ∈ F.filter (fun i => key i = v),
        ∑ j ∈ F, if key i = key j then star (w i) * w j else 0 := by
      exact (Finset.sum_fiberwise_of_maps_to hmap
        (fun i => ∑ j ∈ F,
           if key i = key j then star (w i) * w j else 0)).symm

    _ = ∑ v ∈ T, ∑ i ∈ F.filter (fun i => key i = v),
          ∑ j ∈ F.filter (fun j => key j = v),
             star (w i) * w j := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro i hi
      have hEq : key i = v := (Finset.mem_filter.mp hi).2
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjv : key j = v
      · simp [hEq,hjv]
      · have hbad : v ≠ key j := Ne.symm hjv
        simp [hEq, hjv, hbad]
    _ = ∑ v ∈ T,
        (star (∑ i ∈ F.filter (fun i => key i = v), w i)) *
        (∑ j ∈ F.filter (fun j => key j = v), w j) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [star_sum, Finset.sum_mul_sum]
  done
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CoherentPrimeFiber -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The actual finite complex equality-collision Gram splits into
NONNEGATIVE coherent fibre energies. Importantly, the SQUARE
remains INSIDE each prime-multiset fibre, retaining all
same-multiset path interference. -/
theorem source_original_TRUE_prime_multiset_coherent_fiber_energy434
    {I K : Type} [DecidableEq I] [DecidableEq K]
    (F : Finset I) (key : I → K) (w : I → ℂ) :
    (∑ i ∈ F, ∑ j ∈ F,
      if key i = key j then star (w i) * w j else 0) =
    ∑ v ∈ F.image key,
      (((‖∑ i ∈ F.filter (fun i => key i = v), w i‖ ^ 2 : ℝ)) : ℂ) := by
  rw [source_original_TRUE_prime_multiset_fiber_Gram434]
  apply Finset.sum_congr rfl
  intro v hv
  have hn (z : ℂ) : (((‖z‖^2 : ℝ)) : ℂ) = star z * z := by
    calc
      _ = z * star z := by
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.mul_conj z).symm
      _ = _ := mul_comm _ _
  exact (hn _).symm

/-- Every actual prime-multiset fibre energy is nonnegative.
No TV envelope is taken: the nonnegative expression arises
AFTER the exact coherent sum over matched original amplitudes. -/
theorem source_original_TRUE_prime_multiset_coherent_fiber_energy_nonneg434
    {I K : Type} [DecidableEq I] [DecidableEq K]
    (F : Finset I) (key : I → K) (w : I → ℂ) :
    0 ≤ ∑ v ∈ F.image key,
      (‖∑ i ∈ F.filter (fun i => key i = v), w i‖ ^ 2 : ℝ) := by
  exact Finset.sum_nonneg (fun v hv => sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeCoherentGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The COMPLETE TRUE original moving source03 first-DIRTY
signed Fock×seen Fourier Gram has an EXACT nonnegative coherent
fibre-energy decomposition indexed by the RELATIVE S+Ts torus
displacement. NO equal-initial or equal-terminal state assumption
and NO character averaging. A square is taken only AFTER all
complex RAW/comparison/K-weighted amplitudes inside a fibre
interfere coherently, retaining every chronological state and
all first-DIRTY insertion positions. No logarithmic saving. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_full_relative_coherent_gram434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (freq : ℤ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    let key : Paths → _ := sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R
    let Amp : Paths → ℂ := fun path =>
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T path freq
    (((‖P.coeff freq‖^2 : ℝ)) : ℂ) =
      (((‖Base‖^2 : ℝ)) : ℂ) *
        ∑ rel ∈ (Finset.univ : Finset Paths).image key,
          (((‖∑ path ∈ (Finset.univ : Finset Paths).filter
            (fun path => key path = rel), Amp path‖^2 : ℝ)) : ℂ) := by
  classical
  dsimp only
  let P := sourceOriginalActualSourceDIRTYLaurentRoot434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
  let Base : ℂ := physicalSourceBaselineProduct
    (fun g : β => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R)
  let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
    (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
  let key : Paths → _ := sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R
  let Amp : Paths → ℂ := fun path =>
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq
  have hroot : (((‖P.coeff freq‖^2 : ℝ)) : ℂ) =
      (((‖Base‖^2 : ℝ)) : ℂ) *
        ∑ path : Paths, ∑ other : Paths,
          star (Amp path) * Amp other := by
    exact source_original_ACTUAL_SOURCE_DIRTY_true_path_collision_gram434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T freq
  have hzero (p q : Paths) (hne : key p ≠ key q) :
      star (Amp p)*Amp q = 0 := by
    by_cases ha : Amp p = 0
    · simp [ha]
    · by_cases hb : Amp q = 0
      · simp [hb]
      · have hEq :=
          source_original_ACTUAL_SOURCE_DIRTY_equal_frequency_relative_eq434
            u blockA blockB J ell m hmJ Q hA hB
            xi rho zeta k R T p q freq ha hb
        exact (hne hEq).elim
  have hfilter :
      (∑ p : Paths, ∑ q : Paths, star (Amp p)*Amp q) =
      (∑ p : Paths, ∑ q : Paths,
        if key p=key q then star (Amp p)*Amp q else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases he : key p = key q
    · simp [he]
    · simp only [if_neg he]
      exact hzero p q he
  have hfibre :
      (∑ p : Paths, ∑ q : Paths,
        if key p=key q then star (Amp p)*Amp q else 0) =
      ∑ rel ∈ (Finset.univ : Finset Paths).image key,
        (((‖∑ path ∈ (Finset.univ : Finset Paths).filter
          (fun path => key path = rel), Amp path‖^2 : ℝ)) : ℂ) :=
    source_original_TRUE_prime_multiset_coherent_fiber_energy434
      (Finset.univ : Finset Paths) key Amp
  calc
    (((‖P.coeff freq‖^2 : ℝ)) : ℂ) =
        (((‖Base‖^2 : ℝ)) : ℂ) *
          ∑ path : Paths, ∑ other : Paths,
            star (Amp path)*Amp other := hroot
    _ = (((‖Base‖^2 : ℝ)) : ℂ) *
        ∑ p : Paths, ∑ q : Paths,
          if key p=key q then star (Amp p)*Amp q else 0 := by rw [hfilter]
    _ = _ := by rw [hfibre]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGPrimeFiberSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- The FULL canonical true source03 BIG-product integer collision
Gram is EXACTLY the coherent sum of squared COMPLEX amplitudes,
grouped by genuine prime MULTISETS. This identity does not drop
permutations, auxiliary repeats or joint original K weights. -/
theorem source_original_TRUE_SOURCE03_PHYSICAL_BIG_prime_fiber_sum434
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
    (F : Finset (FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x))

    (w : (FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) → ℂ) :
    let B := fun ch => sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch
    let M := fun ch => sourceOriginalSource03PhysicalBIGPrimeMultiset434
      z J ell m cap patterns x ch
    (∑ ch ∈ F, ∑ ch' ∈ F,
      if B ch = B ch' then star (w ch) * w ch' else 0) =
    ∑ v ∈ F.image M,
      (((‖∑ ch ∈ F.filter (fun ch => M ch = v), w ch‖ ^ 2 : ℝ)):ℂ) := by
  dsimp only
  calc
    _ = ∑ ch ∈ F, ∑ ch' ∈ F,
      if sourceOriginalSource03PhysicalBIGPrimeMultiset434
          z J ell m cap patterns x ch =
        sourceOriginalSource03PhysicalBIGPrimeMultiset434
          z J ell m cap patterns x ch'
      then star (w ch) * w ch' else 0 := by
      apply Finset.sum_congr rfl
      intro ch hch
      apply Finset.sum_congr rfl
      intro ch' hch'
      have heq := source_original_TRUE_SOURCE03_PHYSICAL_BIG_product_iff_prime_multiset434
        z J ell m cap patterns x ch ch'
      simp only [heq]
    _ = _ := source_original_TRUE_prime_multiset_coherent_fiber_energy434
      F (fun ch => sourceOriginalSource03PhysicalBIGPrimeMultiset434
          z J ell m cap patterns x ch) w
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TruePhysicalPrimeFiberGram -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- At every sufficiently large TRUE source03 scale, the genuine
oriented physical E-character second moment with its complete
original joint signed Knu and arbitrary terminal Fock observable
is the TOTIENT times a coherent sum of prime-multiset fibre ENERGIES.
The complex signed weight is summed BEFORE squaring in each fibre.

This is a one-physical-E-step/fixed-source-state/fixed shared-SMALL
sector identity; it does NOT prove the entire chronological
first-DIRTY Fock x seen correlation or logarithmic saving. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_prime_fiber_energy434
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
        let M : FullOrientedSourceChoice
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x → Multiset ℕ := fun ch =>
          sourceOriginalSource03PhysicalBIGPrimeMultiset434
            z J ell m cap patterns x ch
        (∑ χ : DirichletCharacter ℂ Q,
          ∑ ch ∈ F, ∑ ch' ∈ F,
            (star (w ch)*w ch') *
              (χ ((v ch)⁻¹)*χ (v ch'))) =
        (Q.totient : ℂ) *
          (∑ ms ∈ F.image M,
            (((‖∑ ch ∈ F.filter (fun ch => M ch = ms),
                w ch‖^2 : ℝ)):ℂ)) := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_PHYSICAL_INTEGER_BIG_Gram434
      cfg J ell m] with L hGram
  intro n d vmax c0 z hd cap Nu _ patterns x q rho Vs Vb mu Knu
    zeta theta o k ho hk hK hOrigSmall future s
  have h := hGram n d vmax c0 z hd cap patterns x
    q rho Vs Vb mu Knu zeta theta o k ho hk hK hOrigSmall future s
  dsimp only at h ⊢
  rw [h]
  congr 1
  exact source_original_TRUE_SOURCE03_PHYSICAL_BIG_prime_fiber_sum434
    z J ell m cap patterns x
    (sourceOriginalPhysicalSameSharedChoices434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k s)
    (sourceOriginalPhysicalFutureWeight434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k x future)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03BIGGroupMultiset -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Filtering any finite multiset sum distributes over its summands.
In particular, repeated genuine BIG prime labels remain repeated. -/
theorem source_original_prime_multiset_filter_finset_sum434
    {I : Type} [DecidableEq I] (s : Finset I)
    (m : I → Multiset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Multiset.filter P (∑ i ∈ s, m i) =
      ∑ i ∈ s, Multiset.filter P (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Multiset.filter_add, ih]
/-- A family of genuine prime multisets on disjoint prime bands
can be exactly recovered from their total sum by filtering on
one band, including prime multiplicities. -/
theorem source_original_prime_multiset_disjoint_band_extract434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (m : I → Multiset ℕ)
    (hmem : ∀ i q, q ∈ m i → q ∈ P i) (i : I) :
    Multiset.filter (fun q => q ∈ P i) (∑ j : I, m j) = m i := by
  classical
  calc
    Multiset.filter (fun q => q ∈ P i) (∑ j : I, m j) =
        ∑ j : I, Multiset.filter (fun q => q ∈ P i) (m j) := by
      simpa only using (source_original_prime_multiset_filter_finset_sum434
        (Finset.univ : Finset I) m (fun q => q ∈ P i))
    _ =
        Multiset.filter (fun q => q ∈ P i) (m i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        apply Multiset.filter_eq_nil.mpr
        intro q hq
        exact (Finset.disjoint_left.mp (hdis j i hji))
          (hmem j q hq)
      · simp
    _ = m i := Multiset.filter_eq_self.mpr
      (fun q hq => hmem i q hq)
/-- Exactly the physical BIG multiset in ONE genuine Tb group:
permuted shared BIG endpoint slots and independent auxiliary
draws. There is no claim of independence of weights or paths. -/
noncomputable def sourceOriginalSource03PhysicalBIGGroupMultiset434
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
    (g : Fin n) : Multiset ℕ :=
    Multiset.map (fun i =>
      ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val)
      (sourceBigShared J ell m (patterns ch.1) g).val +
    Multiset.map (fun j : ↥((patterns ch.1).free g) =>
      (ch.2.1 g j).val)
      (Finset.univ : Finset ↥((patterns ch.1).free g)).val
/-- Every element of the *individual-group* original physical
BIG multiset is an actual prime in the SAME canonical Tb interval. -/
theorem source_original_TRUE_source03_physical_BIG_group_mem_Tb434
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
    (g : Fin n) (q : ℕ)
    (hq : q ∈ sourceOriginalSource03PhysicalBIGGroupMultiset434
      z J ell m cap patterns x ch g) :
    q ∈ z.Tb g := by
  unfold sourceOriginalSource03PhysicalBIGGroupMultiset434 at hq
  rcases Multiset.mem_add.mp hq with ha | hb
  · obtain ⟨i, hi, hEq⟩ := Multiset.mem_map.mp ha
    simpa only [← hEq] using
      ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).property
  · obtain ⟨j, hj, hEq⟩ := Multiset.mem_map.mp hb
    simpa only [← hEq] using (ch.2.1 g j).property
/-- The complete real physical BIG multiset is the sum of all
true, disjoint, groupwise physical prime multisets. -/
theorem source_original_TRUE_source03_BIG_group_multiset_sum434
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
      (fun _ p => p.val) J ell m cap patterns x) :
    sourceOriginalSource03PhysicalBIGPrimeMultiset434
       z J ell m cap patterns x ch =
      ∑ g : Fin n, sourceOriginalSource03PhysicalBIGGroupMultiset434
        z J ell m cap patterns x ch g := by
  rfl
/-- The genuine physical BIG prime multiset in ANY chosen Tb
group is EXACTLY the corresponding band filter of the original
FULL source BIG multiset. This uses TRUE Tb disjointness. -/
theorem source_original_TRUE_source03_physical_BIG_group_filter434
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
    (g : Fin n) :
    Multiset.filter (fun q => q ∈ z.Tb g)
      (sourceOriginalSource03PhysicalBIGPrimeMultiset434
        z J ell m cap patterns x ch) =
    sourceOriginalSource03PhysicalBIGGroupMultiset434
       z J ell m cap patterns x ch g := by
  rw [source_original_TRUE_source03_BIG_group_multiset_sum434]
  exact source_original_prime_multiset_disjoint_band_extract434
    z.Tb z.hBB
    (fun i => sourceOriginalSource03PhysicalBIGGroupMultiset434
       z J ell m cap patterns x ch i)
    (fun i q hq => source_original_TRUE_source03_physical_BIG_group_mem_Tb434
      z J ell m cap patterns x ch i q hq) g
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03BIGGroupCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- A genuine physical FULL source03 BIG prime multiset agrees
between two choices IFF every actual source03 Tb-group multiset
agrees separately. The proof uses z.hBB, which is true physical
prime-band disjointness; it never assumes BIG group independence,
unique paths, or distinct auxiliary labels. -/
theorem source_original_TRUE_source03_physical_BIG_group_collision_iff434
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
      (fun _ p => p.val) J ell m cap patterns x) :
    (sourceOriginalSource03PhysicalBIGPrimeMultiset434
      z J ell m cap patterns x ch =
     sourceOriginalSource03PhysicalBIGPrimeMultiset434
      z J ell m cap patterns x ch') ↔
    (∀ g : Fin n,
      sourceOriginalSource03PhysicalBIGGroupMultiset434
        z J ell m cap patterns x ch g =
      sourceOriginalSource03PhysicalBIGGroupMultiset434
        z J ell m cap patterns x ch' g) := by
  constructor
  · intro h g
    calc
      sourceOriginalSource03PhysicalBIGGroupMultiset434
          z J ell m cap patterns x ch g =
          Multiset.filter (fun q => q ∈ z.Tb g)
            (sourceOriginalSource03PhysicalBIGPrimeMultiset434
              z J ell m cap patterns x ch) :=
        (source_original_TRUE_source03_physical_BIG_group_filter434
          z J ell m cap patterns x ch g).symm
      _ = Multiset.filter (fun q => q ∈ z.Tb g)
            (sourceOriginalSource03PhysicalBIGPrimeMultiset434
              z J ell m cap patterns x ch') := by
        rw [h]
      _ = sourceOriginalSource03PhysicalBIGGroupMultiset434
          z J ell m cap patterns x ch' g :=
        source_original_TRUE_source03_physical_BIG_group_filter434
          z J ell m cap patterns x ch' g
  · intro h
    rw [source_original_TRUE_source03_BIG_group_multiset_sum434
        z J ell m cap patterns x ch,
      source_original_TRUE_source03_BIG_group_multiset_sum434
        z J ell m cap patterns x ch']
    apply Finset.sum_congr rfl
    intro g hg
    exact h g
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGAuxAvoidance -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4600000

/-- Original input BIG endpoint prime values, a fixed finite set
at the ACTUAL source physical state x (no new probability model). -/
noncomputable def sourceOriginalSource03BIGInputPrimeSet434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (J ell : ℕ) (cap : Fin n → ℕ)
    (x : FullPhysicalState
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) (J+ell) cap)
    (g : Fin n) : Finset ℕ :=
  (Finset.univ : Finset (Fin (J+ell))).image
    (fun i => ((x.2 g).1 i).val)
/-- The exact permuted shared BIG prime multiset of one
true source03 group. Shared marks originate in the actual
input endpoint's BIG slots, respecting source pattern C_g. -/
noncomputable def sourceOriginalSource03PhysicalBIGSharedMultiset434
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
    (g : Fin n) : Multiset ℕ :=
  Multiset.map (fun i =>
    ((x.2 g).1 (ch.2.2.1.sigmaBig g i)).val)
    (sourceBigShared J ell m (patterns ch.1) g).val
/-- Exact SOURCE independent auxiliary BIG prime multiset in the
same TRUE physical group; repeated auxiliary draws are retained. -/
noncomputable def sourceOriginalSource03PhysicalBIGAuxMultiset434
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
    (g : Fin n) : Multiset ℕ :=
  Multiset.map (fun j : ↥((patterns ch.1).free g) =>
    (ch.2.1 g j).val)
    (Finset.univ : Finset ↥((patterns ch.1).free g)).val

/-- REAL physical shared+auxiliary multisets combine exactly. -/
theorem source_original_TRUE_source03_BIG_group_shared_aux_exact434
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
    (g : Fin n) :
    sourceOriginalSource03PhysicalBIGGroupMultiset434
       z J ell m cap patterns x ch g =
    sourceOriginalSource03PhysicalBIGSharedMultiset434
       z J ell m cap patterns x ch g +
    sourceOriginalSource03PhysicalBIGAuxMultiset434
       z J ell m cap patterns x ch g := by
  rfl
/-- Every REAL shared BIG source prime in one group comes from an
ACTUAL permuted input endpoint slot of that group. -/
theorem source_original_TRUE_source03_BIG_shared_in_input434
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
    (g : Fin n) (q : ℕ)
    (hq : q ∈ sourceOriginalSource03PhysicalBIGSharedMultiset434
      z J ell m cap patterns x ch g) :
    q ∈ sourceOriginalSource03BIGInputPrimeSet434
      z J ell cap x g := by
  unfold sourceOriginalSource03PhysicalBIGSharedMultiset434 at hq
  obtain ⟨i,hi,hEq⟩ := Multiset.mem_map.mp hq
  apply Finset.mem_image.mpr
  exact ⟨ch.2.2.1.sigmaBig g i, Finset.mem_univ _, hEq⟩
/-- The original sourceAuxAvoidsEndpoints exclusion forces EVERY
genuine auxiliary BIG prime to lie OUTSIDE the actual input
endpoint prime support. This is a legality theorem, not a
probabilistic independence or distinct-auxiliary premise. -/
theorem source_original_TRUE_source03_legal_BIG_aux_outside_input434
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
    (o k : ℤ)
    (hlegal : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (g : Fin n) (q : ℕ)
    (hq : q ∈ sourceOriginalSource03PhysicalBIGAuxMultiset434
      z J ell m cap patterns x ch g) :
    q ∉ sourceOriginalSource03BIGInputPrimeSet434
       z J ell cap x g := by
  unfold sourceOriginalSource03PhysicalBIGAuxMultiset434 at hq
  obtain ⟨j,hj,hEq⟩ := Multiset.mem_map.mp hq
  intro hInput
  unfold sourceOriginalSource03BIGInputPrimeSet434 at hInput
  obtain ⟨i, hi, hInputEq⟩ := Finset.mem_image.mp hInput
  have hVals : (ch.2.1 g j).val = ((x.2 g).1 i).val := by
    calc
      _ = q := hEq
      _ = _ := hInputEq.symm
  have hSubs : ch.2.1 g j = (x.2 g).1 i := Subtype.ext hVals
  exact (hlegal.2.2.1 g j i).1 hSubs
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGLegalCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- For a legal original oriented physical E source choice,
filtering one TRUE Tb-group source prime multiset on the
ACTUAL input BIG endpoint support returns PRECISELY its
shared BIG part; all auxiliary prime slots are excluded. -/
theorem source_original_TRUE_source03_legal_BIG_shared_filter434
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
    (o k : ℤ)
    (hlegal : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (g : Fin n) :
    Multiset.filter
       (fun q => q ∈ sourceOriginalSource03BIGInputPrimeSet434
         z J ell cap x g)
       (sourceOriginalSource03PhysicalBIGGroupMultiset434
         z J ell m cap patterns x ch g) =
       sourceOriginalSource03PhysicalBIGSharedMultiset434
         z J ell m cap patterns x ch g := by
  rw [source_original_TRUE_source03_BIG_group_shared_aux_exact434]
  rw [Multiset.filter_add]
  have hs : Multiset.filter
      (fun q => q ∈ sourceOriginalSource03BIGInputPrimeSet434
        z J ell cap x g)
      (sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch g) =
      sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch g := by
    apply Multiset.filter_eq_self.mpr
    intro q hq
    exact source_original_TRUE_source03_BIG_shared_in_input434
      z J ell m cap patterns x ch g q hq
  have ha : Multiset.filter
      (fun q => q ∈ sourceOriginalSource03BIGInputPrimeSet434
        z J ell cap x g)
      (sourceOriginalSource03PhysicalBIGAuxMultiset434
        z J ell m cap patterns x ch g) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro q hq
    exact source_original_TRUE_source03_legal_BIG_aux_outside_input434
      z J ell m cap patterns x ch o k hlegal g q hq
  rw [hs,ha,add_zero]

/-- With original physical admissibility, equality of ONE Tb
group prime multiset iff equality of its SHARED (input endpoint)
AND AUXILIARY (outside endpoint) prime multisets separately.
Repeated prime labels are retained in both components. -/
theorem source_original_TRUE_source03_legal_BIG_group_collision_split434
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
    (o k : ℤ)
    (hch : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (hch' : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch')
    (g : Fin n) :
    (sourceOriginalSource03PhysicalBIGGroupMultiset434
      z J ell m cap patterns x ch g =
     sourceOriginalSource03PhysicalBIGGroupMultiset434
      z J ell m cap patterns x ch' g) ↔
    (sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch g =
     sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch' g ∧
     sourceOriginalSource03PhysicalBIGAuxMultiset434
        z J ell m cap patterns x ch g =
     sourceOriginalSource03PhysicalBIGAuxMultiset434
        z J ell m cap patterns x ch' g) := by
  constructor
  · intro hg
    have hs : sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch g =
      sourceOriginalSource03PhysicalBIGSharedMultiset434
        z J ell m cap patterns x ch' g := by
      have hf := congrArg (Multiset.filter
        (fun q => q ∈ sourceOriginalSource03BIGInputPrimeSet434
          z J ell cap x g)) hg
      rw [source_original_TRUE_source03_legal_BIG_shared_filter434
            z J ell m cap patterns x ch o k hch g,
          source_original_TRUE_source03_legal_BIG_shared_filter434
            z J ell m cap patterns x ch' o k hch' g] at hf
      exact hf
    constructor
    · exact hs
    · rw [source_original_TRUE_source03_BIG_group_shared_aux_exact434
          z J ell m cap patterns x ch g,
        source_original_TRUE_source03_BIG_group_shared_aux_exact434
          z J ell m cap patterns x ch' g,hs] at hg
      exact add_left_cancel hg
  · rintro ⟨hs,ha⟩
    rw [source_original_TRUE_source03_BIG_group_shared_aux_exact434
          z J ell m cap patterns x ch g,
        source_original_TRUE_source03_BIG_group_shared_aux_exact434
          z J ell m cap patterns x ch' g,hs,ha]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGSignature -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The COMPLETE per-TRUE-BIG-group prime signature of the actual
source physical choice: exactly shared endpoint marks AND auxiliary
outside-input marks, as a pair of MULTISETS (with multiplicities).
The joint K weight is NOT declared independent across components. -/
noncomputable def sourceOriginalSource03PhysicalBIGSignature434
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
      (fun _ p => p.val) J ell m cap patterns x) :
      Fin n → Multiset ℕ × Multiset ℕ :=
  fun g =>
    (sourceOriginalSource03PhysicalBIGSharedMultiset434
       z J ell m cap patterns x ch g,
     sourceOriginalSource03PhysicalBIGAuxMultiset434
       z J ell m cap patterns x ch g)
/-- A TRUE physical BIG integer-product collision between TWO
legal oriented E choices is exactly equality of ALL groupwise
(shared-input, auxiliary-outside-input) prime MULTISET pairs.
No spurious uniqueness of physical paths or auxiliary tuple order. -/
theorem source_original_TRUE_source03_PHYSICAL_BIG_prod_iff_signature434
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
    (o k : ℤ)
    (hch : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (hch' : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch') :
    (sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch =
     sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch') ↔
    (sourceOriginalSource03PhysicalBIGSignature434
       z J ell m cap patterns x ch =
     sourceOriginalSource03PhysicalBIGSignature434
       z J ell m cap patterns x ch') := by
  constructor
  · intro h
    have hM := (source_original_TRUE_SOURCE03_PHYSICAL_BIG_product_iff_prime_multiset434
      z J ell m cap patterns x ch ch').mp h
    have hg := (source_original_TRUE_source03_physical_BIG_group_collision_iff434
      z J ell m cap patterns x ch ch').mp hM
    funext g
    have hs := (source_original_TRUE_source03_legal_BIG_group_collision_split434
      z J ell m cap patterns x ch ch' o k hch hch' g).mp (hg g)
    exact Prod.ext hs.1 hs.2
  · intro h
    have hg : ∀ g : Fin n,
        sourceOriginalSource03PhysicalBIGGroupMultiset434
          z J ell m cap patterns x ch g =
        sourceOriginalSource03PhysicalBIGGroupMultiset434
          z J ell m cap patterns x ch' g := by
      intro g
      have hp := congrArg (fun f : Fin n → Multiset ℕ × Multiset ℕ => f g) h
      have hs : sourceOriginalSource03PhysicalBIGSharedMultiset434
          z J ell m cap patterns x ch g =
        sourceOriginalSource03PhysicalBIGSharedMultiset434
          z J ell m cap patterns x ch' g :=
        congrArg Prod.fst hp
      have ha : sourceOriginalSource03PhysicalBIGAuxMultiset434
          z J ell m cap patterns x ch g =
        sourceOriginalSource03PhysicalBIGAuxMultiset434
          z J ell m cap patterns x ch' g :=
        congrArg Prod.snd hp
      exact (source_original_TRUE_source03_legal_BIG_group_collision_split434
        z J ell m cap patterns x ch ch' o k hch hch' g).mpr ⟨hs,ha⟩
    have hM := (source_original_TRUE_source03_physical_BIG_group_collision_iff434
      z J ell m cap patterns x ch ch').mpr hg
    exact (source_original_TRUE_SOURCE03_PHYSICAL_BIG_product_iff_prime_multiset434
      z J ell m cap patterns x ch ch').mpr hM
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PhysicalBIGSignatureFiber -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- With actual oriented source E admissibility at a fixed REAL
input Fock state, the BIG integer collision Gram equals the sum
of squared coherent amplitudes conditioned on the COMPLETE
PER-GROUP (SHARED, AUXILIARY) prime multiset signatures.
The weights are arbitrary complex numbers, and Knu remains
joint when instantiated with literal sourceOrientedPhysicalCoefficient.

Crucially, the sum of the complex amplitudes is taken BEFORE
the square in every true physical signature-fibre; no diagonal
approximation or independence of source paths is made. -/
theorem source_original_TRUE_source03_legal_BIG_signature_coherent_Gram434
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
    (o k : ℤ)
    (F : Finset (FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x))
    (hlegal : ∀ ch ∈ F, sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (w : (FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) → ℂ) :
    let B := fun ch => sourceOriginalSource03CanonicalPhysicalBIGFactor434
      z J ell m cap patterns x ch
    let S := fun ch => sourceOriginalSource03PhysicalBIGSignature434
      z J ell m cap patterns x ch
    (∑ ch ∈ F, ∑ ch' ∈ F,
      if B ch = B ch' then star (w ch)*w ch' else 0) =
    ∑ sig ∈ F.image S,
      (((‖∑ ch ∈ F.filter (fun ch => S ch = sig), w ch‖^2:ℝ)):ℂ) := by
  dsimp only
  calc
    _ = ∑ ch ∈ F, ∑ ch' ∈ F,
      if sourceOriginalSource03PhysicalBIGSignature434
         z J ell m cap patterns x ch =
        sourceOriginalSource03PhysicalBIGSignature434
         z J ell m cap patterns x ch'
      then star (w ch)*w ch' else 0 := by
      apply Finset.sum_congr rfl
      intro ch hch
      apply Finset.sum_congr rfl
      intro ch' hch'
      have hsig := source_original_TRUE_source03_PHYSICAL_BIG_prod_iff_signature434
        z J ell m cap patterns x ch ch' o k
        (hlegal ch hch) (hlegal ch' hch')
      simp only [hsig]
    _ = _ := source_original_TRUE_prime_multiset_coherent_fiber_energy434
      F (fun ch => sourceOriginalSource03PhysicalBIGSignature434
        z J ell m cap patterns x ch) w
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TruePhysicalSignatureGram -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- UNCONDITIONAL eventual EXACT coherent character Gram of one
TRUE source03 physical E step, split into the actual LEGAL
(shared-input-BIG, auxiliary-outside-input-BIG) MULTISETS in
EACH genuine Tb group. Original joint signed Knu, oriented Fock
legality, independent permutations and arbitrary terminal future
observable are fully retained. Every same-signature off-diagonal
pair survives inside its coherent complex sum.

This is a SINGLE source state/fixed shared-SMALL fibre theorem,
NOT a first-DIRTY chronological Fock x seen Gram smallness theorem,
NOT sh:correlation, and NOT the full Green64 proof. -/
theorem eventually_source_original_TRUE_SOURCE03_PHYSICAL_exact_signature_Gram434
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
        let Sig : FullOrientedSourceChoice
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns x → Fin n → Multiset ℕ × Multiset ℕ :=
          fun ch => sourceOriginalSource03PhysicalBIGSignature434
            z J ell m cap patterns x ch
        (∑ χ : DirichletCharacter ℂ Q,
          ∑ ch ∈ F, ∑ ch' ∈ F,
            (star (w ch)*w ch') *
              (χ ((v ch)⁻¹)*χ (v ch'))) =
        (Q.totient : ℂ) *
          (∑ sig ∈ F.image Sig,
            (((‖∑ ch ∈ F.filter (fun ch => Sig ch = sig),
                 w ch‖^2 : ℝ)):ℂ)) := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_PHYSICAL_INTEGER_BIG_Gram434
      cfg J ell m] with L hGram
  intro n d vmax c0 z hd cap Nu _ patterns x q rho Vs Vb mu Knu
    zeta theta o k ho hk hK hOrigSmall future s
  have h := hGram n d vmax c0 z hd cap patterns x
    q rho Vs Vb mu Knu zeta theta o k ho hk hK hOrigSmall future s
  dsimp only at h ⊢
  rw [h]
  congr 1
  have hleg : ∀ ch ∈ sourceOriginalPhysicalSameSharedChoices434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k s,
      sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch := by
    intro ch hc
    have hh := (Finset.mem_filter.mp hc).1
    exact (Finset.mem_filter.mp hh).2
  exact source_original_TRUE_source03_legal_BIG_signature_coherent_Gram434
    z J ell m cap patterns x o k
    (sourceOriginalPhysicalSameSharedChoices434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k s)
    hleg
    (sourceOriginalPhysicalFutureWeight434
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k x future)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03LegalBIGFreeCard -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Each true source03 auxiliary prime draw contributes exactly
one label WITH MULTIPLICITY. Therefore the auxiliary prime
multiset size is the cardinality of the original source pattern's
free set C_g, not the number of distinct auxiliary primes. -/
theorem source_original_TRUE_source03_BIG_aux_multiset_card434
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
    (g : Fin n) :
    (sourceOriginalSource03PhysicalBIGAuxMultiset434
      z J ell m cap patterns x ch g).card =
      ((patterns ch.1).free g).card := by
  unfold sourceOriginalSource03PhysicalBIGAuxMultiset434
  rw [Multiset.card_map]
  change ((patterns ch.1).free g).attach.card =
    ((patterns ch.1).free g).card
  exact Finset.card_attach
/-- For TWO legal original source E choices with the SAME
BIG integer product, the NUMBER of auxiliary free draws
must agree in EVERY true Tb group. Thus cross-channel
patterns with differing groupwise free-card vectors C_g
CANNOT be BIG product collisions, regardless of the complex Knu.

This does not imply pattern identities or source path identities. -/
theorem source_original_TRUE_source03_legal_BIG_collision_free_card_eq434
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
    (o k : ℤ)
    (hch : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (hch' : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch')
    (hprod :
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch =
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch')
    (g : Fin n) :
    ((patterns ch.1).free g).card =
      ((patterns ch'.1).free g).card := by
  have hsig := (source_original_TRUE_source03_PHYSICAL_BIG_prod_iff_signature434
    z J ell m cap patterns x ch ch' o k hch hch').mp hprod
  have haux : sourceOriginalSource03PhysicalBIGAuxMultiset434
      z J ell m cap patterns x ch g =
    sourceOriginalSource03PhysicalBIGAuxMultiset434
      z J ell m cap patterns x ch' g :=
    congrArg Prod.snd (congrArg
      (fun f : Fin n → Multiset ℕ × Multiset ℕ => f g) hsig)
  have hcard := congrArg Multiset.card haux
  simpa only [
    source_original_TRUE_source03_BIG_aux_multiset_card434] using hcard

/-- A truly legal off-diagonal source pair from DIFFERENT
free-card vectors has an EXACTLY ZERO integer-product collision
term. This excludes cross-size channels before any positive
envelope or signed path-pair Gram estimate is attempted. -/
theorem source_original_TRUE_source03_legal_BIG_diff_free_card_zero434
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
    (o k : ℤ)
    (hch : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch)
    (hch' : sourceOrientedPhysicalLegal
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x o k ch')
    (g : Fin n)
    (hneq : ((patterns ch.1).free g).card ≠
      ((patterns ch'.1).free g).card)
    (w : (FullOrientedSourceChoice
      (sourceOriginalSource03CanonicalSmallCarrier434 z)
      (fun _ p => p.val)
      (sourceOriginalSource03CanonicalBigCarrier434 z)
      (fun _ p => p.val) J ell m cap patterns x) → ℂ) :
    (if sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch =
        sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch'
     then star (w ch)*w ch' else 0) = 0 := by
  have hno :
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch ≠
      sourceOriginalSource03CanonicalPhysicalBIGFactor434
        z J ell m cap patterns x ch' := by
    intro heq
    exact hneq (source_original_TRUE_source03_legal_BIG_collision_free_card_eq434
      z J ell m cap patterns x ch ch' o k hch hch' heq g)
  simp only [hno, ite_false]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ChronologicalSpectralGrowth -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Uniform ASYMPTOTIC numerical growth for ORIGINAL source03
signed chronological Fourier radii, with n moving under the
actual logarithmic group budget and 2R visits with R ≤ L².
The TRUE S+Ts source SMALL modulus has logarithm at least
L^a*exp(L^a)*vmin; the complete Fock E divisor costs only
O(sqrt L * (J+ell)*log L). NO new number-theoretic axiom. -/
theorem eventually_source_original_TRUE_chronological_window_growth434
    (a vmin C0 : ℝ) (ha : 0 < a) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ n R : ℕ, (n:ℝ) ≤ C0*Real.log L →
        (R:ℝ) ≤ L^2 →
        (4:ℝ)*(R:ℝ)*
          (Real.exp (Real.sqrt L))^(
            (J+ell)*(n+1)+(2*J+ell)*n) <
          Real.exp (L^a*(Real.exp (L^a)*vmin)) := by
  let A : ℕ := J+ell
  let B : ℕ := 2*J+ell
  let C : ℝ := ((A+B+1:ℕ):ℝ)*(C0+1)
  let K : ℝ := C+4
  have hC01 : 0 < C0+1 := by linarith
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by exact_mod_cast Nat.succ_pos (A+B)) hC01
  have hK : 0 < K := by dsimp [K]; linarith
  have hc : 0 < vmin/K := div_pos hv hK
  filter_upwards
    [eventually_source_original_exp_rpow_dominates_square434
      a (vmin/K) ha hc, eventually_ge_atTop (1:ℝ)] with L hg hL
  intro n R hn hR
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L := Real.log_le_self hL0
  have hnL : (n:ℝ) ≤ C0*L :=
    hn.trans (mul_le_mul_of_nonneg_left hlog hC0)
  have hn1 : ((n+1:ℕ):ℝ) ≤ (C0+1)*L := by
    push_cast
    linarith
  have hcoef : (C0:ℝ)*L ≤ (C0+1)*L := by
    nlinarith
  have hM : (((A*(n+1)+B*n:ℕ):ℝ)) ≤ C*L := by
    calc
      _ = (A:ℝ)*((n+1:ℕ):ℝ)+(B:ℝ)*(n:ℝ) := by push_cast; ring
      _ ≤ (A:ℝ)*((C0+1)*L)+(B:ℝ)*(C0*L) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg A))
          (mul_le_mul_of_nonneg_left hnL (Nat.cast_nonneg B))
      _ ≤ (A:ℝ)*((C0+1)*L)+(B:ℝ)*((C0+1)*L) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg B)) _
      _ = ((A+B:ℕ):ℝ)*((C0+1)*L) := by push_cast; ring
      _ ≤ ((A+B+1:ℕ):ℝ)*((C0+1)*L) := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_succ (A+B))
          (mul_nonneg hC01.le hL0)
      _ = C*L := by dsimp [C]; ring
  have hLsquare : L ≤ L^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) hL0]
  have hsqrt : Real.sqrt L ≤ L :=
    (Real.sqrt_le_iff).2 ⟨hL0,hLsquare⟩
  have hMroot : (((A*(n+1)+B*n:ℕ):ℝ)) * Real.sqrt L ≤ C*L^2 := by
    calc
      _ ≤ (((A*(n+1)+B*n:ℕ):ℝ)) * L :=
        mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)
      _ ≤ (C*L)*L := mul_le_mul_of_nonneg_right hM hL0
      _ = C*L^2 := by ring
  have hPow :
      (Real.exp (Real.sqrt L))^(A*(n+1)+B*n) ≤ Real.exp (C*L^2) := by
    rw [←Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hMroot
  have hRexp : (4:ℝ)*(R:ℝ) ≤ Real.exp (4*L^2) := by
    calc
      _ ≤ 4*L^2 := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ _ := by linarith [Real.add_one_le_exp (4*L^2)]
  have hSourceExponent : K*L^2 < L^a * (Real.exp (L^a)*vmin) := by
    have hKbound : K*L^2 < vmin*Real.exp (L^a) := by
      have hh := mul_lt_mul_of_pos_left hg hK
      calc
        _ < K*(vmin/K*Real.exp (L^a)) := hh
        _ = vmin*Real.exp (L^a) := by field_simp
    have hPower : 1 ≤ L^a := Real.one_le_rpow hL ha.le
    have hBound : vmin*Real.exp (L^a) ≤
        L^a*(Real.exp (L^a)*vmin) := by
      have hpos : 0 ≤ Real.exp (L^a)*vmin :=
        mul_nonneg (Real.exp_pos _).le hv.le
      convert mul_le_mul_of_nonneg_right hPower hpos using 1 <;> ring
    exact hKbound.trans_le hBound
  have hTotal :
    (4:ℝ)*(R:ℝ)*(Real.exp (Real.sqrt L))^(
      A*(n+1)+B*n) < Real.exp (L^a*(Real.exp (L^a)*vmin)) := by
    calc
      _ ≤ Real.exp (4*L^2)*Real.exp (C*L^2) := by
        exact mul_le_mul hRexp hPow
          (by positivity) (by positivity)
      _ = Real.exp (K*L^2) := by
        rw [←Real.exp_add]
        congr 1
        dsimp [K]
        ring
      _ < _ := Real.exp_lt_exp.mpr hSourceExponent
  simpa only [A,B] using hTotal
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03EventuallyPhysicalDIRTYNoReturn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- UNCONDITIONAL EVENTUAL discharge of the true canonical
source03 physical first-DIRTY no-return NUMERICAL WINDOW.
Fixed J,ell,m precede the threshold. ALL true n moving groups,
ALL signed RAW/comparison families, ALL |k| and ALL R with
R ≤ L² are admitted simultaneously. No fake small-prime-count
hypothesis or joint K norm bound occurs.
This is ONLY frequency separation, not signed Gram saving. -/
theorem eventually_source_original_TRUE_SOURCE03_physical_DIRTY_window434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (k : ℤ) (R : ℕ),
          (R:ℝ) ≤ L^2 →
        2*(2*R)*sourceOriginalActualSourceGEDualDivisorCap434
          u blockA blockB J ell m hmJ k <
            sourceOriginalActualSourceALLSmallModulus434 u := by
  filter_upwards [
    eventually_source_original_TRUE_chronological_window_growth434
      cfg.aexp cfg.vmin cfg.C0 cfg.haexp cfg.hv cfg.hC0 J ell
    ] with L hGrowth
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB k R hR
  have hn : (n:ℝ) ≤ cfg.C0*Real.log L := by
    simpa using u.hSmallGroups
  have hNumeric := hGrowth n R hn hR
  have hCap := source_original_ACTUAL_SOURCE_GE_true_divisor_cap_explicit434
    u blockA blockB J ell m hmJ k
  have hQ := source_original_TRUE_CANONICAL_MATCH_actual_SMALL_superexp434
    z u hmatch
  have hCast :
      (((2*(2*R)*sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k : ℕ) : ℝ)) <
      (sourceOriginalActualSourceALLSmallModulus434 u : ℝ) := by
    calc
      _ = (4:ℝ)*(R:ℝ)*
        (sourceOriginalActualSourceGEDualDivisorCap434
          u blockA blockB J ell m hmJ k : ℝ) := by
          push_cast
          ring
      _ ≤ (4:ℝ)*(R:ℝ)*
        (Real.exp (Real.sqrt L))^(
          (J+ell)*(n+1)+(2*J+ell)*n) := by
          have hCap' :
              (sourceOriginalActualSourceGEDualDivisorCap434
                u blockA blockB J ell m hmJ k : ℝ) ≤
                  (Real.exp (Real.sqrt L))^(
                    (J+ell)*(n+1)+(2*J+ell)*n) := by
            simpa only [Fintype.card_option,Fintype.card_fin] using hCap
          exact mul_le_mul_of_nonneg_left hCap' (by positivity)
      _ < Real.exp (L^cfg.aexp*
          (Real.exp (L^cfg.aexp)*cfg.vmin)) := hNumeric
      _ ≤ _ := hQ
  exact_mod_cast hCast

/-- As a direct REAL-physical first-DIRTY consequence, for
sufficiently large moving L and EVERY actual 2R-visit state
history with R ≤ L², two nonzero total signed frequencies in the
same initial AND terminal genuine SMALL torus fibre COINCIDE.
No remaining hwindow premise: it is discharged above using
Chebyshev-certified source03 S mass and actual E divisor bounds.
Coherent off-path equal-frequency Gram remains uncontrolled. -/
theorem eventually_source_original_TRUE_CANONICAL_DIRTY_no_return434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n))
        (Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
        (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
        (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
        (hR : (R:ℝ) ≤ L^2)
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
          xi rho zeta k R T q freq' ≠ 0),
          freq = freq' := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_physical_DIRTY_window434
      cfg J ell m hmJ] with L hwin
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB
    Q hA hB xi rho zeta k R T hk hkBound hR
    p q freq freq' hstarts hends hnp hnq
  exact source_original_TRUE_CANONICAL_MATCH_DIRTY_k_cancelled_no_return434
    z u hmatch blockA blockB J ell m hmJ
    Q hA hB xi rho zeta k R T hk hkBound
    (hwin n d vmax c0 x Y Hp z u hmatch blockA blockB k R hR)
    p q freq freq' hstarts hends hnp hnq
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03OriginalRNoReturn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- The chronological choice R=ceil(L^0.52) is eventually <= L^2. -/
theorem eventually_source_original_TRUE_R_ceil052_below_square434 :
    ∀ᶠ L : ℝ in atTop,
      ((Nat.ceil (L^(0.52:ℝ)) : ℕ):ℝ) ≤ L^2 := by
  filter_upwards [eventually_ge_atTop (2:ℝ)] with L hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hPower : L^(0.52:ℝ) ≤ L := by
    calc
      _ ≤ L^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le
        hL1 (by norm_num)
      _ = L := Real.rpow_one _
  have hCeil : ((Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ) <
      L^(0.52:ℝ)+1 := Nat.ceil_lt_add_one
        (Real.rpow_nonneg hL0 _)
  have hSquare : L+1 ≤ L^2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hL) (by linarith : 0 ≤ L+1)]
  exact le_trans (le_trans hCeil.le (by linarith : L^(0.52:ℝ)+1 ≤ L+1))
    hSquare

/-- This is a source03 arithmetic window at the literal R
used in the original birth-tail analysis, not an extra hypothesis. -/
theorem eventually_source_original_TRUE_SOURCE03_original_R_physical_window434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (k : ℤ),
        2*(2*Nat.ceil (L^(0.52:ℝ)))*
          sourceOriginalActualSourceGEDualDivisorCap434
            u blockA blockB J ell m hmJ k <
          sourceOriginalActualSourceALLSmallModulus434 u := by
  filter_upwards [
    eventually_source_original_TRUE_SOURCE03_physical_DIRTY_window434
      cfg J ell m hmJ,
    eventually_source_original_TRUE_R_ceil052_below_square434
    ] with L hwindow hR
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB k
  exact hwindow n d vmax c0 x Y Hp z u hmatch
    blockA blockB k (Nat.ceil (L^(0.52:ℝ))) hR
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03EventuallyRelativeSpectral -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- REAL SOURCE03 unconditional EVENTUAL full-path spectral
bijection: for all moving prime families canonically matched to
source03, and ALL signed first-DIRTY chronological Fock×seen
paths with nonzero complex amplitudes, equality of TOTAL integer
Fourier frequencies is EQUIVALENT to equality of their RELATIVE
S+Ts torus displacement. NO matched initial or terminal state
hypotheses; this is stronger than earlier endpoint version.
Uniform for original signed k within arc, 2R visits R≤L²,
all joint K RAW/comparison coefficients, and fixed J ell m. -/
theorem eventually_source_original_TRUE_CANONICAL_DIRTY_frequency_iff_relative434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
        (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
        (hk : 0 < k.natAbs) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
        (hR : (R:ℝ) ≤ L^2)
        (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
          (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
        (freq freq' : ℤ)
        (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T p freq ≠ 0)
        (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T q freq' ≠ 0),
      freq = freq' ↔
        sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R p =
          sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R q := by
  filter_upwards
    [eventually_source_original_TRUE_SOURCE03_physical_DIRTY_window434
      cfg J ell m hmJ] with L hwindow
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB Q hA hB
    xi rho zeta k R T hk hkBound hR p q freq freq' hnp hnq
  constructor
  · intro hFreq
    subst freq'
    exact source_original_ACTUAL_SOURCE_DIRTY_equal_frequency_relative_eq434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p q freq hnp hnq
  · intro hRelative
    exact source_original_TRUE_CANONICAL_MATCH_DIRTY_relative_k_cancelled_no_return434
      z u hmatch blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hk hkBound
      (hwindow n d vmax c0 x Y Hp z u hmatch blockA blockB k R hR)
      p q freq freq' hRelative hnp hnq
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeFibre -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact original source03 physical first-DIRTY complex amplitude
of ONE relative S+Ts torus sector at TOTAL Fourier frequency d.
The amplitude sums ALL real chronological Fock×seen paths,
with their signed joint RAW/comparison K and OLD gates, BEFORE
taking an absolute value or a square. -/
noncomputable def sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) : ℂ := by
  classical
  exact ∑ path ∈ (Finset.univ : Finset (
      (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))).filter
        (fun path => sourceOriginalActualSourceDIRTYRelativeTorus434
          u J ell R path = rel),
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq

/-- A NONZERO coherent relative-sector amplitude cannot arise
without some genuinely nonzero original chronological PATH
amplitude in that same sector. This does not replace complex
amplitudes by positive TV in the surviving sum. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_relative_fibre_nonzero_witness434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ)
    (hne : sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq ≠ 0) :
    ∃ path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
        (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
      sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R path = rel ∧
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T path freq ≠ 0 := by
  classical
  let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
    (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
  let s : Finset Paths := (Finset.univ : Finset Paths).filter
    (fun path => sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R path = rel)
  let A : Paths → ℂ := fun path =>
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq
  have hW : ∃ path ∈ s, A path ≠ 0 := by
    by_contra hn
    have hz : (∑ path ∈ s, A path) = 0 := by
      apply Finset.sum_eq_zero
      intro path hp
      by_contra hpn
      exact hn ⟨path,hp,hpn⟩
    exact hne hz
  obtain ⟨path,hp,hpn⟩ := hW
  exact ⟨path,(Finset.mem_filter.mp hp).2,hpn⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYDiagonalSector -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The UNIQUE actual S+Ts relative-torus sector carrying an
integer Fourier frequency d: coordinate-wise d modulo EVERY
original SMALL prime. It does NOT depend on the initial Fock
or numerical-seen state. -/
def sourceOriginalActualSourceDIRTYDiagonalTorus434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (freq : ℤ) :
    (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val) :=
  fun g p => (freq : ZMod p.val)

/-- Every actual source03 first-DIRTY nonzero path coefficient
belongs exactly to the diagonal relative S+Ts torus sector of
its TOTAL physical Fourier frequency. Unconditional, with
all original RAW/comparison joint K. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_path_diagonal_sector434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq : ℤ)
    (hn : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq ≠ 0) :
    sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R path =
      sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq := by
  funext g p
  exact source_original_ACTUAL_SOURCE_DIRTY_relative_equals_frequency434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T path freq hn g p

/-- A coherent physical relative S+Ts torus-sector amplitude is
EXACTLY ZERO off its selected integer-frequency residue key.
All path coefficients inside the surviving sector remain SIGNED. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_off_diagonal_sector_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ)
    (hwrong : rel ≠ sourceOriginalActualSourceDIRTYDiagonalTorus434
      u freq) :
    sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq = 0 := by
  classical
  unfold sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
  apply Finset.sum_eq_zero
  intro path hp
  have hrel := (Finset.mem_filter.mp hp).2
  by_contra hn
  have hdiag := source_original_ACTUAL_SOURCE_DIRTY_path_diagonal_sector434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T path freq hn
  exact hwrong (hrel.symm.trans hdiag)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYDiagonalRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- COMPLETE original source03 first-DIRTY physical Fourier
coefficient is exactly the genuine BIG baseline multiplied
by ONE coherent relative SMALL-torus sector selected by the
integer TOTAL frequency. No equal-start/end restriction,
no character average, no independent Fock/seen histories,
and NO positive envelope or lost RAW/comparison signs. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_root_diagonal_relative_coeff434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (freq : ℤ) :
    (sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T).coeff freq =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  classical
  let Paths := (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
    (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
  let key : Paths → _ :=
    sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R
  let selected := sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq
  let Amp : Paths → ℂ := fun path =>
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq
  have hsum : (∑ path : Paths, Amp path) =
      ∑ path ∈ (Finset.univ : Finset Paths).filter
        (fun path => key path = selected), Amp path := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro path hp
    by_cases hk : key path = selected
    · simp [hk]
    · have hz : Amp path = 0 := by
        by_contra hn
        exact hk (source_original_ACTUAL_SOURCE_DIRTY_path_diagonal_sector434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T path freq hn)
      simp [hk,hz]
  have hc := source_original_ACTUAL_SOURCE_DIRTY_true_path_coefficient434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T freq
  rw [hc]
  congr 1

/-- EXACT true original source03 total-mode signed energy lives
in ONE diagonal relative torus sector per frequency.
Only the coherent complex sum inside that sector remains. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_root_diagonal_relative_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (freq : ℤ) :
    ‖(sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T).coeff freq‖^2 =
    ‖(physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2 *
    ‖sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq‖^2 := by
  rw [source_original_ACTUAL_SOURCE_DIRTY_root_diagonal_relative_coeff434]
  rw [norm_mul,mul_pow]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYInitialWeight -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine initial complex Fock/SMALL-vacuum weight from
the UNCHANGED source03 first-DIRTY path amplitude. Its Fock
state and numerical seen history are the same actual input. -/
noncomputable def sourceOriginalActualSourceDIRTYInitialWeight434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedInitialWeight434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    (fun _ => le_rfl) Vs mu a

/-- The true first-DIRTY path amplitude is EXACTLY zero
whenever its initial physical vacuum weight is zero.
No end-state reset or independent repeated initial trial. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_path_zero_at_initial_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (tail : Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ)
    (hw : sourceOriginalActualSourceDIRTYInitialWeight434
      u J ell R a = 0) :
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T (a,tail) freq = 0 := by
  change sourceOriginalActualSourceDIRTYInitialWeight434
    u J ell R a * _ = 0
  rw [hw]
  exact zero_mul _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeFuture -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Actual source03 first-DIRTY normalized signed continuation
of one TRUE initial Fock×seen state and one true future state
path, with original joint K, OLD gates and insertion positions.
The quotient is harmless: the amplitude is already zero where
the physical initial vacuum weight is zero. -/
noncomputable def sourceOriginalActualSourceDIRTYNormalizedFuture434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (tail : Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ) : ℂ :=
  let w := sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a
  if w=0 then 0 else
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T (a,tail) freq / w

/-- No fake regularization of the actual signed K amplitudes:
the ORIGINAL physical path equals its initial Fock/vacuum
weight times the true normalized complex chronological future. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_normalized_future_factor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (tail : Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ) :
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T (a,tail) freq =
    sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a *
      sourceOriginalActualSourceDIRTYNormalizedFuture434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a tail freq := by
  classical
  let w := sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a
  let A := sourceOriginalActualSourceDIRTYPathAmplitude434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T (a,tail) freq
  change A = w * (if w=0 then 0 else A/w)
  by_cases hw : w=0
  · have ha0 : A=0 := source_original_ACTUAL_SOURCE_DIRTY_path_zero_at_initial_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a tail freq hw
    simp [hw,ha0]
  · simp only [if_neg hw]
    field_simp [hw]

/-- The actual FULL signed coherent continuation for ONE genuine
initial Fock×seen state and ONE true relative S+Ts torus sector.
The entire chronological state-path sum remains complex inside. -/
noncomputable def sourceOriginalActualSourceDIRTYRelativeFuture434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) : ℂ :=
  sourceOriginalSignedCoherentFibreSuffix434 (2*R)
    (sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R)
    (fun a tail => sourceOriginalActualSourceDIRTYNormalizedFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a tail freq) a rel

/-- TRUE source03 coherent sector now DISINTEGRATED by initial
physical Fock×seen states. A single complex continuation sum is
formed BEFORE the initial vacuum density is paired with it.
This has no chronological-history counting factor. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_relative_initial_pairing434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) :
    sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq =
    ∑ a : sourceOriginalActualSourceDIRTYPathState434 u J ell,
      sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a *
      sourceOriginalActualSourceDIRTYRelativeFuture434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a rel freq := by
  classical
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let key : H × (Fin (2*R) → H) → _ :=
    sourceOriginalActualSourceDIRTYRelativeTorus434 u J ell R
  let w : H → ℂ := sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R
  let U : H → (Fin (2*R) → H) → ℂ := fun a tail =>
    sourceOriginalActualSourceDIRTYNormalizedFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a tail freq
  have hAmp (path : H × (Fin (2*R) → H)) :
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T path freq =
        w path.1 * U path.1 path.2 :=
    source_original_ACTUAL_SOURCE_DIRTY_normalized_future_factor434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path.1 path.2 freq
  change (∑ path ∈ (Finset.univ : Finset (H × (Fin (2*R) → H))).filter
      (fun path => key path=rel),
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path freq) =
    ∑ a : H, w a *
      sourceOriginalSignedCoherentFibreSuffix434 (2*R) key U a rel
  simp_rw [hAmp]
  exact source_original_SIGNED_coherent_fibre_initial_disintegration434
    (2*R) key w U rel
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The exact ORIGINAL positive Fock/sector-weighted energy
of the SIGNED chronological future AFTER coherent summation
of ALL true state paths from each ORIGINAL initial vacuum
state, inside ONE true S+Ts relative-torus fibre.
NOT a TV norm of individual full paths. -/
noncomputable def sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedTrueTargetEnergy434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    Vs u.Vbig mu
    (fun a => sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a rel freq)

/-- Real source03 PHYSICAL signed Hilbert bound for a single
coherent relative S+Ts torus fibre. The initial factor is EXACTLY
the old true initial Fock/vacuum energy; the target factor is
the true Fock/OLD-density quadratic energy of the COMPLEX future
summed over all future histories for EACH initial state. Thus
no factor #histories, no sup history, no independence of joint K.
This is an explicit proved estimate, not the sought logarithmic
saving; the remaining target-energy budget is still open. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_relative_vacuum_CS434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) :
    ‖sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq‖ ≤
    Real.sqrt (sourceOriginalActualSourceInitialVacuumEnergy434
      u J ell R) *
    Real.sqrt (sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let w : H → ℂ := sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R
  let f : H → ℂ := fun a =>
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a rel freq
  let π : H → ℝ :=
    sourceOriginalActualSignedTrueFockDensity434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs u.Vbig mu
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hVb (g : β) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have hmu (g : β) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv := hVb g
    have hbp := hb g p
    dsimp [mu,physicalSourceMuTilde]
    positivity
  have hπ (a : H) : 0 < π a :=
    source_original_ACTUAL_signed_true_fock_density_pos434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs u.Vbig mu hVs hVb hmu a
  have hCS := source_original_SIGNED_joint_weighted_CS434
    π hπ w f
  have hIdent := source_original_ACTUAL_SOURCE_DIRTY_relative_initial_pairing434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T rel freq
  have hInitial := source_original_ACTUAL_initial_signed_dual_energy_vacuum434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap (fun _ => le_rfl) Vs u.Vbig mu hVs hVb hmu
  have hInitial' :
      sourceOriginalSignedJointInverseEnergy434 π w =
      sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R := by
    change sourceOriginalSignedJointInverseEnergy434 π w =
      sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap Vs mu at hInitial
    exact hInitial
  change ‖sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T rel freq‖ ≤
    Real.sqrt (sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R) *
      Real.sqrt (sourceOriginalSignedJointForwardEnergy434 π f)
  rw [hIdent]
  exact (hCS.trans_eq (by rw [hInitial']))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeEnergyNonneg -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The true signed coherent FUTURE target energy is nonnegative
for EVERY original source03 relative torus key and integer frequency.
This is a genuine weighted finite Fock×OLD-state L2 energy after
COMPLEX summation of future histories, not a path TV envelope. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_relative_target_energy_nonneg434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ) :
    0 ≤ sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let π : H → ℝ :=
    sourceOriginalActualSignedTrueFockDensity434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs u.Vbig mu
  let f : H → ℂ := fun a =>
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a rel freq
  change 0 ≤ sourceOriginalSignedJointForwardEnergy434 π f
  unfold sourceOriginalSignedJointForwardEnergy434
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)

/-- Real physical INITIAL vacuum energy has a provable
nonnegative value whenever the ORIGINAL BIG baseline b_p > 0.
This same exact b_p hypothesis already occurs in the physical
source OLD/Schur branches; not a new probability-normalization. -/
theorem source_original_ACTUAL_SOURCE_initial_vacuum_energy_nonneg434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    0 ≤ sourceOriginalActualSourceInitialVacuumEnergy434
      u J ell R := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hmu (g : β) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
    have hbp := hb g p
    dsimp [mu,physicalSourceMuTilde]
    positivity
  exact source_original_ACTUAL_physical_initial_vacuum_energy_nonneg434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap Vs hVs mu hmu
end Green64Analytic.CorrelationSquare

end

end

