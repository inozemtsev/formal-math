module

public import Green64.Library.Correlation.MemoryNumericGates
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part047
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part050
public import Green64.Library.Weights.Part045
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.Part049
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Correlation / Part036

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeMemoryActualGates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- True corrected smooth K, with the ORIGINAL signed graph shift 2*k.
    The character modulus in T remains |k|; this theorem changes none of it. -/
theorem eventually_native_memory_corrected_shift434
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      ∀ k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)),
        (2*k:ℤ) ≠ 0 ∧
        (((2*k:ℤ).natAbs:ℕ):ℝ) < Real.exp (L^(1/10:ℝ)) := by
  filter_upwards [
    eventually_native_memory_poly_shift434 (K+89) (by linarith),
    eventually_gt_atTop (1:ℝ)] with L hpoly hL
  have hLpos : 0 < L := by linarith
  intro k hk
  have hks := source_corrected_smooth_shift_abs_le
    (L^K) (L^(89:ℝ)) (by positivity) k hk
  have hnonzero : (2*k:ℤ) ≠ 0 := by
    intro h
    have : k = 0 := by omega
    exact hks.1 this
  have hcap : (((2*k:ℤ).natAbs:ℕ):ℝ) ≤ 4*L^(K+89) := by
    calc
      _ = 2*(k.natAbs:ℝ) := by
        norm_num [Int.natAbs_mul]
      _ ≤ 2*(2*L^K*L^(89:ℝ)) :=
        mul_le_mul_of_nonneg_left hks.2.2 (by norm_num)
      _ = 4*L^(K+89) := by
        rw [Real.rpow_add hLpos]
        ring
  exact ⟨hnonzero, hcap.trans_lt hpoly⟩

/-- The genuine 20-field MemorySourceDomain, now without any assumed
    numeric shift, visit or reciprocal-mass bounds. All groups are source
    S / remaining Ts / independent full Tb. -/
theorem eventually_native_memory_corrected_domain434
    (r : ℕ) (hr : 1 ≤ r) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧
      ∀ k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)),
      ∀ hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty,
      MemorySourceDomain
        (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
        (fun g => (sourceNativeOriginalTb434 r L g).card)
        (1/2:ℝ) (9/10:ℝ) (SourceNativeMemorySmallMass434 r L hS)
        (sourceNativeOriginalVbig434 r L) (2*k) (Nat.ceil (L^(0.52:ℝ))) := by
  classical
  have hrho : Real.sqrt (1/2:ℝ) < (9/10:ℝ)^2 := by
    have hs : (Real.sqrt (1/2:ℝ))^2 = (1/2:ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (1/2:ℝ)
    nlinarith
  have hFloor : 0 < Real.log (6/5:ℝ)/2 :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  filter_upwards [
    eventually_source_native_original_group_masses434 r hr,
    eventually_native_memory_corrected_shift434 K hK,
    eventually_native_memory_original_visits434]
    with L hMass hShift hVisits
  refine ⟨hMass.1, ?_⟩
  intro k hk hS
  have hm := hMass.2.2 hS
  have hsk := hShift k hk
  exact source_native_memory_domain_of_numeric_gates434
    r L hr hMass.1 hS (1/2) (9/10)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hrho
    (2*k) hsk.1 hsk.2
    (Nat.ceil (L^(0.52:ℝ))) hVisits.1 hVisits.2
    (hFloor.trans_le hm.1.1)
    (fun i => hFloor.trans_le (hm.2.1 i).1)
    (fun g => hFloor.trans_le (hm.2.2 g).1)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalProbeExpandedFamily -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Actual finite source03 pattern plus TWO global original active
log-cell / primitive-character indices. Each cell is independently
selected under that pattern's REAL product prime law. -/
noncomputable def sourceOriginalProbeExpandedFamily434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi : ℝ) :=
  sourceOriginalActualFourIndexFamily434
    (sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fun ν => sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi)
    (fun ν => sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi) Q

/-- Exact ABSOLUTE coefficient of one original primitive Fourier
comparison term; only the source j_A and j_B cell normalizations
appear. The four independent sign channels do not affect this norm. -/
noncomputable def sourceOriginalProbeExpandedCost434
    {G : Type} [DecidableEq G] (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (z : Σ ν : SourceOriginalProbePattern434 G m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)))) : ℝ :=
  sourceOriginalTwoCellCoefficient434
    (sourceOriginalProbeCellA434 m P V z.1 (hA z.1))
    (sourceOriginalProbeCellB434 m P V z.1 (hB z.1))
    z.2.1.1 z.2.2.1

/-- Exact source03 per-term coefficients have positive sign after
taking absolute value, by the actual canonical active cell
threshold. No arbitrary hCost or hMass is postulated. -/
theorem source_original_probe_expanded_cost_nonneg434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (xi : ℝ) (hxi : 0 < xi)
    (z : Σ ν : SourceOriginalProbePattern434 G m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))))
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi) :
    0 ≤ sourceOriginalProbeExpandedCost434 m Q P V hA hB z := by
  classical
  have hmem := (Finset.mem_sigma.mp hz)
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m :=
    hmem.1
  have hAB := (Finset.mem_product.mp hmem.2)
  have hja : z.2.1.1 ∈
      sourceOriginalProbeActiveCellsA434 m P V z.1 (hA z.1) xi :=
    (Finset.mem_product.mp hAB.1).1
  have hjb : z.2.2.1 ∈
      sourceOriginalProbeActiveCellsB434 m P V z.1 (hB z.1) xi :=
    (Finset.mem_product.mp hAB.2).1
  exact (source_original_two_cell_coefficient_bound434
    (sourceOriginalProbeCellA434 m P V z.1 (hA z.1))
    (sourceOriginalProbeCellB434 m P V z.1 (hB z.1))
    z.2.1.1 z.2.2.1 xi hxi
    ((source_original_probe_active_cell_A_mem_iff434
       m P V z.1 (hA z.1) xi (hhA z.1 hν) hxi _).mp hja)
    ((source_original_probe_active_cell_B_mem_iff434
       m P V z.1 (hB z.1) xi (hhB z.1 hν) hxi _).mp hjb)).1

/-- No hFamilyBudget: the COMPLETE actual source03 expanded family
has total coefficient mass <= 2^(m(s1+s2))*Q^4*xi^-4,
including every primitive conductor and both independent cells. -/
theorem source_original_probe_expanded_family_cost434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (hPrime : ∀ g p,p ∈ P g → p.Prime)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (xi : ℝ) (hxi : 0 < xi) :
    (∑ z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi,
        sourceOriginalProbeExpandedCost434 m Q P V hA hB z) ≤
    (2^(m*(blockA.card+blockB.card)):ℝ)*((Q:ℝ)^4*(xi⁻¹)^4) := by
  classical
  simp only [sourceOriginalProbeExpandedFamily434,
    sourceOriginalProbeExpandedCost434]
  have hReindex := source_original_actual_four_index_reindex434
    (sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fun ν => sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi)
    (fun ν => sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi)
    Q (fun _ => (1:ℝ))
    (fun ν => sourceOriginalProbeCellA434 m P V ν (hA ν))
    (fun ν => sourceOriginalProbeCellB434 m P V ν (hB ν))
  simp only [sourceOriginalActualFourIndexCost434,one_mul] at hReindex
  rw [hReindex]
  simpa only [one_mul] using
    source_original_probe_canonical_active_expansion_cost434
      blockA blockB m Q P V hV hVpos hPrime hA hB
      hhA hhB xi hxi
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeGroupedProductMass -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact SOURCE03 ν selected physical BIG prime product equals
the product of the true per-group enumerated C6 labels, for
EVERY original prime-mark tuple, including repeated numerical
prime values. This is a genuine product origin identity, not
an external hypothesis that C6 and ν integer atoms match. -/
theorem source_original_probe_grouped_prime_product_eq434
    {G : Type} [DecidableEq G]
    (m : ℕ) (block : Finset G)
    (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ)
    (a : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : block,
       Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val)) :
    sourceOriginalGramPrimeProduct434
      (fun z : Σ g : block,
       Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val) a =
    sourceOriginalGramPrimeProduct434
      (fun z : A => S z.val.1)
      (sourceOriginalProbeBigGroupedPrimeEquiv434
        m block A hBlock S a) := by
  classical
  let E := sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock
  let T := sourceOriginalProbeBigGroupedPrimeEquiv434
    m block A hBlock S
  unfold sourceOriginalGramPrimeProduct434
  exact Fintype.prod_equiv E
    (fun z => (a z).val)
    (fun z => (T a z).val)
    (fun z => (source_original_probe_big_grouped_prime_equiv_apply434
      m block A hBlock S a z).symm)

/-- Exact SOURCE03 ν selected BIG prime harmonic probability
mass equals that of its C6 grouped representation.
The probability for each true marked position (g,i) remains
W_g(p), including the original 1/(p V_g).
This is algebraic and does not require positivity or any
conditional independence of arbitrary mark-dependent f. -/
theorem source_original_probe_grouped_prime_mass_eq434
    {G : Type} [DecidableEq G]
    (m : ℕ) (block : Finset G)
    (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ) (W : G → ℕ → ℝ)
    (a : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : block,
       Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val)) :
    sourceOriginalGramPrimeMass434
      (fun z : Σ g : block,
       Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val)
      (fun z p => W z.1.val p) a =
    sourceOriginalGramPrimeMass434
      (fun z : A => S z.val.1)
      (fun z p => W z.val.1 p)
      (sourceOriginalProbeBigGroupedPrimeEquiv434
         m block A hBlock S a) := by
  classical
  let E := sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock
  let T := sourceOriginalProbeBigGroupedPrimeEquiv434
    m block A hBlock S
  unfold sourceOriginalGramPrimeMass434
  exact Fintype.prod_equiv E
    (fun z => W z.1.val (a z).val)
    (fun z => W z.val.1 (T a z).val)
    (fun z => by
      rw [source_original_probe_group_sigma_group434
        m block A hBlock z]
      rw [source_original_probe_big_grouped_prime_equiv_apply434
        m block A hBlock S a z])
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeGroupedAtomReindex -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- TRUE exact original ν-marked complex integer product-atom
coefficients are IDENTICAL after physical prime tuple reindexing
by actual BIG groups and each group's exact selected probe count.
The test f may depend ARBITRARILY on all ν prime-mark labels,
not just on their integer product. No product-map injectivity,
new probability law, or assumed physical sum equality. -/
theorem source_original_probe_grouped_product_atom_coefficient_eq434
    {G : Type} [DecidableEq G]
    (m : ℕ) (block : Finset G)
    (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ) (W : G → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434
      (fun z : A => S z.val.1) → ℂ)
    (n : ℕ) :
    sourceOriginalPhysicalProductAtomCoefficient434
      (fun z : Σ g : block,
         Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
           S z.1.val)
      (fun z p => W z.1.val p)
      (fun x => f (sourceOriginalProbeBigGroupedPrimeEquiv434
         m block A hBlock S x)) n =
    sourceOriginalPhysicalProductAtomCoefficient434
      (fun z : A => S z.val.1)
      (fun z p => W z.val.1 p)
      f n := by
  classical
  let SG : (Σ g : block,
    Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) →
      Finset ℕ := fun z => S z.1.val
  let SA : A → Finset ℕ := fun z => S z.val.1
  let muG : (Σ g : block,
    Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) →
      ℕ → ℝ := fun z p => W z.1.val p
  let muA : A → ℕ → ℝ := fun z p => W z.val.1 p
  let E := sourceOriginalProbeBigGroupedPrimeEquiv434
    m block A hBlock S
  have hPoint (x : SourceOriginalGramPrimeTuple434 SG) :
      (if sourceOriginalGramPrimeProduct434 SG x = n
       then (sourceOriginalGramPrimeMass434 SG muG x:ℂ) *
         f (E x) else 0) =
      (if sourceOriginalGramPrimeProduct434 SA (E x) = n
       then (sourceOriginalGramPrimeMass434 SA muA (E x):ℂ) *
          f (E x) else 0) := by
    rw [source_original_probe_grouped_prime_product_eq434
        m block A hBlock S x,
      source_original_probe_grouped_prime_mass_eq434
        m block A hBlock S W x]
  have hSum := Fintype.sum_equiv E
    (fun x : SourceOriginalGramPrimeTuple434 SG =>
      if sourceOriginalGramPrimeProduct434 SG x = n
      then (sourceOriginalGramPrimeMass434 SG muG x:ℂ)*f (E x)
      else 0)
    (fun x : SourceOriginalGramPrimeTuple434 SA =>
      if sourceOriginalGramPrimeProduct434 SA x = n
      then (sourceOriginalGramPrimeMass434 SA muA x:ℂ)*f x
      else 0)
    hPoint
  unfold sourceOriginalPhysicalProductAtomCoefficient434
  exact hSum

/-- Under precisely the SAME original ν/group equivalence,
weighted L² energies of completely mark-dependent endpoint
tests are equal, not merely bounded. Thus the generic
two-BIG-block C6 bound transfers to the true marked
source03 ν-test without any extra energy normalization
or restriction that f factorizes through product n. -/
theorem source_original_probe_grouped_physical_energy_eq434
    {G : Type} [DecidableEq G]
    (m : ℕ) (block : Finset G)
    (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ) (W : G → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434
      (fun z : A => S z.val.1) → ℂ) :
    (∑ a : SourceOriginalGramPrimeTuple434
       (fun z : Σ g : block,
         Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
           S z.1.val),
       sourceOriginalGramPrimeMass434
         (fun z : Σ g : block,
           Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
             S z.1.val)
         (fun z p => W z.1.val p) a *
         ‖f (sourceOriginalProbeBigGroupedPrimeEquiv434
           m block A hBlock S a)‖^2) =
    (∑ a : SourceOriginalGramPrimeTuple434
       (fun z : A => S z.val.1),
       sourceOriginalGramPrimeMass434
         (fun z : A => S z.val.1)
         (fun z p => W z.val.1 p) a * ‖f a‖^2) := by
  classical
  let SG : (Σ g : block,
    Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) →
      Finset ℕ := fun z => S z.1.val
  let SA : A → Finset ℕ := fun z => S z.val.1
  let muG : (Σ g : block,
    Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) →
      ℕ → ℝ := fun z p => W z.1.val p
  let muA : A → ℕ → ℝ := fun z p => W z.val.1 p
  let E := sourceOriginalProbeBigGroupedPrimeEquiv434
    m block A hBlock S
  have hPoint (x : SourceOriginalGramPrimeTuple434 SG) :
      sourceOriginalGramPrimeMass434 SG muG x * ‖f (E x)‖^2 =
      sourceOriginalGramPrimeMass434 SA muA (E x) * ‖f (E x)‖^2 := by
    rw [source_original_probe_grouped_prime_mass_eq434
      m block A hBlock S W x]
  exact Fintype.sum_equiv E
    (fun x : SourceOriginalGramPrimeTuple434 SG =>
       sourceOriginalGramPrimeMass434 SG muG x * ‖f (E x)‖^2)
    (fun x : SourceOriginalGramPrimeTuple434 SA =>
       sourceOriginalGramPrimeMass434 SA muA x * ‖f x‖^2)
    hPoint
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueCandidateCellGeometry -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- TRUE SOURCE03 ν-dependent candidate GLOBAL log-cell
complexity on BOTH selected A and B prime-blocks, using actual
prime support and actual numbers of labelled selected probes.
The single polynomial bound is independent of all large prime
support sizes and allows repeated numerical prime values in
different labelled positions. -/
theorem source_original_probe_true_two_candidate_cell_bound434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (L d hA hB : ℝ)
    (hL : 1 ≤ L) (hhA : 0 < hA) (hhB : 0 < hB)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    (((sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card:ℝ) +
      ((sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card:ℝ)) ≤
       ((Fintype.card ν.1:ℝ)*L^d)/hA +
       ((Fintype.card ν.2:ℝ)*L^d)/hB + 4 := by
  have hA := source_original_true_BIG_candidate_cell_real_bound434
    (fun z : ν.1 => P z.val.1) L d hA hL hhA
    (fun z p hp => hPrimeA z p hp)
  have hB := source_original_true_BIG_candidate_cell_real_bound434
    (fun z : ν.2 => P z.val.1) L d hB hL hhB
    (fun z p hp => hPrimeB z p hp)
  linarith

/-- The actual ν-specific discarded two-ENDPOINT coefficient
2*(#candidate_A+#candidate_B)*xi is bounded by an explicit
linear-in-slot-count and polynomial-in-L quantity. This will
be combined with the physically proved signed rare-event L²
estimate; it is not an independent cell-budget hypothesis. -/
theorem source_original_probe_two_candidate_loss_bound434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (L d hA hB xi : ℝ)
    (hL : 1 ≤ L) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 ≤ xi)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    2*(((sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card +
       (sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card:ℕ):ℝ)*xi ≤
    2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
       ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi := by
  have hcount := source_original_probe_true_two_candidate_cell_bound434
    m ν P L d hA hB hL hhA hhB hPrimeA hPrimeB
  have hcount' :
      (((sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card +
       (sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card:ℕ):ℝ) ≤
    (((Fintype.card ν.1:ℝ)*L^d)/hA +
       ((Fintype.card ν.2:ℝ)*L^d)/hB)+4 := by
    push_cast
    linarith
  have hh := mul_le_mul_of_nonneg_right hcount' hxi
  nlinarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDiscardedBothL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE source03 ν-dependent *full physical* free-slot
independent law, with all complementary prime marks present:
the joint source/target bilinear contribution of the event
"source B GLOBAL cell discarded OR target A GLOBAL cell discarded"
has squared L² saving 2*(N_B+N_A)*xi, where N_B/N_A count
GENUINELY attainable original prime-product cells.

This theorem uses the PROVED marginal pushforwards C153 and
actual physical discarded cell masses C155/C156, with the
CORRECT source-vs-target orientation. The free-slot counts
are ell+|C_g|, all tests may depend on ALL free slots, and
the joint phase H can depend on both endpoints; only |H|<=1.
It does not assert the full signed comparison kernel is
unit-bounded on discarded states. -/
theorem source_original_probe_true_physical_discarded_union_L2_sq434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi)
    (sourceTest targetTest :
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (H : (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
        (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let nA := (sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA).card
    let nB := (sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB).card
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                 (SourceOriginalVariableBIGState434 BP t),
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0))‖^2 ≤
      (2*((nA+nB:ℕ):ℝ)*xi) *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let nA := (sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA).card
  let nB := (sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB).card
  let etaSource : ℝ := (nB:ℝ)*xi
  let etaTarget : ℝ := (nA:ℝ)*xi
  have hVEq (g : G) :
      V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      _ = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa [BP,prime] using
          (Finset.sum_coe_sort (P g)
            (fun p : ℕ => 1/(p:ℝ))).symm
  obtain ⟨hmuNN,hmuOne⟩ :=
    source_original_joint_harmonic_normalized434
      BP prime V hVpos hVEq
  have hw : ∀ x : X, 0 ≤ w x :=
    source_original_variable_BIG_mass_nonneg434 BP t mu hmuNN
  have htotal : (∑ x : X, w x) ≤ 1 :=
    le_of_eq (source_original_variable_BIG_law_total434
      BP t mu hmuOne)
  have hetaS : 0 ≤ etaSource := by
    dsimp [etaSource]
    positivity
  have hetaT : 0 ≤ etaTarget := by
    dsimp [etaTarget]
    positivity
  have hBadSource :
      (∑ s : X, w s*
        (@ite ℝ (badSource s) (Classical.propDecidable (badSource s)) 1 0)) ≤ etaSource := by
    have hBMass := source_original_probe_true_source_B_discarded_mass434
      J ell m hmJ ν P V hV hVpos hB xi hhB hxi
    change
      (∑ s : X, w s*
        (if sourceOriginalLiteralLogCellIndex434 hB
          (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
         then 0 else (1:ℝ))) ≤ etaSource at hBMass
    calc
      _ = (∑ s : X, w s*
        (if sourceOriginalLiteralLogCellIndex434 hB
          (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
         then 0 else (1:ℝ))) := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hKeep : sourceOriginalLiteralLogCellIndex434 hB
            (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
        · have hn : ¬ badSource s := by
            dsimp only [badSource]
            exact not_not_intro hKeep
          simp only [if_neg hn, if_pos hKeep, mul_zero]
        · have hy : badSource s := hKeep
          simp only [if_pos hy, if_neg hKeep, mul_one]
      _ ≤ etaSource := hBMass
  have hBadTarget :
      (∑ v : X, w v*
        (@ite ℝ (badTarget v) (Classical.propDecidable (badTarget v)) 1 0)) ≤ etaTarget := by
    have hAMass := source_original_probe_true_target_A_discarded_mass434
      J ell m hmJ ν P V hV hVpos hA xi hhA hxi
    change
      (∑ v : X, w v*
        (if sourceOriginalLiteralLogCellIndex434 hA
          (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
         then 0 else (1:ℝ))) ≤ etaTarget at hAMass
    calc
      _ = (∑ v : X, w v*
        (if sourceOriginalLiteralLogCellIndex434 hA
          (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
         then 0 else (1:ℝ))) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hKeep : sourceOriginalLiteralLogCellIndex434 hA
            (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
        · have hn : ¬ badTarget v := by
            dsimp only [badTarget]
            exact not_not_intro hKeep
          simp only [if_neg hn, if_pos hKeep, mul_zero]
        · have hy : badTarget v := hKeep
          simp only [if_pos hy, if_neg hKeep, mul_one]
      _ ≤ etaTarget := hAMass
  have hL2 :=
    source_original_finite_union_rare_endpoint_L2_sq434
      w w hw hw htotal htotal
      badSource badTarget etaSource etaTarget
      hetaS hetaT hBadSource hBadTarget
      sourceTest targetTest H hH
  have hEta :
      2*(etaSource+etaTarget) =
      2*((nA+nB:ℕ):ℝ)*xi := by
    dsimp [etaSource,etaTarget]
    push_cast
    ring
  change
    ‖(∑ ab : X × X,
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0))‖^2 ≤
      (2*((nA+nB:ℕ):ℝ)*xi) *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2)
  rw [←hEta]
  convert hL2 using 1
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hp : badSource ab.1 ∨ badTarget ab.2
  · simp only [if_pos hp]
  · simp only [if_neg hp]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDiscardedBIGGeometryL2 -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- SOURCE03 physically exact ν-pattern dropped-cell contribution
with explicit BIG geometric cell-count loss. The width and all
source prime groups remain literal: only the true upper scale
p <= exp(L^d) is required. This combines C157 original full
variable-slot marginal and C158 candidate-count geometry.
Arbitrary complex tests and an arbitrary joint unit-bounded H
are allowed. It does not automatically bound the full original
signed Knu kernel on discarded states. -/
theorem source_original_probe_true_physical_discarded_BIG_L2_sq434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi)
    (sourceTest targetTest :
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (H : (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
        (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let nA := (sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA).card
    let nB := (sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB).card
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                 (SourceOriginalVariableBIGState434 BP t),
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0))‖^2 ≤
      (2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
        ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi) *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let nA := (sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA).card
  let nB := (sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB).card
  let ESource : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
  let ETarget : ℝ := ∑ v : X, w v*‖targetTest v‖^2
  let Cgeo : ℝ :=
    2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
       ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
  have hNN (g : G) (p : BP g) : 0 ≤ mu g p := by
    exact source_original_harmonic_prime_nonneg434
      (fun p : BP g => (prime g p)) (V g) (hVpos g) p
  have hw (s : X) : 0 ≤ w s :=
    source_original_variable_BIG_mass_nonneg434 BP t mu hNN s
  have hESource : 0 ≤ ESource := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hw s) (sq_nonneg _)
  have hETarget : 0 ≤ ETarget := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (hw v) (sq_nonneg _)
  have hE : 0 ≤ ESource*ETarget := mul_nonneg hESource hETarget
  have hCellLoss : 2*((nA+nB:ℕ):ℝ)*xi ≤ Cgeo := by
    change
      2*(((sourceOriginalCandidateLogCells434
        (fun z : ν.1 => P z.val.1) hA).card +
        (sourceOriginalCandidateLogCells434
        (fun z : ν.2 => P z.val.1) hB).card:ℕ):ℝ)*xi ≤
      2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
         ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
    exact source_original_probe_two_candidate_loss_bound434
      m ν P L d hA hB xi hL hhA hhB hxi.le hPrimeA hPrimeB
  have hRaw := source_original_probe_true_physical_discarded_union_L2_sq434
    J ell m hmJ ν P V hV hVpos
    hA hB xi hhA hhB hxi
    sourceTest targetTest H hH
  change
    ‖(∑ ab : X × X,
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0))‖^2 ≤
      Cgeo*ESource*ETarget
  calc
    _ ≤ (2*((nA+nB:ℕ):ℝ)*xi)*ESource*ETarget := by
      exact hRaw
    _ ≤ Cgeo*ESource*ETarget := by
      have hh := mul_le_mul_of_nonneg_right hCellLoss hE
      nlinarith [hh]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDyadicDiscardedL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The full ORIGINAL SOURCE03 ν-dependent physical
free-slot source/target harmonic laws give the same
discarded-GLOBAL-cell L² cost after restriction to ONE
actual pair of product dyads; arbitrary complex endpoint
tests and any jointly dependent unit-bounded phase H.
This is the genuine marginal theorem C159 specialized
through the new validated dyadic rare-event lemma C194.
No loss in test energies and no cell count beyond the
true attainable log-cell complexity. -/
theorem source_original_probe_true_physical_dyadic_discarded_union_L2_sq434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi)
    (Uscale Vscale : ℝ)
    (sourceTest targetTest :
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (H : (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
        (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let dyadSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
    let dyadTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
    let nA := (sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA).card
    let nB := (sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB).card
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                 (SourceOriginalVariableBIGState434 BP t),
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if dyadSource ab.1 ∧ dyadTarget ab.2 then
           (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0)
         else 0))‖^2 ≤
      (2*((nA+nB:ℕ):ℝ)*xi) *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let dyadSource : X → Prop := fun s =>
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val):ℝ) ≤ 2*Vscale
  let dyadTarget : X → Prop := fun v =>
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val):ℝ) ≤ 2*Uscale
  let nA := (sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA).card
  let nB := (sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB).card
  let etaSource : ℝ := (nB:ℝ)*xi
  let etaTarget : ℝ := (nA:ℝ)*xi
  have hVEq (g : G) :
      V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      _ = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa [BP,prime] using
          (Finset.sum_coe_sort (P g)
            (fun p : ℕ => 1/(p:ℝ))).symm
  obtain ⟨hmuNN,hmuOne⟩ :=
    source_original_joint_harmonic_normalized434
      BP prime V hVpos hVEq
  have hw : ∀ x : X, 0 ≤ w x :=
    source_original_variable_BIG_mass_nonneg434 BP t mu hmuNN
  have htotal : (∑ x : X, w x) ≤ 1 :=
    le_of_eq (source_original_variable_BIG_law_total434
      BP t mu hmuOne)
  have hetaS : 0 ≤ etaSource := by
    dsimp [etaSource]
    positivity
  have hetaT : 0 ≤ etaTarget := by
    dsimp [etaTarget]
    positivity
  have hBadSource :
      (∑ s : X, w s*
        (@ite ℝ (badSource s) (Classical.propDecidable (badSource s)) 1 0)) ≤ etaSource := by
    have hBMass := source_original_probe_true_source_B_discarded_mass434
      J ell m hmJ ν P V hV hVpos hB xi hhB hxi
    change
      (∑ s : X, w s*
        (if sourceOriginalLiteralLogCellIndex434 hB
          (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
         then 0 else (1:ℝ))) ≤ etaSource at hBMass
    calc
      _ = (∑ s : X, w s*
        (if sourceOriginalLiteralLogCellIndex434 hB
          (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
         then 0 else (1:ℝ))) := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hKeep : sourceOriginalLiteralLogCellIndex434 hB
            (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∈ activeB
        · have hn : ¬ badSource s := by
            dsimp only [badSource]
            exact not_not_intro hKeep
          simp only [if_neg hn, if_pos hKeep, mul_zero]
        · have hy : badSource s := hKeep
          simp only [if_pos hy, if_neg hKeep, mul_one]
      _ ≤ etaSource := hBMass
  have hBadTarget :
      (∑ v : X, w v*
        (@ite ℝ (badTarget v) (Classical.propDecidable (badTarget v)) 1 0)) ≤ etaTarget := by
    have hAMass := source_original_probe_true_target_A_discarded_mass434
      J ell m hmJ ν P V hV hVpos hA xi hhA hxi
    change
      (∑ v : X, w v*
        (if sourceOriginalLiteralLogCellIndex434 hA
          (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
         then 0 else (1:ℝ))) ≤ etaTarget at hAMass
    calc
      _ = (∑ v : X, w v*
        (if sourceOriginalLiteralLogCellIndex434 hA
          (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
         then 0 else (1:ℝ))) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hKeep : sourceOriginalLiteralLogCellIndex434 hA
            (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∈ activeA
        · have hn : ¬ badTarget v := by
            dsimp only [badTarget]
            exact not_not_intro hKeep
          simp only [if_neg hn, if_pos hKeep, mul_zero]
        · have hy : badTarget v := hKeep
          simp only [if_pos hy, if_neg hKeep, mul_one]
      _ ≤ etaTarget := hAMass
  have hL2 :=
    source_original_finite_dyad_masked_union_rare_L2_sq434
      w w hw hw htotal htotal dyadSource dyadTarget
      badSource badTarget etaSource etaTarget
      hetaS hetaT hBadSource hBadTarget
      sourceTest targetTest H hH
  have hEta :
      2*(etaSource+etaTarget) =
      2*((nA+nB:ℕ):ℝ)*xi := by
    dsimp [etaSource,etaTarget]
    push_cast
    ring
  change
    ‖(∑ ab : X × X,
       (((w ab.1)*(w ab.2):ℝ):ℂ) *
         star (sourceTest ab.1)*targetTest ab.2*
         (if dyadSource ab.1 ∧ dyadTarget ab.2 then
           (if badSource ab.1 ∨ badTarget ab.2 then H ab else 0)
         else 0))‖^2 ≤
      (2*((nA+nB:ℕ):ℝ)*xi) *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2)
  rw [←hEta]
  convert hL2 using 1
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hd : dyadSource ab.1 ∧ dyadTarget ab.2
  · by_cases hp : badSource ab.1 ∨ badTarget ab.2
    · simp only [if_pos hd, if_pos hp]
    · simp only [if_pos hd, if_neg hp]
  · simp only [if_neg hd]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueHprimeScale -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The TRUE source03 two-global comparison scale H'=U_A U_B,
built from the original integer active cells, not a separately
chosen positive dyadic number. -/
noncomputable def sourceOriginalProbeTrueHprime434
    {G : Type} (m Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (z : Σ ν : SourceOriginalProbePattern434 G m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)))) : ℝ :=
  Real.exp ((z.2.1.1:ℝ)*(hA z.1)) *
    Real.exp ((z.2.2.1:ℝ)*(hB z.1))

/-- Source03's TRUE product scale is uniformly sandwiched:
 exp(2*L^c - h_A - h_B) < H' <=
 exp(m*(s_A+s_B)*L^d).
It holds for EVERY actual five-index z, with the original
A and B both NONEMPTY, finite auxiliary draws, log-cell
probability threshold and big-group prime windows.
No extra source hU_i/hH'_z assumptions and no J-dependence. -/
theorem source_original_probe_true_Hprime_bounds434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G)
    (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi : ℝ) (L c d : ℝ) (hL : 0 ≤ L)
    (hBounds : ∀ g ∈ blockA ∪ blockB,∀ p ∈ P g,
      Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (z : Σ ν : SourceOriginalProbePattern434 G m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))))
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi) :
    Real.exp (2*(L^c) - ((hA z.1)+(hB z.1))) <
      sourceOriginalProbeTrueHprime434 m Q hA hB z ∧
    sourceOriginalProbeTrueHprime434 m Q hA hB z ≤
      Real.exp ((((m*(blockA.card+blockB.card):ℕ):ℝ))*(L^d)) := by
  classical
  have hMem := Finset.mem_sigma.mp hz
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m := hMem.1
  have hAB := Finset.mem_product.mp hMem.2
  have hJA : z.2.1.1 ∈
      sourceOriginalProbeActiveCellsA434 m P V z.1 (hA z.1) xi :=
    (Finset.mem_product.mp hAB.1).1
  have hJB : z.2.2.1 ∈
      sourceOriginalProbeActiveCellsB434 m P V z.1 (hB z.1) xi :=
    (Finset.mem_product.mp hAB.2).1
  have hScA := source_original_probe_active_A_big_scale434
    blockA blockB m z.1 hν P V L c d hL hBounds
    (hA z.1) xi (hhA z.1 hν) z.2.1.1 hJA
  have hScB := source_original_probe_active_B_big_scale434
    blockA blockB m z.1 hν P V L c d hL hBounds
    (hB z.1) xi (hhB z.1 hν) z.2.2.1 hJB
  have hLowSum :
      2*(L^c) - ((hA z.1)+(hB z.1)) <
      (z.2.1.1:ℝ)*(hA z.1)+(z.2.2.1:ℝ)*(hB z.1) := by
    linarith [hScA.1,hScB.1]
  have hCardN : z.1.1.card+z.1.2.card ≤
      m*(blockA.card+blockB.card) := by
    simpa only [source_original_probe_aux_card_exact434] using
      source_original_probe_aux_card_bound434
        blockA blockB m z.1 hν
  have hCardR :
      (((z.1.1.card+z.1.2.card:ℕ):ℝ)) ≤
      (((m*(blockA.card+blockB.card):ℕ):ℝ)) := by
    exact_mod_cast hCardN
  have hLd : 0 ≤ L^d := Real.rpow_nonneg hL _
  have hHighSum :
      (z.2.1.1:ℝ)*(hA z.1)+(z.2.2.1:ℝ)*(hB z.1) ≤
        (((m*(blockA.card+blockB.card):ℕ):ℝ))*(L^d) := by
    calc
      _ ≤ (z.1.1.card:ℝ)*(L^d)+(z.1.2.card:ℝ)*(L^d) :=
        add_le_add hScA.2 hScB.2
      _ = (((z.1.1.card+z.1.2.card:ℕ):ℝ))*(L^d) := by
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCardR hLd
  constructor
  · have hh : Real.exp (2*(L^c)-((hA z.1)+(hB z.1))) <
        Real.exp ((z.2.1.1:ℝ)*(hA z.1)+
          (z.2.2.1:ℝ)*(hB z.1)) :=
      Real.exp_lt_exp.mpr hLowSum
    simpa only [sourceOriginalProbeTrueHprime434,Real.exp_add] using hh
  · have hh : Real.exp ((z.2.1.1:ℝ)*(hA z.1)+
          (z.2.2.1:ℝ)*(hB z.1)) ≤
        Real.exp ((((m*(blockA.card+blockB.card):ℕ):ℝ))*(L^d)) :=
      Real.exp_le_exp.mpr hHighSum
    simpa only [sourceOriginalProbeTrueHprime434,Real.exp_add] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03BigBandC196Inputs -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The true SOURCE03 complete BIG-group prime interval
(u_g,v_g] meets C196's arithmetic prime/conductor cutoff.
No abstract hBIG premise is imported: Q^2<p follows from
the actual integer group lower boundary and strict (u,v]
membership. -/
theorem source_original_source03_big_band_conductor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (Q : ℕ) (loB hiB : β → ℕ)
    (hBigBand : ∀ g, d.Tb g =
      sourceOriginalActualPrimeBand434 (loB g) (hiB g))
    (hBigLower : ∀ g, Q^2 ≤ loB g) :
    ∀ g : β, ∀ p ∈ d.Tb g, p.Prime ∧ Q^2 < p := by
  intro g p hp
  rw [hBigBand g] at hp
  obtain ⟨hpInterval,hPrime⟩ := (Finset.mem_filter.mp hp)
  have hLo : loB g < p := (Finset.mem_Ioc.mp hpInterval).1
  exact ⟨hPrime,lt_of_le_of_lt (hBigLower g) hLo⟩

/-- Under the source03 full-band upper endpoint bound, every
genuine BIG prime also meets the literal C196 upper cutoff
p <= exp(L^d). In particular this applies to all ν-selected
BIG source and target groups, with no added support. -/
theorem source_original_source03_big_band_upper434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (dexp : ℝ) (loB hiB : β → ℕ)
    (hBigBand : ∀ g, d.Tb g =
      sourceOriginalActualPrimeBand434 (loB g) (hiB g))
    (hUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dexp)) :
    ∀ g : β, ∀ p ∈ d.Tb g,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^dexp) := by
  intro g p hp
  rw [hBigBand g] at hp
  obtain ⟨hpInterval,hPrime⟩ := Finset.mem_filter.mp hp
  have hpNat : p ≤ hiB g := (Finset.mem_Ioc.mp hpInterval).2
  have hpReal : (p:ℝ) ≤ (hiB g:ℝ) := by
    exact_mod_cast hpNat
  exact ⟨hPrime,hpReal.trans (hUpper g)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03BigGroupPrefactor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- An AUTHENTIC SOURCE03 result, without an auxiliary group
count hypothesis: the ACTUAL moving BIG groups of the original
SourceComparisonData434 have logarithmic count, at most
cfg.C0*log L, each with genuine number of labelled prime marks
tb(g)≤ cfg.tmax, and true harmonic normalizers
Vbig(g)≥cfg.vmin>0. Consequently their original C6
per-group factorial atom prefactor is <=L^C whenever
C≥cfg.C0*log(cfg.tmax! *
 max(1,cfg.vmin^-1)^cfg.tmax).
This DISCHARGES the factorial-prefactor logarithmic-loss
hypothesis for the actual BIG groups directly from the
original source data. It does not establish the separate
cross-group prime-support disjointness needed for the
sharp C6 physical atom envelope. -/
theorem source_original_source03_big_group_C6_prefactor_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (C : ℕ) (hL : 1 ≤ L)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ)) :
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset β) d.tb d.Vbig ≤ L^C := by
  classical
  let A : ℝ := ((cfg.tmax.factorial:ℕ):ℝ) *
    (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax
  have hFact : (1:ℝ) ≤ ((cfg.tmax.factorial:ℕ):ℝ) := by
    have hNat : 1 ≤ cfg.tmax.factorial := by
      have hp := Nat.factorial_pos cfg.tmax
      omega
    exact_mod_cast hNat
  have hBase : (1:ℝ) ≤ max (1:ℝ) cfg.vmin⁻¹ :=
    le_max_left _ _
  have hPow : (1:ℝ) ≤
      (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ hBase (Nat.zero_le cfg.tmax))
  have hAone : 1 ≤ A := by
    dsimp [A]
    have hh := mul_le_mul hFact hPow
      (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) ≤ ((cfg.tmax.factorial:ℕ):ℝ))
    simpa using hh
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hAone
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hCount :
      ((Finset.univ : Finset β).card:ℝ) ≤
      cfg.C0*Real.log L := by
    simpa using d.hBigGroups
  have hGroup :
      ((Finset.univ : Finset β).card:ℝ)*Real.log A ≤
      (C:ℝ)*Real.log L := by
    calc
      _ ≤ (cfg.C0*Real.log L)*Real.log A :=
        mul_le_mul_of_nonneg_right hCount hLogA
      _ = (cfg.C0*Real.log A)*Real.log L := by ring
      _ ≤ (C:ℝ)*Real.log L := by
        apply mul_le_mul_of_nonneg_right _ hLogL
        exact hExponent
  exact source_original_c6_group_prefactor_log_power434
    (Finset.univ : Finset β) d.tb d.Vbig
    cfg.tmax C cfg.vmin L cfg.hv hL
    (by intro g hg; exact d.htb g)
    (by intro g hg; exact d.hVbig g)
    hGroup
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03OrderedBandAdmissibility -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- TRUE SOURCE03 small groups need only be SUBSETS of
separated prime intervals (the manuscript does not say
small groups contain every prime). Actual BIG groups, by
contrast, are complete prime intervals. If the same-family
intervals are numerically disjoint and the manuscript's
small/large prime scale gap holds, full original group
separation is derived with no synthetic small-band equality
or independent cross-family disjointness hypothesis. -/
theorem source_original_source03_ordered_prime_bands_admissible434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 1 < L)
    (loS hiS : ι → ℕ)
    (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, d.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, d.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ d.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hTbLower : ∀ j : β, ∀ p ∈ d.Tb j,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ)) :
    SourceOriginalSource03GroupSeparation434 d := by
  have hSmall : ∀ i j : ι, ∀ p : ℕ,
      p ∈ d.Ts i → p ∈ d.Ts j → i=j := by
    intro i j p hpi hpj
    by_contra hneq
    have hDisj := source_original_actual_prime_bands_disjoint434
      (loS i) (hiS i) (loS j) (hiS j) (hSmallOrder i j hneq)
    exact (Finset.disjoint_left.mp hDisj)
      (hSmallSubset i hpi) (hSmallSubset j hpj)
  have hBig : ∀ i j : β, ∀ p : ℕ,
      p ∈ d.Tb i → p ∈ d.Tb j → i=j := by
    intro i j p hpi hpj
    by_contra hneq
    have hDisj := source_original_actual_prime_bands_disjoint434
      (loB i) (hiB i) (loB j) (hiB j) (hBigOrder i j hneq)
    rw [hBigFull i] at hpi
    rw [hBigFull j] at hpj
    exact (Finset.disjoint_left.mp hDisj) hpi hpj
  exact source_original_source03_separation_from_scales434
    cfg x L Y Hprime d hL hTsUpper hTbLower hSmall hBig
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03RealBandBelowSqrt -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 250000

/-- For original 0 < b < c < d < 1/2, every actual prime
inside the SMALL or BIG source03 moving exponential bands is
below exp(sqrt L). This is exactly SourceComparisonData.hGroup,
without artificially changing any prime set. -/
theorem source_original_SOURCE03_real_exp_band_le_sqrt434
    (L e : ℝ) (hL : 1 < L) (he : e ≤ (1/2:ℝ)) :
    Real.exp (L^e) ≤ Real.exp (Real.sqrt L) := by
  apply Real.exp_le_exp.mpr
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL.le he

/-- Original genuine finite SMALL and FULL BIG source groups
are bounded by the real physical source mass truncation.
No arbitrary modeled group can evade the current finite orbit. -/
theorem source_original_SOURCE03_true_group_union_below_sqrt434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (L b c d : ℝ) (hL : 1 < L)
    (hbd : b ≤ (1/2:ℝ))
    (hd : d ≤ (1/2:ℝ))
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (hS : ∀ p∈S, (p:ℝ) ≤ Real.exp (L^b))
    (hTs : ∀ i p, p∈Ts i → (p:ℝ) ≤ Real.exp (L^b))
    (hTb : ∀ i p, p∈Tb i → (p:ℝ) ≤ Real.exp (L^d)) :
    ∀ p ∈ (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)),
      (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  intro p hp
  have hs := source_original_SOURCE03_real_exp_band_le_sqrt434
    L b hL hbd
  have hb := source_original_SOURCE03_real_exp_band_le_sqrt434
    L d hL hd
  rcases Finset.mem_union.mp hp with hleft | hright
  · rcases Finset.mem_union.mp hleft with hpS | hpTs
    · exact (hS p hpS).trans hs
    · rcases Finset.mem_biUnion.mp hpTs with ⟨i,hi,hip⟩
      exact (hTs i p hip).trans hs
  · rcases Finset.mem_biUnion.mp hright with ⟨i,hi,hip⟩
    exact (hTb i p hip).trans hb
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalPrimeSlice -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 240000

/-- Concrete slice of the original source03 SourceComparisonData434
group inputs. The actual P_g are finite sets of Nat.Prime,
the BIG sets are ALL primes in integer intervals, and V_g is
the exact harmonic sum, not a freely assigned mass.
This type includes the group cardinality and FULL disjointness
that SourceComparisonData434 itself does not currently enforce. -/
structure SourceOriginalSource03CanonicalPrimeSlice434
    (n : ℕ) (cfg : SourceComparisonFixed434)
    (L d vmax c0 : ℝ) where
  T : ℕ
  P : Option (Fin n) → Finset ℕ
  V : Option (Fin n) → ℝ
  left : Fin n → ℕ
  right : Fin n → ℕ
  hTpos : 0 < T
  hTlog : 0 < Real.log L
  hTlower : 0 < (T : ℝ)
  hTcountsLow : c0*(T:ℝ) ≤ (n:ℝ)
  hTcountsHigh : ((n+1:ℕ):ℝ) ≤ cfg.C0*(T:ℝ)
  hSmallLog : (n:ℝ) ≤ cfg.C0*Real.log L
  hBigLog : (n:ℝ) ≤ cfg.C0*Real.log L
  hSmallNonempty : ∀ g, (P g).Nonempty
  hSmallBand : ∀ g p, p∈P g →
    p.Prime ∧ Real.exp (L^cfg.aexp) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^cfg.bexp)
  hSmallHarmonic : ∀ g,
    V g = ∑ p ∈ P g, (1:ℝ)/(p:ℝ)
  hSmallMass : ∀ g, cfg.vmin ≤ V g ∧ V g < vmax
  hBigOrdered : ∀ i, left i < right i
  hBigBand : ∀ i p, p∈sourceOriginalActualPrimeBand434
    (left i) (right i) →
    p.Prime ∧ Real.exp (L^cfg.cexp) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^d)
  hBigMass : ∀ i, cfg.vmin ≤
      sourceOriginalPrimeBandHarmonicMass434 (left i) (right i) ∧
      sourceOriginalPrimeBandHarmonicMass434 (left i) (right i) < vmax
  hSS : ∀ g h, g≠h → Disjoint (P g) (P h)
  hBB : ∀ i j, i≠j → Disjoint
    (sourceOriginalActualPrimeBand434 (left i) (right i))
    (sourceOriginalActualPrimeBand434 (left j) (right j))
  hSB : ∀ g i, Disjoint (P g)
    (sourceOriginalActualPrimeBand434 (left i) (right i))

namespace SourceOriginalSource03CanonicalPrimeSlice434
variable {n : ℕ} {cfg : SourceComparisonFixed434} {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- Literal original SOURCE fields, including distinguished S. -/
def S : Finset ℕ := z.P none
def Ts (i : Fin n) : Finset ℕ := z.P (some i)
def Tb (i : Fin n) : Finset ℕ :=
  sourceOriginalActualPrimeBand434 (z.left i) (z.right i)
def Vs : ℝ := z.V none
def Vsmall (i : Fin n) : ℝ := z.V (some i)
def Vbig (i : Fin n) : ℝ :=
  sourceOriginalPrimeBandHarmonicMass434 (z.left i) (z.right i)
def G : Finset ℕ := z.S ∪
  ((Finset.univ : Finset (Fin n)).biUnion z.Ts) ∪
  ((Finset.univ : Finset (Fin n)).biUnion z.Tb)

/-- Exactly the source SMALL harmonic identity missing from the
unaugmented SourceComparisonData434 record. -/
theorem exact_SMALL_harmonic434 :
    z.Vs = ∑ p ∈ z.S, (1:ℝ)/(p:ℝ) ∧
    (∀ i, z.Vsmall i = ∑ p ∈ z.Ts i, (1:ℝ)/(p:ℝ)) := by
  exact ⟨z.hSmallHarmonic none,fun i => z.hSmallHarmonic (some i)⟩

/-- The source real BIG mass is the reciprocal sum over its
complete prime interval, without an independent free mass. -/
theorem exact_BIG_harmonic434 :
    ∀ i, z.Vbig i = ∑ p ∈ z.Tb i, (1:ℝ)/(p:ℝ) := by
  intro i
  rfl

/-- Every literal original SOURCE prime field obeys the same
upper exp(sqrt L) truncation as SourceComparisonData434.hGroup.
This includes ALL Ts and Tb, not just the distinguished S. -/
theorem physical_G_below_sqrt434
    (hL : 1 < L) (hExp : d < (1/2:ℝ))
    (hcd : cfg.cexp < d) :
    ∀ p ∈ z.G, (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  have hbd : cfg.bexp ≤ (1/2:ℝ) :=
    (cfg.hbc.trans (hcd.trans hExp)).le
  have hd : d ≤ (1/2:ℝ) := hExp.le
  exact source_original_SOURCE03_true_group_union_below_sqrt434
    L cfg.bexp cfg.cexp d hL hbd hd
    z.S z.Ts z.Tb
    (fun p hp => (z.hSmallBand none p hp).2.2)
    (fun i p hp => (z.hSmallBand (some i) p hp).2.2)
    (fun i p hp => (z.hBigBand i p hp).2.2)

/-- All SOURCE group fields needed by the unchanged comparison
data: source membership in G, primality of every group prime,
true harmonic V and every literal group disjointness, including
distinguished S vs all other SMALL and BIG groups. -/
theorem source_group_membership_and_disjoint434 :
    z.S ⊆ z.G ∧
    (∀ p ∈ z.S, p.Prime) ∧
    (∀ i p, p∈z.Ts i → p.Prime) ∧
    (∀ i p, p∈z.Tb i → p.Prime) ∧
    (∀ i p, p∈z.S → p∉z.Ts i) ∧
    (∀ i p, p∈z.S → p∉z.Tb i) ∧
    (∀ i j, i≠j → Disjoint (z.Ts i) (z.Ts j)) ∧
    (∀ i j, i≠j → Disjoint (z.Tb i) (z.Tb j)) ∧
    (∀ i j, Disjoint (z.Ts i) (z.Tb j)) := by
  classical
  refine ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    (fun p hp => (z.hSmallBand none p hp).1),
    (fun i p hp => (z.hSmallBand (some i) p hp).1),
    (fun i p hp => (z.hBigBand i p hp).1),
    ?_,?_,?_,?_,?_⟩
  · intro i p hp hpi
    exact (Finset.disjoint_left.mp
      (z.hSS none (some i) (by simp))) hp hpi
  · intro i p hp hpi
    exact (Finset.disjoint_left.mp (z.hSB none i)) hp hpi
  · intro i j hij
    exact z.hSS (some i) (some j) (by simpa using hij)
  · intro i j hij
    exact z.hBB i j hij
  · intro i j
    exact z.hSB (some i) j

end SourceOriginalSource03CanonicalPrimeSlice434
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalBigNonempty -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 250000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- The TRUE source03 BIG group has at least one genuine prime.
This is a CONSEQUENCE of its proven strictly positive exact
reciprocal-prime mass, not an extra BIG-group existence axiom. -/
theorem source_original_CANONICAL_true_BIG_nonempty434
    (i : Fin n) :
    (z.Tb i).Nonempty := by
  by_contra hn
  have he : z.Tb i = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hn
  have hz : z.Vbig i = 0 := by
    rw [z.exact_BIG_harmonic434 i, he]
    simp
  have hpos : (0:ℝ) < z.Vbig i :=
    cfg.hv.trans_le (z.hBigMass i).1
  linarith

/-- All TRUE source BIG prime group values have positive
reciprocal harmonic normalization. -/
theorem source_original_CANONICAL_true_BIG_mass_pos434
    (i : Fin n) : 0 < z.Vbig i :=
  cfg.hv.trans_le (z.hBigMass i).1

/-- The true distinguished SMALL group and EACH Ts group are
all nonempty, including when there are no Ts groups (n=0). -/
theorem source_original_CANONICAL_true_SMALL_nonempty434 :
    z.S.Nonempty ∧ (∀ i : Fin n, (z.Ts i).Nonempty) := by
  exact ⟨z.hSmallNonempty none, fun i => z.hSmallNonempty (some i)⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalTruePrimeGroupCardinalityLower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 220000

/-- Actual reciprocal mass of a finite group of primes above
a genuine positive lower cutoff A is at most card/A.
No made-up i.i.d. prime measure or Mertens assumption. -/
theorem source_original_TRUE_prime_mass_le_card_over_lower434
    (s : Finset ℕ) (A : ℝ) (hA : 0 < A)
    (hbelow : ∀ p ∈ s, A ≤ (p:ℝ)) :
    (∑ p ∈ s, (1:ℝ)/(p:ℝ)) ≤
      (s.card:ℝ)/A := by
  calc
    _ ≤ ∑ p ∈ s, (1:ℝ)/A := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hA (hbelow p hp)
    _ = (s.card:ℝ)/A := by
      simp [Finset.sum_const,nsmul_eq_mul]
      ring

/-- A positive normalized harmonic mass forces a genuinely
LARGE number of DISTINCT actual prime labels, not just a
nonempty BIG Fock group. -/
theorem source_original_TRUE_prime_mass_implies_card_lower434
    (s : Finset ℕ) (A vmin : ℝ)
    (hA : 0 < A) (hvmin : 0 ≤ vmin)
    (hbelow : ∀ p ∈ s, A ≤ (p:ℝ))
    (hmass : vmin ≤ ∑ p ∈ s, (1:ℝ)/(p:ℝ)) :
    A*vmin ≤ (s.card:ℝ) := by
  have hh := source_original_TRUE_prime_mass_le_card_over_lower434
    s A hA hbelow
  have h := hmass.trans hh
  simpa only [mul_comm] using (le_div_iff₀ hA).mp h

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)

/-- For EVERY original source03 FULL BIG prime interval,
the TRUE source prime support at exp(L^cfg.cexp)
and V_big>=cfg.vmin imply the concrete cardinal lower bound
exp(L^cfg.cexp)*cfg.vmin <= number of actual primes in Tb.
The proof relies on the real canonical prime group construction
and its actual MASS; no extra nonemptiness or prime count axiom. -/
theorem source_original_CANONICAL_true_BIG_card_lower434
    (i : Fin n) :
    Real.exp (L^cfg.cexp)*cfg.vmin ≤ ((z.Tb i).card:ℝ) := by
  have hA : (0:ℝ) < Real.exp (L^cfg.cexp) :=
    Real.exp_pos _
  apply source_original_TRUE_prime_mass_implies_card_lower434
    (z.Tb i) (Real.exp (L^cfg.cexp)) cfg.vmin
    hA cfg.hv.le
  · intro p hp
    exact (z.hBigBand i p hp).2.1
  · exact (z.hBigMass i).1

/-- The exact same minimum-cardinality phenomenon holds for
distinguished S and each Ts SMALL group. -/
theorem source_original_CANONICAL_true_SMALL_card_lower434
    (g : Option (Fin n)) :
    Real.exp (L^cfg.aexp)*cfg.vmin ≤ ((z.P g).card:ℝ) := by
  have hA : (0:ℝ) < Real.exp (L^cfg.aexp) := Real.exp_pos _
  apply source_original_TRUE_prime_mass_implies_card_lower434
    (z.P g) (Real.exp (L^cfg.aexp)) cfg.vmin hA cfg.hv.le
  · intro p hp
    exact (z.hSmallBand g p hp).2.1
  · have h := (z.hSmallMass g).1
    rw [z.hSmallHarmonic g] at h
    exact h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalPrimeSliceExist -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 340000

/-- EVENTUAL EXISTENCE of an ACTUAL concrete SOURCE prime-data slice
whose field names and types match the original SourceComparisonData434
group inputs S,Ts,Tb,Vs,Vsmall,Vbig,G. This is constructed from
the unconditional original-power64 Chebyshev group geometry with
the exact moving source S/Ts/Tb count and exact harmonic mass.
No endpoint F/G or sign claims are manufactured. -/
theorem source_original_eventually_source03_canonical_prime_slice434
    (cfg : SourceComparisonFixed434)
    (d vmax c0 κS κB : ℝ)
    (hcd : cfg.cexp < d) (hd : d < (1/2:ℝ))
    (hvm : cfg.vmin < vmax)
    (hc0 : 0 < c0) (hC0 : c0 < cfg.C0)
    (hκSpos : 0 < κS) (hκBpos : 0 < κB)
    (hκS : 192*κS*(cfg.vmin+1) ≤ cfg.bexp-cfg.aexp)
    (hκB : 192*κB*(cfg.vmin+1) ≤ d-cfg.cexp)
    (hκSupper : κS ≤ cfg.C0) (hκBupper : κB ≤ cfg.C0) :
    ∀ᶠ L : ℝ in atTop,
      ∃ n : ℕ,
        Nonempty (SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0) := by
  have hgeom :=
    source_original_eventually_TRUE_source03_full_prime_geometry434
      cfg.aexp cfg.bexp cfg.cexp d
      cfg.vmin vmax cfg.vmin vmax κS κB
      cfg.haexp cfg.hab cfg.hbc hcd
      cfg.hv hvm cfg.hv hvm hκS hκB
  have hcount :=
    source_original_eventually_TRUE_original_group_cardinalities434
      c0 cfg.C0 κS κB hc0 hC0 hκSpos hκBpos
  filter_upwards [hgeom,hcount,eventually_gt_atTop (1:ℝ)]
    with L hGeom hCount hL
  obtain ⟨T,n,hT,hTlow,hNlow,hNhigh,hScap,hBcap⟩ := hCount
  obtain ⟨P,V,left,right,hS,hSband,hB,hBband,hSS,hBB,hSB⟩ :=
    hGeom n n hScap hBcap
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hTreal : 0 < (T:ℝ) := by exact_mod_cast hT
  have hcard : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by
    exact_mod_cast Nat.le_succ n
  have hlogS : (n:ℝ) ≤ cfg.C0*Real.log L := by
    calc
      _ ≤ ((n+1:ℕ):ℝ) := hcard
      _ ≤ κS*Real.log L := hScap
      _ ≤ cfg.C0*Real.log L :=
        mul_le_mul_of_nonneg_right hκSupper hlog.le
  have hlogB : (n:ℝ) ≤ cfg.C0*Real.log L := by
    calc
      _ ≤ κB*Real.log L := hBcap
      _ ≤ cfg.C0*Real.log L :=
        mul_le_mul_of_nonneg_right hκBupper hlog.le
  refine ⟨n,⟨⟨T,P,V,left,right,hT,hlog,hTreal,
    hNlow,hNhigh,hlogS,hlogB,
    ?_,hSband,?_,?_,?_,hBband,?_,hSS,hBB,hSB⟩⟩⟩
  · intro g
    exact (hS g).1
  · intro g
    exact (hS g).2.1
  · intro g
    exact (hS g).2.2
  · intro i
    exact (hB i).1
  · intro i
    exact (hB i).2
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalPrimeSliceRates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 270000

/-- Explicitly select POSITIVE real group-count rates, fitting
all SOURCE03 Chebyshev band budget constraints and the
UNCHANGED SourceComparisonFixed434.C0 logarithmic group cap.
There is no arbitrary rate whose admissibility was assumed. -/
theorem source_original_SOURCE03_actual_rates_exist434
    (cfg : SourceComparisonFixed434)
    (d c0 : ℝ) (hcd : cfg.cexp < d)
    (hc0 : 0 < c0) (hC0 : c0 < cfg.C0) :
    ∃ κS κB : ℝ,
      0 < κS ∧ 0 < κB ∧
      192*κS*(cfg.vmin+1) ≤ cfg.bexp-cfg.aexp ∧
      192*κB*(cfg.vmin+1) ≤ d-cfg.cexp ∧
      κS ≤ cfg.C0 ∧ κB ≤ cfg.C0 := by
  let DS : ℝ := cfg.bexp-cfg.aexp
  let DB : ℝ := d-cfg.cexp
  let V : ℝ := cfg.vmin+1
  have hDS : 0 < DS := sub_pos.mpr cfg.hab
  have hDB : 0 < DB := sub_pos.mpr hcd
  have hV : 0 < V := by dsimp [V]; linarith [cfg.hv]
  have hC : 0 < cfg.C0 := hc0.trans hC0
  let κS : ℝ := min (DS/(192*V)) (cfg.C0/2)
  let κB : ℝ := min (DB/(192*V)) (cfg.C0/2)
  have hden : 0 < 192*V := by positivity
  have hspos : 0 < κS :=
    lt_min (div_pos hDS hden) (by positivity)
  have hbpos : 0 < κB :=
    lt_min (div_pos hDB hden) (by positivity)
  have hsbd : 192*κS*(cfg.vmin+1) ≤ DS := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (DS/(192*V)) (cfg.C0/2)) hden.le
    have heq : (DS/(192*V))*(192*V) = DS := by
      field_simp [ne_of_gt hden]
    rw [heq] at hh
    dsimp [V] at hh
    nlinarith
  have hbbd : 192*κB*(cfg.vmin+1) ≤ DB := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (DB/(192*V)) (cfg.C0/2)) hden.le
    have heq : (DB/(192*V))*(192*V) = DB := by
      field_simp [ne_of_gt hden]
    rw [heq] at hh
    dsimp [V] at hh
    nlinarith
  have hsC : κS ≤ cfg.C0 := by
    calc
      _ ≤ cfg.C0/2 := min_le_right _ _
      _ ≤ cfg.C0 := by linarith
  have hbC : κB ≤ cfg.C0 := by
    calc
      _ ≤ cfg.C0/2 := min_le_right _ _
      _ ≤ cfg.C0 := by linarith
  exact ⟨κS,κB,hspos,hbpos,
    by simpa only [DS] using hsbd,
    by simpa only [DB] using hbbd,hsC,hbC⟩

/-- No extra κ/group-number hypotheses: for EVERY valid fixed
SourceComparisonFixed434 with 0<c0<C0 and one original BIG
upper exponent cexp<d<1/2, the FULL concrete moving prime
group slice exists for ALL sufficiently large L.
This selects valid Chebyshev rates INSIDE THE PROOF. -/
theorem source_original_eventually_SOURCE03_true_canonical_group_slice434
    (cfg : SourceComparisonFixed434)
    (d vmax c0 : ℝ)
    (hcd : cfg.cexp < d) (hd : d < (1/2:ℝ))
    (hvm : cfg.vmin < vmax)
    (hc0 : 0 < c0) (hC0 : c0 < cfg.C0) :
    ∀ᶠ L : ℝ in atTop,
      ∃ n : ℕ,
        Nonempty (SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0) := by
  obtain ⟨κS,κB,hκSpos,hκBpos,hκS,hκB,hκSC,hκBC⟩ :=
    source_original_SOURCE03_actual_rates_exist434 cfg d c0 hcd hc0 hC0
  exact source_original_eventually_source03_canonical_prime_slice434
    cfg d vmax c0 κS κB hcd hd hvm hc0 hC0
    hκSpos hκBpos hκS hκB hκSC hκBC
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PrimeSliceComparisonBridge -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 360000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 x Y Hp : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
variable (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)

/-- Exact witness that the EXISTING source03 comparison endpoint
uses precisely the verified real prime group fields, not
new independently assigned P_g or V_g. Endpoint fields remain
owned by the original SourceComparisonData434. -/
def SourceOriginalSource03CanonicalFieldsMatch434 : Prop :=
  u.S = z.S ∧ u.Ts = z.Ts ∧ u.Tb = z.Tb ∧
  u.Vs = z.Vs ∧ u.Vsmall = z.Vsmall ∧ u.Vbig = z.Vbig

/-- The completed SourceComparisonData hG union of prime groups
equals the TRUE certified canonical prime-group union, not
an extra arbitrary group alphabet. -/
theorem source_original_canonical_fields_true_G434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    u.G = z.G := by
  rcases h with ⟨hS,hTs,hTb,_,_,_⟩
  rw [u.hG,hS,hTs,hTb]
  rfl

/-- The TRUE arithmetic sum over p in the actual prime group
is definitionally equal to the sum over the physical subtype
Fock/Haar prime alphabet, which SourceComparisonData uses. -/
theorem source_original_canonical_FINSET_subtype_harmonic434
    (s : Finset ℕ) :
    (∑ p : {p : ℕ // p∈s}, (1:ℝ)/(p.val:ℝ)) =
       ∑ p ∈ s, (1:ℝ)/(p:ℝ) := by
  classical
  exact (Finset.sum_subtype s (fun p => Iff.rfl)
    (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm

/-- The missing source-paper pairwise prime-group disjointness
becomes PROVABLE for the original comparison data when its
group fields are provided by the certified true arithmetic
constructor. In particular all three missing hTT/hBB/hTB
conditions are established, not assumed. -/
theorem source_original_canonical_fields_original_group_separation434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    SourceOriginalSource03GroupSeparation434 u := by
  rcases h with ⟨_,hTs,hTb,_,_,_⟩
  refine ⟨?_,?_,?_⟩
  · intro i j p hp hq
    rw [hTs] at hp hq
    by_contra hij
    exact (Finset.disjoint_left.mp
      (z.hSS (some i) (some j) (by simpa using hij))) hp hq
  · intro i j p hp hq
    rw [hTb] at hp hq
    by_contra hij
    exact (Finset.disjoint_left.mp
      (z.hBB i j hij)) hp hq
  · intro i j p hp
    rw [hTs] at hp
    intro hq
    rw [hTb] at hq
    exact (Finset.disjoint_left.mp
      (z.hSB (some i) j)) hp hq

/-- TRUE BIG source masses agree with their entire original
FULL prime intervals, rather than individually assigned Vbig. -/
theorem source_original_canonical_fields_big_harmonic434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    ∀ i, u.Vbig i =
      ∑ p ∈ u.Tb i, (1:ℝ)/(p:ℝ) := by
  rcases h with ⟨_,_,hTb,_,_,hVbig⟩
  intro i
  rw [hTb,hVbig]
  exact z.exact_BIG_harmonic434 i

/-- Actual ORIGINAL source physical group-prime index is
UNIQUE across all of distinguished S, Ts and the FULL
BIG Tb intervals, once the comparison rows are tied to
the proven concrete prime geometry. This is the precise
group-label separation used by C6 arithmetic factorial
atom bounds; it is NOT an extra axiom about random marks. -/
theorem source_original_canonical_fields_ALL_group_index_unique434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    ∀ g h : Unit ⊕ (Fin n ⊕ Fin n), ∀ p : ℕ,
      p ∈ (Sum.elim (fun _ : Unit => u.S)
          (Sum.elim u.Ts u.Tb)) g →
      p ∈ (Sum.elim (fun _ : Unit => u.S)
          (Sum.elim u.Ts u.Tb)) h →
      g=h := by
  exact source_original_source03_all_group_separation434
    cfg x L Y Hp u
    (source_original_canonical_fields_original_group_separation434 z u h)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03SmallGroupPrefactor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- An AUTHENTIC SOURCE03 result, without an auxiliary group
count hypothesis: the ACTUAL moving SMALL groups of the original
SourceComparisonData434 have logarithmic count, at most
cfg.C0*log L, each with genuine number of labelled prime marks
tb(g)≤ cfg.tmax, and true harmonic normalizers
Vbig(g)≥cfg.vmin>0. Consequently their original C6
per-group factorial atom prefactor is <=L^C whenever
C≥cfg.C0*log(cfg.tmax! *
 max(1,cfg.vmin^-1)^cfg.tmax).
This DISCHARGES the factorial-prefactor logarithmic-loss
hypothesis for the actual SMALL groups directly from the
original source data. It does not establish the separate
cross-group prime-support disjointness needed for the
sharp C6 physical atom envelope. -/
theorem source_original_source03_small_group_C6_prefactor_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (C : ℕ) (hL : 1 ≤ L)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ)) :
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset ι) d.ts d.Vsmall ≤ L^C := by
  classical
  let A : ℝ := ((cfg.tmax.factorial:ℕ):ℝ) *
    (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax
  have hFact : (1:ℝ) ≤ ((cfg.tmax.factorial:ℕ):ℝ) := by
    have hNat : 1 ≤ cfg.tmax.factorial := by
      have hp := Nat.factorial_pos cfg.tmax
      omega
    exact_mod_cast hNat
  have hBase : (1:ℝ) ≤ max (1:ℝ) cfg.vmin⁻¹ :=
    le_max_left _ _
  have hPow : (1:ℝ) ≤
      (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ hBase (Nat.zero_le cfg.tmax))
  have hAone : 1 ≤ A := by
    dsimp [A]
    have hh := mul_le_mul hFact hPow
      (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) ≤ ((cfg.tmax.factorial:ℕ):ℝ))
    simpa using hh
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hAone
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hCount :
      ((Finset.univ : Finset ι).card:ℝ) ≤
      cfg.C0*Real.log L := by
    simpa using d.hSmallGroups
  have hGroup :
      ((Finset.univ : Finset ι).card:ℝ)*Real.log A ≤
      (C:ℝ)*Real.log L := by
    calc
      _ ≤ (cfg.C0*Real.log L)*Real.log A :=
        mul_le_mul_of_nonneg_right hCount hLogA
      _ = (cfg.C0*Real.log A)*Real.log L := by ring
      _ ≤ (C:ℝ)*Real.log L := by
        apply mul_le_mul_of_nonneg_right _ hLogL
        exact hExponent
  exact source_original_c6_group_prefactor_log_power434
    (Finset.univ : Finset ι) d.ts d.Vsmall
    cfg.tmax C cfg.vmin L cfg.hv hL
    (by intro g hg; exact d.hts g)
    (by intro g hg; exact d.hVsmall g)
    hGroup
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03AllGroupPrefactors -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The ACTUAL original SOURCE03 simultaneous moving SMALL
and BIG group prime-atom factorial prefactors are jointly
polynomial in L, from source data alone:
 pref(Ts,ts,Vsmall) * pref(Tb,tb,Vbig) <= L^(2*C).
The original source hSmallGroups/hBigGroups, hts/htb,
hVsmall/hVbig and fixed cfg.tmax/cfg.vmin suffice.
No independent group-cardinality or normalizer assumption
is introduced. Group support DISJOINTNESS is a separate
arithmetic requirement of the sharp C6 atom bound,
and is NOT claimed here. -/
theorem source_original_source03_all_group_C6_prefactors_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (C : ℕ) (hL : 1 ≤ L)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ)) :
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset ι) d.ts d.Vsmall *
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset β) d.tb d.Vbig ≤
        L^(2*C) := by
  let small : ℝ :=
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset ι) d.ts d.Vsmall
  let big : ℝ :=
    Green64SourceC6.sourceProductAtomPrefactor
      (Finset.univ : Finset β) d.tb d.Vbig
  have hSmall := source_original_source03_small_group_C6_prefactor_power434
    cfg x L Y Hprime d C hL hExponent
  have hBig := source_original_source03_big_group_C6_prefactor_power434
    cfg x L Y Hprime d C hL hExponent
  have hBigNonneg : 0 ≤ big := by
    dsimp [big,Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (cfg.hv.trans_le (d.hVbig g)).le _)
  have hLNonneg : 0 ≤ L^C :=
    pow_nonneg (by linarith : (0:ℝ) ≤ L) _
  change small*big ≤ L^(2*C)
  calc
    _ ≤ L^C*L^C := mul_le_mul hSmall hBig hBigNonneg hLNonneg
    _ = L^(2*C) := by
      rw [← pow_add]
      congr 1
      omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03LongProductLower -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The TWO ACTUAL source03 prime-list products F1/F2
are at least exp(L^cfg.cexp). This follows from their
genuine NONEMPTY ordered lists, each underlying prime
factor >=exp(L^cfg.cexp), and all factors >=1.
It is the real big-product lower bound used by the C6
minor-circle large-window analysis; it is not an
extra hypothesis on source03 data. -/
theorem source_original_source03_true_long_product_lower434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime) :
    Real.exp (L^cfg.cexp) ≤
      (((∏ i ∈ d.F1, d.p1 i : ℕ):ℝ)) ∧
    Real.exp (L^cfg.cexp) ≤
      (((∏ i ∈ d.F2, d.p2 i : ℕ):ℝ)) := by
  classical
  constructor
  · obtain ⟨i,hi⟩ := d.hF1
    have hOthers (j : ℕ) (hj : j ∈ d.F1) :
        (1:ℝ) ≤ (d.p1 j:ℝ) := by
      exact_mod_cast d.hp1 j hj
    have hBig : (d.p1 i:ℝ) ≤
        ∏ j ∈ d.F1, (d.p1 j:ℝ) := by
      have hh := Finset.prod_le_prod_of_subset_of_one_le₀
        (s := ({i} : Finset ℕ)) (t := d.F1)
        (f := fun j => (d.p1 j:ℝ))
        (Finset.singleton_subset_iff.mpr hi)
        (by
          intro j hj
          have heq : j = i := Finset.mem_singleton.mp hj
          subst j
          exact zero_le_one.trans (hOthers i hi))
        (by intro j hj hnot; exact hOthers j hj)
      simpa using hh
    calc
      _ ≤ (d.p1 i:ℝ) := d.hmin1 i hi
      _ ≤ (∏ j ∈ d.F1, (d.p1 j:ℝ)) := hBig
      _ = (((∏ j ∈ d.F1, d.p1 j : ℕ):ℝ)) := by
        norm_cast
  · obtain ⟨i,hi⟩ := d.hF2
    have hOthers (j : ℕ) (hj : j ∈ d.F2) :
        (1:ℝ) ≤ (d.p2 j:ℝ) := by
      exact_mod_cast d.hp2 j hj
    have hBig : (d.p2 i:ℝ) ≤
        ∏ j ∈ d.F2, (d.p2 j:ℝ) := by
      have hh := Finset.prod_le_prod_of_subset_of_one_le₀
        (s := ({i} : Finset ℕ)) (t := d.F2)
        (f := fun j => (d.p2 j:ℝ))
        (Finset.singleton_subset_iff.mpr hi)
        (by
          intro j hj
          have heq : j = i := Finset.mem_singleton.mp hj
          subst j
          exact zero_le_one.trans (hOthers i hi))
        (by intro j hj hnot; exact hOthers j hj)
      simpa using hh
    calc
      _ ≤ (d.p2 i:ℝ) := d.hmin2 i hi
      _ ≤ (∏ j ∈ d.F2, (d.p2 j:ℝ)) := hBig
      _ = (((∏ j ∈ d.F2, d.p2 j : ℕ):ℝ)) := by
        norm_cast
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03C6DyadSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The ACTUAL original source03 lower prime scales for the
two nonempty labelled products F1/F2 transfer the C6
large-denominator spectral saving to TRUE containing dyads
[M,M+P), [N,N+Q) of size <=M,N, without assuming
the lower dyadic products M,N are enormous directly.
The only still explicit arithmetic growth hypothesis is
exp(L^cfg.cexp) >=4*L^D*r². For fixed D and polynomial r
this is asymptotically true because cexp>0, but the
present lemma does NOT silently assert that asymptotic
comparison at a finite L. -/
theorem source_original_source03_C6_containing_dyad_minor_saving434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (M N P Q r : ℕ) (D : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hR : L^D ≤ (r:ℝ))
    (hDyad1 : (((∏ i ∈ d.F1, d.p1 i : ℕ):ℝ)) ≤
       2*(M:ℝ))
    (hDyad2 : (((∏ i ∈ d.F2, d.p2 i : ℕ):ℝ)) ≤
       2*(N:ℝ))
    (hSuper : 4*L^D*(r:ℝ)^2 ≤ Real.exp (L^cfg.cexp)) :
    ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) /
       ((M:ℝ)*(N:ℝ)) ≤ 5*L^(-D) := by
  have hProducts :=
    source_original_source03_true_long_product_lower434
      cfg x L Y Hprime d
  obtain ⟨hProd1,hProd2⟩ := hProducts
  have hMscale : 2*L^D*(r:ℝ)^2 ≤ (M:ℝ) := by
    have hUpper : Real.exp (L^cfg.cexp) ≤ 2*(M:ℝ) :=
      hProd1.trans hDyad1
    nlinarith [hSuper,hUpper]
  have hRR : (1:ℝ) ≤ (r:ℝ) := by
    have hn : 1 ≤ r := by omega
    exact_mod_cast hn
  have hRRsq : (1:ℝ) ≤ (r:ℝ)^2 := by
    nlinarith [sq_nonneg ((r:ℝ)-1)]
  have hPower : 0 ≤ L^D :=
    Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hSuperN : 2*L^D ≤ 4*L^D*(r:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hRRsq
      (by positivity : 0 ≤ 4*L^D)
    nlinarith
  have hNscale : L^D ≤ (N:ℝ) := by
    have hUpper : Real.exp (L^cfg.cexp) ≤ 2*(N:ℝ) :=
      hProd2.trans hDyad2
    nlinarith [hSuper,hSuperN,hUpper]
  exact source_original_C6_minor_large_product_saving434
    M N P Q r L D hM hN hr hP hQ
    hL hD hR hNscale hMscale
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCircleDenominatorSuperpolynomial -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- EXPLICIT non-circular large-L criterion eliminating the
remaining C262 'exp(L^c) beats L^D r²' premise.
The original source03 has c=cfg.cexp>0 and the Dirichlet
denominator r<=L^Cr. It suffices that L>=4 and the
explicit growth threshold
    (D+2*Cr+1)*(2/c) <= L^(c/2).
The conclusion is the actual arithmetic inequality
    4*L^D*r² <= exp(L^c).
No desired exponential inequality is assumed.
The proof uses the verified Mathlib inequality
    log L <= L^(c/2)/(c/2)
rather than an unquantified 'large enough' slogan. -/
theorem source_original_circle_exponential_denominator_scale434
    (L c D Cr r : ℝ)
    (hL : 4 ≤ L) (hc : 0 < c)
    (hD : 0 ≤ D) (hCr : 0 ≤ Cr)
    (hrr : 0 ≤ r) (hr : r ≤ L^Cr)
    (hThreshold : (D+2*Cr+1)*(2/c) ≤ L^(c/2)) :
    4*L^D*r^2 ≤ Real.exp (L^c) := by
  have hLp : 0 < L := by linarith
  have hOne : 1 ≤ L := by linarith
  have hc2 : 0 < c/2 := by linarith
  let A : ℝ := D+2*Cr+1
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hPow : 0 ≤ L^(c/2) := Real.rpow_nonneg hLp.le _
  have hlog :=
    Real.log_le_rpow_div (x:=L) (ε:=c/2) hLp.le hc2
  have hlog2 : Real.log L ≤ (2/c)*L^(c/2) := by
    calc
      _ ≤ L^(c/2)/(c/2) := hlog
      _ = (2/c)*L^(c/2) := by field_simp
  have hscale : A*Real.log L ≤ L^c := by
    calc
      _ ≤ A*((2/c)*L^(c/2)) :=
        mul_le_mul_of_nonneg_left hlog2 hA
      _ = (A*(2/c))*L^(c/2) := by ring
      _ ≤ L^(c/2)*L^(c/2) :=
        mul_le_mul_of_nonneg_right hThreshold hPow
      _ = L^c := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  have hExpo : L^A ≤ Real.exp (L^c) := by
    rw [Real.rpow_def_of_pos hLp]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hscale)
  have hPowR : r^2 ≤ (L^Cr)^2 :=
    pow_le_pow_left₀ hrr hr 2
  have hDpow : 0 ≤ L^D := Real.rpow_nonneg hLp.le _
  have hPowerCombine :
      L^D*(L^Cr)^2 = L^(D+2*Cr) := by
    calc
      _ = L^D*(L^Cr*L^Cr) := by ring
      _ = L^D*L^(Cr+Cr) := by rw [← Real.rpow_add hLp]
      _ = L^(D+Cr+Cr) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
      _ = L^(D+2*Cr) := by congr 1; ring
  have h2 : 0 ≤ L^(D+2*Cr) := Real.rpow_nonneg hLp.le _
  calc
    4*L^D*r^2 ≤ 4*L^D*(L^Cr)^2 := by
      exact mul_le_mul_of_nonneg_left hPowR (by positivity)
    _ = 4*L^(D+2*Cr) := by rw [mul_assoc,hPowerCombine]
    _ ≤ L*L^(D+2*Cr) :=
      mul_le_mul_of_nonneg_right hL h2
    _ = L^A := by
      dsimp [A]
      conv_rhs => rw [show D+2*Cr+1=(D+2*Cr)+1 by ring,
        Real.rpow_add hLp, Real.rpow_one]
      ring
    _ ≤ Real.exp (L^c) := hExpo
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCircleEventuallySuperpolynomial -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The explicit C263 threshold is actually fulfilled
for ALL sufficiently large L, uniformly for EVERY
positive minor-circle denominator r<=L^Cr.
The threshold L0 depends ONLY on fixed c,D,Cr, not
on the moving prime products, source03 data, r or
the number of marked primes.
Unlike invoking 'superpolynomial' informally,
this proves the needed asymptotic quantification in
the SAME Lean 4.34.1 kernel. -/
theorem source_original_circle_eventual_exp_dominance434
    (c D Cr : ℝ) (hc : 0 < c)
    (hD : 0 ≤ D) (hCr : 0 ≤ Cr) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
      4 ≤ L ∧ ∀ r : ℝ,
        0 ≤ r → r ≤ L^Cr →
          4*L^D*r^2 ≤ Real.exp (L^c) := by
  have hc2 : 0 < c/2 := by linarith
  let threshold : ℝ := (D+2*Cr+1)*(2/c)
  have hEven1 : ∀ᶠ L : ℝ in atTop,
      4 ≤ L := eventually_ge_atTop 4
  have hEven2 : ∀ᶠ L : ℝ in atTop,
      threshold ≤ L^(c/2) :=
    (tendsto_rpow_atTop hc2).eventually (eventually_ge_atTop threshold)
  obtain ⟨L0,hL0⟩ :=
    Filter.eventually_atTop.1 (hEven1.and hEven2)
  refine ⟨L0,?_⟩
  intro L hL
  obtain ⟨hL4,hThreshold⟩ := hL0 L hL
  refine ⟨hL4,?_⟩
  intro r hrr hr
  exact source_original_circle_exponential_denominator_scale434
    L c D Cr r hL4 hc hD hCr hrr hr hThreshold
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAlignedConductorSchedule -/

section

open Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Concrete NATURAL exponent schedule for the new actual comparison
estimates, for every nonnegative requested SQUARED saving Bgoal.
All conductor, Fourier, mesh and retention constraints are simultaneous;
neither Cq nor Cxi re-enters D. This is numerical feasibility, separate
from the original physical prime-interval admissibility hypotheses. -/
theorem source_original_aligned_comparison_MODULUS_exponents434
    (cfg : SourceComparisonFixed434)
    (Bgoal d Cfreq Ck : ℝ) (hGoal : 0 ≤ Bgoal) (hd : 0 ≤ d) (hCk : 0 ≤ Ck) :
    ∃ (Cfactor Cq Cs C4 Cxi : ℕ) (Bsave D H : ℝ),
      0 < Bsave ∧ 0 ≤ D ∧ 0 ≤ H ∧
      Bgoal+(2*d+4)+2 ≤ Bsave ∧
      cfg.C0*Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ) ∧
      Bsave+2*(Cfactor:ℝ) ≤ D ∧
      D+Ck+2 ≤ (Cq:ℝ) ∧
      D+d+2 ≤ (Cs:ℝ) ∧
      (Cs:ℝ)+1 ≤ (C4:ℝ) ∧ Cfreq ≤ (C4:ℝ) ∧
      Bsave+((4*Cq+C4:ℕ):ℝ)+2 ≤ H ∧
      Bsave+H+d+4 ≤ (Cxi:ℝ) := by
  let cost := cfg.C0*Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
    (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax)
  let Cfactor : ℕ := Nat.ceil cost
  let Bsave : ℝ := Bgoal+2*d+6
  let D : ℝ := Bsave+2*(Cfactor:ℝ)
  let Cq : ℕ := Nat.ceil (D+Ck+2)
  let Cs : ℕ := Nat.ceil (D+d+2)
  let C4 : ℕ := Nat.ceil ((Cs:ℝ)+1+max Cfreq 0)
  let H : ℝ := Bsave+((4*Cq+C4:ℕ):ℝ)+2
  let Cxi : ℕ := Nat.ceil (Bsave+H+d+4)
  have hcf : cost ≤ (Cfactor:ℝ) := Nat.le_ceil _
  have hq : D+Ck+2 ≤ (Cq:ℝ) := Nat.le_ceil _
  have hs : D+d+2 ≤ (Cs:ℝ) := Nat.le_ceil _
  have h4 : (Cs:ℝ)+1+max Cfreq 0 ≤ (C4:ℝ) := Nat.le_ceil _
  have hxi : Bsave+H+d+4 ≤ (Cxi:ℝ) := Nat.le_ceil _
  have hMax0 : 0 ≤ max Cfreq 0 := le_max_right _ _
  have hMaxF : Cfreq ≤ max Cfreq 0 := le_max_left _ _
  have hCf0 : (0:ℝ) ≤ Cfactor := Nat.cast_nonneg _
  have hCs0 : (0:ℝ) ≤ Cs := Nat.cast_nonneg _
  have hWidth0 : (0:ℝ) ≤ ((4*Cq+C4:ℕ):ℝ) := Nat.cast_nonneg _
  refine ⟨Cfactor,Cq,Cs,C4,Cxi,Bsave,D,H,?_,?_,?_,?_,hcf,?_,hq,hs,?_,?_,?_,hxi⟩
  all_goals try dsimp [Bsave,D,H]
  all_goals linarith

/-- Original |k|*ceil(L^(D+1)) conductor requirement is compatible with
the new minor budget. Q depends only on the FIXED bound Ck, not on the
individual Fourier mode or on growing labels. -/
theorem eventually_source_original_aligned_conductor_choice434
    (D Ck : ℝ) (Cq : ℕ)
    (hD : 0 ≤ D) (hCk : 0 ≤ Ck) (hCq : D+Ck+2 ≤ (Cq:ℝ)) :
    ∀ᶠ L : ℝ in Filter.atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    0 < Q ∧ L^D ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ L^Cq ∧
      ∀ (k : ℤ), (k.natAbs:ℝ) ≤ L^Ck →
        k.natAbs * Nat.ceil (L^(D+1)) ≤ Q := by
  filter_upwards [Filter.eventually_ge_atTop (5:ℝ)] with L hL5
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hp : 1 ≤ L^(D+Ck+1) := Real.one_le_rpow hL (by linarith)
  have hp0 : 0 < L^(D+Ck+1) := Real.rpow_pos_of_pos hLp _
  let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
  have hLow : 4*L^(D+Ck+1) ≤ (Q:ℝ) := Nat.le_ceil _
  have hUp : (Q:ℝ) ≤ 5*L^(D+Ck+1) := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*L^(D+Ck+1))
    change (Nat.ceil (4*L^(D+Ck+1)):ℝ) ≤ _
    linarith
  have hQp : 0 < (Q:ℝ) := by linarith
  have hNat : 0 < Q := by exact_mod_cast hQp
  have hDlow : L^D ≤ (Q:ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL
      (by linarith : D ≤ D+Ck+1)
    linarith
  have hQupper : (Q:ℝ) ≤ L^Cq := by
    calc
      _ ≤ 5*L^(D+Ck+1) := hUp
      _ ≤ L*L^(D+Ck+1) := mul_le_mul_of_nonneg_right hL5 hp0.le
      _ = L^(D+Ck+2) := by
        nth_rw 1 [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ L^Cq := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hL hCq
  refine ⟨hNat,hDlow,hQupper,?_⟩
  intro k hk
  have hpD : 1 ≤ L^(D+1) := Real.one_le_rpow hL (by linarith)
  have hCeil : (Nat.ceil (L^(D+1)):ℝ) ≤ 2*L^(D+1) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (D+1))
    linarith
  have hProduct : (k.natAbs:ℝ)*(Nat.ceil (L^(D+1)):ℝ) ≤ (Q:ℝ) := by
    calc
      _ ≤ L^Ck*(2*L^(D+1)) :=
        mul_le_mul hk hCeil (Nat.cast_nonneg _) (Real.rpow_nonneg hLp.le _)
      _ = 2*L^(D+Ck+1) := by
        rw [← mul_assoc,mul_comm (L^Ck) 2,mul_assoc,← Real.rpow_add hLp]
        congr 1
        congr 1
        ring
      _ ≤ (Q:ℝ) := by linarith
  exact_mod_cast hProduct

/-- Fixed polynomial conductors eventually lie below every actual
BIG prime, uniformly in all prime labels. This discharges the physical
Q^2<p side condition once the original exponential lower bound holds. -/
theorem eventually_source_original_conductor_below_BIG434
    (Cq : ℕ) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (Q p : ℕ), (Q:ℝ) ≤ L^Cq →
      Real.exp (L^gamma) ≤ (p:ℝ) → Q^2 < p := by
  obtain ⟨L0,hLarge⟩ := source_original_circle_eventual_exp_dominance434
    gamma (2*(Cq:ℝ)) 0 hgamma (by positivity) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop L0] with L hL0
  obtain ⟨hL4,hExp⟩ := hLarge L hL0
  have hLp : 0 < L := by linarith
  have hh := hExp 1 (by norm_num) (by simp)
  have hBound : 4*L^(2*(Cq:ℝ)) ≤ Real.exp (L^gamma) := by simpa using hh
  intro Q p hQ hPrime
  have hQpow : (Q:ℝ)^2 ≤ (L^Cq)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2
  have hPower : (L^Cq)^2 = L^(2*(Cq:ℝ)) := by
    rw [← pow_mul,← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hPower] at hQpow
  have hp : 0 < L^(2*(Cq:ℝ)) := Real.rpow_pos_of_pos hLp _
  have hResult : (Q:ℝ)^2 < (p:ℝ) := by linarith
  exact_mod_cast hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TrueFiveIndexHprime -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The actual source03 five-index ν, global A/B cell,
primitive A/B character term has its OWN correct H'=U_A*U_B
and its full exp(O(log L sqrt L)) upper bound.
The upper BIG-prime and block-count geometry is DERIVED from
original d.hG/d.hGroup/d.hBigGroups, not postulated. -/
theorem source_original_source03_true_five_index_Hprime_upper434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 1 ≤ L)
    (blockA blockB : Finset β) (m Q : ℕ)
    (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hB ν)
    (xi : ℝ)
    (z : Σ ν : SourceOriginalProbePattern434 β m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))))
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q d.Tb d.Vbig hA hB xi) :
    Real.exp (2*(L^cfg.cexp)-((hA z.1)+(hB z.1))) <
      sourceOriginalProbeTrueHprime434 m Q hA hB z ∧
    sourceOriginalProbeTrueHprime434 m Q hA hB z ≤
      Real.exp
        ((2*(cfg.tmax:ℝ)*cfg.C0*Real.log L)*
          L^(1/2:ℝ)) := by
  have hBig : ∀ g ∈ blockA ∪ blockB, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ) ∧
       (p:ℝ) ≤ Real.exp (L^(1/2:ℝ)) := by
    intro g hg p hp
    constructor
    · exact hTbLower g p hp
    · simpa only [Real.sqrt_eq_rpow] using
        source_original_source03_true_big_prime_upper434
          cfg x L Y Hprime d g p hp
  obtain ⟨hLow,hHigh⟩ :=
    source_original_probe_true_Hprime_bounds434
      blockA blockB m Q d.Tb d.Vbig hA hB xi
      L cfg.cexp (1/2:ℝ) (by linarith) hBig hhA hhB z hz
  have hCard :=
    source_original_source03_two_big_block_card_budget434
      cfg x L Y Hprime d blockA blockB m hm hL
  have hPowerNonneg :
      0 ≤ L^(1/2:ℝ) :=
    Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hExponent :
      (((m*(blockA.card+blockB.card):ℕ):ℝ))*L^(1/2:ℝ) ≤
      (2*(cfg.tmax:ℝ)*cfg.C0*Real.log L)*L^(1/2:ℝ) :=
    mul_le_mul_of_nonneg_right hCard hPowerNonneg
  exact ⟨hLow,hHigh.trans (Real.exp_le_exp.mpr hExponent)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TrueFiveIndexCircleScales -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- ALL three exact original circle-scale hypotheses for
every actual source03 pattern+two active GLOBAL cells+two
primitive characters. The two lower U bounds and the
true H'=UA*UB upper growth derive from the real grouped
source data and the canonical active-cell construction,
not a synthetic independent F1/F2 pair. -/
theorem source_original_source03_true_five_index_circle_scales434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 1 ≤ L)
    (blockA blockB : Finset β) (m Q : ℕ)
    (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hA ν ∧ hA ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hB ν ∧ hB ν ≤ 1)
    (xi : ℝ)
    (z : Σ ν : SourceOriginalProbePattern434 β m,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))))
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q d.Tb d.Vbig hA hB xi) :
    let UA := Real.exp ((z.2.1.1:ℝ)*hA z.1)
    let UB := Real.exp ((z.2.2.1:ℝ)*hB z.1)
    let Hcell := sourceOriginalProbeTrueHprime434 m Q hA hB z
    Real.exp (L^cfg.cexp-1) ≤ UA ∧
    Real.exp (L^cfg.cexp-1) ≤ UB ∧
    Hcell = UA*UB ∧
    Hcell ≤ Real.exp (
      (2*(cfg.tmax:ℝ)*cfg.C0*Real.log L)*L^(1/2:ℝ)) := by
  classical
  have hmem := Finset.mem_sigma.mp hz
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
    blockA blockB m := hmem.1
  have hPairs := Finset.mem_product.mp hmem.2
  have hjA : z.2.1.1 ∈
      sourceOriginalProbeActiveCellsA434
        m d.Tb d.Vbig z.1 (hA z.1) xi :=
    (Finset.mem_product.mp hPairs.1).1
  have hjB : z.2.2.1 ∈
      sourceOriginalProbeActiveCellsB434
        m d.Tb d.Vbig z.1 (hB z.1) xi :=
    (Finset.mem_product.mp hPairs.2).1
  have hBounds : ∀ g ∈ blockA ∪ blockB,∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(1/2:ℝ)) := by
    intro g hg p hp
    exact ⟨hTbLower g p hp,by
      simpa only [Real.sqrt_eq_rpow] using
        source_original_source03_true_big_prime_upper434
          cfg x L Y Hprime d g p hp⟩
  have hScA := source_original_probe_active_A_big_scale434
    blockA blockB m z.1 hν d.Tb d.Vbig
    L cfg.cexp (1/2:ℝ) (by linarith) hBounds
    (hA z.1) xi (hhA z.1 hν).1 z.2.1.1 hjA
  have hScB := source_original_probe_active_B_big_scale434
    blockA blockB m z.1 hν d.Tb d.Vbig
    L cfg.cexp (1/2:ℝ) (by linarith) hBounds
    (hB z.1) xi (hhB z.1 hν).1 z.2.2.1 hjB
  have hUA :
      Real.exp (L^cfg.cexp-1) ≤
        Real.exp ((z.2.1.1:ℝ)*hA z.1) :=
    Real.exp_le_exp.mpr (by linarith [hScA.1,(hhA z.1 hν).2])
  have hUB :
      Real.exp (L^cfg.cexp-1) ≤
        Real.exp ((z.2.2.1:ℝ)*hB z.1) :=
    Real.exp_le_exp.mpr (by linarith [hScB.1,(hhB z.1 hν).2])
  obtain ⟨_,hHupper⟩ :=
    source_original_source03_true_five_index_Hprime_upper434
      cfg x L Y Hprime d hL blockA blockB m Q hm
      hTbLower hA hB
      (fun ν hν => (hhA ν hν).1)
      (fun ν hν => (hhB ν hν).1)
      xi z hz
  exact ⟨hUA,hUB,rfl,hHupper⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TwoBigBlockMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- A genuine correction of the group split for the ORIGINAL
source03 major/minor comparison. In the actual manuscript,
the two nonempty comparison probe blocks A and B both live
among BIG prime groups (not small versus big groups).
This theorem applies the already unconditional C6 integer
spectral bound to ANY two disjoint selected BIG group subsets,
with their exact source03 Tb(g), Vbig(g), arbitrary actual
numbers of freed labelled marks per selected group, and
arbitrary mark-dependent complex tests. The original
source d.hBigGroups, cfg.tmax, cfg.vmin imply polynomial
factorial prefactor losses for BOTH subsets.
Required source manuscript group separation is made explicit
through sep, not inferred from the inadequate old record.
Dyadic and integer Dirichlet hypotheses are explicit.
No assertion is made about original ν-index origin, or the
RAW-minus-Knu signed operator; those are separate bridges. -/
theorem source_original_source03_two_big_blocks_C6_minor_L2_log_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (GA GB : Finset β) (hDisjoint : Disjoint GA GB)
    (kA kB : β → ℕ)
    (hkA : ∀ g ∈ GA, kA g ≤ cfg.tmax)
    (hkB : ∀ g ∈ GB, kB g ≤ cfg.tmax)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GA, Fin (kA g.val) => d.Tb z.1.val) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GB, Fin (kB g.val) => d.Tb z.1.val) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
      fun z => d.Tb z.1.val
    let SB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
      fun z => d.Tb z.1.val
    let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.1.val)
    let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.1.val)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    ‖(∑ i ∈ Finset.range P,
       sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta0)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  let A : ℝ := ((cfg.tmax.factorial:ℕ):ℝ) *
    (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax
  have hFact : (1:ℝ) ≤ ((cfg.tmax.factorial:ℕ):ℝ) := by
    have hp : 0 < cfg.tmax.factorial := Nat.factorial_pos _
    exact_mod_cast (by omega : 1 ≤ cfg.tmax.factorial)
  have hBase : (1:ℝ) ≤ max (1:ℝ) cfg.vmin⁻¹ :=
    le_max_left _ _
  have hPow : (1:ℝ) ≤
      (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax :=
    one_le_pow₀ hBase
  have hAone : 1 ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul hFact hPow
      (by norm_num : (0:ℝ) ≤ 1)
      (by exact_mod_cast (Nat.zero_le cfg.tmax.factorial))]
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hAone
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hGALe :
      (GA.card:ℝ) ≤ cfg.C0*Real.log L := by
    calc
      (GA.card:ℝ) ≤ (Fintype.card β:ℝ) := by
        exact_mod_cast Finset.card_le_univ GA
      _ ≤ cfg.C0*Real.log L := d.hBigGroups
  have hGBLe :
      (GB.card:ℝ) ≤ cfg.C0*Real.log L := by
    calc
      (GB.card:ℝ) ≤ (Fintype.card β:ℝ) := by
        exact_mod_cast Finset.card_le_univ GB
      _ ≤ cfg.C0*Real.log L := d.hBigGroups
  have hLogGA :
      (GA.card:ℝ)*Real.log A ≤ (C:ℝ)*Real.log L := by
    calc
      _ ≤ (cfg.C0*Real.log L)*Real.log A :=
        mul_le_mul_of_nonneg_right hGALe hLogA
      _ = (cfg.C0*Real.log A)*Real.log L := by ring
      _ ≤ (C:ℝ)*Real.log L :=
        mul_le_mul_of_nonneg_right hExponent hLogL
  have hLogGB :
      (GB.card:ℝ)*Real.log A ≤ (C:ℝ)*Real.log L := by
    calc
      _ ≤ (cfg.C0*Real.log L)*Real.log A :=
        mul_le_mul_of_nonneg_right hGBLe hLogA
      _ = (cfg.C0*Real.log A)*Real.log L := by ring
      _ ≤ (C:ℝ)*Real.log L :=
        mul_le_mul_of_nonneg_right hExponent hLogL
  have hDisjBig (g : β) (hg : g ∈ GA) (h : β)
      (hh : h ∈ GA) (hne : g ≠ h) :
      Disjoint (d.Tb g) (d.Tb h) := by
    apply Finset.disjoint_left.mpr
    intro p hp hph
    exact hne (sep.hBB g h p hp hph)
  have hDisjBig2 (g : β) (hg : g ∈ GB) (h : β)
      (hh : h ∈ GB) (hne : g ≠ h) :
      Disjoint (d.Tb g) (d.Tb h) := by
    apply Finset.disjoint_left.mpr
    intro p hp hph
    exact hne (sep.hBB g h p hp hph)
  have hRsave : Bsave+(C:ℝ)+(C:ℝ) ≤ D := by
    linarith
  have hresult :=
    source_original_actual_C6_minor_log_power_after_group_budget434
      GA d.Tb kA d.Vbig GB d.Tb kB d.Vbig
      (fun g hg p hp => d.hTbPrime g p hp)
      (fun g hg p hp => d.hTbPrime g p hp)
      (fun g hg h hh hne => hDisjBig g hg h hh hne)
      (fun g hg h hh hne => hDisjBig2 g hg h hh hne)
      (fun g hg => cfg.hv.trans_le (d.hVbig g))
      (fun g hg => cfg.hv.trans_le (d.hVbig g))
      fA fB M N P Q hM hN a r beta0
      hr hcop hbeta hP hQ L D hL hR
      hNlarge hMlarge hMNlarge
      Bsave cfg.tmax C C cfg.vmin cfg.hv
      hkA hkB
      (fun g hg => d.hVbig g)
      (fun g hg => d.hVbig g)
      (by simpa only [A] using hLogGA)
      (by simpa only [A] using hLogGB)
      hRsave
  exact hresult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03TrueNuBigMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- TRUE original SOURCE03 minor-arc C6 bound for the TWO
designated BIG probe blocks of an ACTUAL ν comparison pattern.
Unlike C271 (which accidentally specializes to all SMALL
versus all BIG groups), this matches the manuscript's
comparison structure with A and B both subsets of BIG
groups. Actual selected ν-position products and harmonic
prime measures are reindexed into genuine per-group
independent marks using the separately kernel-proven
index/mass/atom/energy equivalences. Hence arbitrary
complex mark-dependent tests require no spurious product
factorization or independence assumption. hPattern is the
real original two-block pattern membership, not an
assumed equality of minor sums. Dyadic integer/Dirichlet,
group separation from manuscript and quantitative saving
exponent compatibility remain explicit, as they must.
Still not a statement about signed RAW-minus-Kν residual. -/
theorem source_original_source03_true_nu_two_big_minor_L2_log_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    ‖(∑ i ∈ Finset.range P,
       sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta0)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  obtain ⟨hNonA,hSubA,hNonB,hSubB⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m A B).mp hPattern
  let kA : β → ℕ := sourceOriginalProbeChosenGroupCount434 m A
  let kB : β → ℕ := sourceOriginalProbeChosenGroupCount434 m B
  have hkA : ∀ g∈blockA, kA g ≤ cfg.tmax := by
    intro g hg
    exact (source_original_probe_chosen_group_count_le434
      m A g).trans hm
  have hkB : ∀ g∈blockB, kB g ≤ cfg.tmax := by
    intro g hg
    exact (source_original_probe_chosen_group_count_le434
      m B g).trans hm
  let GA : (Σ g : blockA, Fin (kA g.val)) → Finset ℕ :=
    fun z => d.Tb z.1.val
  let GB : (Σ g : blockB, Fin (kB g.val)) → Finset ℕ :=
    fun z => d.Tb z.1.val
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let W : β → ℕ → ℝ := fun g p => (1/(p:ℝ))/(d.Vbig g)
  let muGA : (Σ g : blockA, Fin (kA g.val)) → ℕ → ℝ :=
    fun z p => W z.1.val p
  let muGB : (Σ g : blockB, Fin (kB g.val)) → ℕ → ℝ :=
    fun z p => W z.1.val p
  let muA : A → ℕ → ℝ := fun z p => W z.val.1 p
  let muB : B → ℕ → ℝ := fun z p => W z.val.1 p
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  let eA := sourceOriginalProbeBigGroupedPrimeEquiv434
    m blockA A hSubA d.Tb
  let eB := sourceOriginalProbeBigGroupedPrimeEquiv434
    m blockB B hSubB d.Tb
  let fGA : SourceOriginalGramPrimeTuple434 GA → ℂ :=
    fun v => fA (eA v)
  let fGB : SourceOriginalGramPrimeTuple434 GB → ℂ :=
    fun v => fB (eB v)
  have hAtomA (n : ℕ) :
      sourceOriginalPhysicalProductAtomCoefficient434
        GA muGA fGA n =
      sourceOriginalPhysicalProductAtomCoefficient434
        SA muA fA n := by
    exact source_original_probe_grouped_product_atom_coefficient_eq434
      m blockA A hSubA d.Tb W fA n
  have hAtomB (n : ℕ) :
      sourceOriginalPhysicalProductAtomCoefficient434
        GB muGB fGB n =
      sourceOriginalPhysicalProductAtomCoefficient434
        SB muB fB n := by
    exact source_original_probe_grouped_product_atom_coefficient_eq434
      m blockB B hSubB d.Tb W fB n
  have hEnergyA :
      (∑ v : SourceOriginalGramPrimeTuple434 GA,
        sourceOriginalGramPrimeMass434 GA muGA v*‖fGA v‖^2) = EA := by
    exact source_original_probe_grouped_physical_energy_eq434
      m blockA A hSubA d.Tb W fA
  have hEnergyB :
      (∑ v : SourceOriginalGramPrimeTuple434 GB,
        sourceOriginalGramPrimeMass434 GB muGB v*‖fGB v‖^2) = EB := by
    exact source_original_probe_grouped_physical_energy_eq434
      m blockB B hSubB d.Tb W fB
  have hBigResult :=
    source_original_source03_two_big_blocks_C6_minor_L2_log_power434
      cfg x L Y Hprime d sep
      blockA blockB hDisjoint kA kB hkA hkB
      fGA fGB M N P Q hM hN a r beta0
      hr hcop hbeta hP hQ D Bsave hL hR
      hNlarge hMlarge hMNlarge C hExponent hSaving
  change
    ‖(∑ i ∈ Finset.range P,
       sourceOriginalPhysicalProductAtomCoefficient434 GA muGA fGA (M+i) *
       (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 GB muGB fGB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta0)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
      125*
        ((∑ v : SourceOriginalGramPrimeTuple434 GA,
          sourceOriginalGramPrimeMass434 GA muGA v*‖fGA v‖^2)*
         (∑ v : SourceOriginalGramPrimeTuple434 GB,
          sourceOriginalGramPrimeMass434 GB muGB v*‖fGB v‖^2))*
        L^(-Bsave) at hBigResult
  change
    ‖(∑ i ∈ Finset.range P,
       sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta0)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
       125*(EA*EB)*L^(-Bsave)
  calc
    _ = ‖(∑ i ∈ Finset.range P,
       sourceOriginalPhysicalProductAtomCoefficient434 GA muGA fGA (M+i) *
       (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 GB muGB fGB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta0)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 := by
      apply congrArg (fun z : ℂ => ‖z‖^2)
      apply Finset.sum_congr rfl
      intro i hi
      rw [hAtomA]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hAtomB]
    _ ≤ 125*
        ((∑ v : SourceOriginalGramPrimeTuple434 GA,
          sourceOriginalGramPrimeMass434 GA muGA v*‖fGA v‖^2)*
         (∑ v : SourceOriginalGramPrimeTuple434 GB,
          sourceOriginalGramPrimeMass434 GB muGB v*‖fGB v‖^2))*
        L^(-Bsave) := hBigResult
    _ = 125*(EA*EB)*L^(-Bsave) := by
      rw [hEnergyA,hEnergyB]
end Green64Analytic.CorrelationSquare

end

