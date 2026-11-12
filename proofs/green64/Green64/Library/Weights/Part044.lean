module

public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part041
public import Green64.Library.Weights.Part012
public import Mathlib.Tactic
public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part033
public import Mathlib.Data.Fintype.BigOperators
public import Green64.Library.Weights.Part018
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

/-!
# Weights / Part044

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceSharedActualDefectWeighted -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- A genuinely bounded complex test on the actual shared product law:
the omitted dirty expectation costs its exact missing probability mass. -/
theorem source_shared_dirty_weighted_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (hmass : ∀ i, ∑ p ∈ S i, mu i p = 1)
    (clean : (ι → ℕ) → Prop) [DecidablePred clean]
    (K : (ι → ℕ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ a ∈ Fintype.piFinset S, ‖K a‖ ≤ B) :
    ‖∑ a ∈ Fintype.piFinset S,
        if clean a then (0:ℂ)
        else (sourceSharedLaw434 mu a:ℂ)*K a‖ ≤
      B*(1-∑ a ∈ Fintype.piFinset S,
        if clean a then sourceSharedLaw434 mu a else 0) := by
  classical
  have hnonneg (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S) :
      0 ≤ sourceSharedLaw434 mu a :=
    source_shared_law_nonneg434 S mu hmu a ha
  calc
    _ ≤ ∑ a ∈ Fintype.piFinset S,
        ‖if clean a then (0:ℂ) else (sourceSharedLaw434 mu a:ℂ)*K a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Fintype.piFinset S,
        if clean a then 0 else sourceSharedLaw434 mu a*B := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · simp
      · simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hnonneg a ha)] using
          mul_le_mul_of_nonneg_left (hK a ha) (hnonneg a ha)
    _ = B*(1-∑ a ∈ Fintype.piFinset S,
        if clean a then sourceSharedLaw434 mu a else 0) := by
      calc
        _ = (∑ a ∈ Fintype.piFinset S,
            (sourceSharedLaw434 mu a -
              if clean a then sourceSharedLaw434 mu a else 0))*B := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : clean a <;> simp [h]
        _ = _ := by
          rw [Finset.sum_sub_distrib, source_shared_law_total434 S mu hmass]
          ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyExpectationSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- True discarded shared-label expectation, with arbitrary complex
coupling K and explicit polynomial source envelope B*L^C.
The clean predicate includes both endpoint prime divisors and aux slots;
the independent law is NOT conditioned on pairwise distinctness. -/
theorem eventually_source_actual_shared_weighted_dirty_saving434
    (a v Cs Ca C D B : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (V : ι → ℝ) (w wp : ℕ)
      (aux : Finset ℕ) (K : (ι → ℕ) → ℂ),
    0 < w → 0 < wp → (w:ℝ) ≤ Real.exp (2*L) →
    (wp:ℝ) ≤ Real.exp (2*L) →
    (Fintype.card ι:ℝ) ≤ Cs*Real.log L →
    (aux.card:ℝ) ≤ Ca*Real.log L →
    (∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) →
    (∀ i,v ≤ V i) →
    (∀ i p,p ∈ S i → Real.exp (L^a) ≤ (p:ℝ)) →
    (∀ t ∈ Fintype.piFinset S, ‖K t‖ ≤ B*L^C) →
    ‖∑ t ∈ Fintype.piFinset S,
      if sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux) t
      then (0:ℂ)
      else (sourceSharedLaw434
        (fun i => sourcePrimeSharedAtom434 (V i)) t:ℂ)*K t‖ ≤
    B*L^(-D) := by
  filter_upwards [eventually_source_actual_shared_defect_saving434
      a v Cs Ca (D+C) ha hv hCs hCa,
    eventually_ge_atTop (1:ℝ)] with L hDefect hL
  intro ι _ _ S V w wp aux K hw hwp hwSize hwpSize hslots haux
    hV hVmin hPmin hK
  classical
  let μ : ι → ℕ → ℝ := fun i => sourcePrimeSharedAtom434 (V i)
  have hmu : ∀ i p, p ∈ S i → 0 ≤ μ i p := by
    intro i p hp
    have hVp : 0 < V i := hv.trans_le (hVmin i)
    have hpR : (0:ℝ) < p :=
      (Real.exp_pos _).trans_le (hPmin i p hp)
    dsimp only [μ,sourcePrimeSharedAtom434]
    positivity
  have hmass : ∀ i, ∑ p ∈ S i, μ i p = 1 := by
    intro i
    exact source_prime_shared_atom_total434 (S i) (V i)
      (hV i) (hv.trans_le (hVmin i)).ne'
  let good : (ι → ℕ) → Prop :=
    sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux)
  have hBasic := source_shared_dirty_weighted_mass434
    S μ hmu hmass good K (B*L^C)
    (mul_nonneg hB (Real.rpow_nonneg (by linarith : 0 ≤ L) C)) hK
  have hDef := hDefect S V w wp aux hw hwp hwSize hwpSize hslots haux
    hV hVmin hPmin
  have hLpos : 0 < L := by linarith
  have hPower : L^C * L^(-(D+C)) = L^(-D) := by
    rw [←Real.rpow_add hLpos]
    congr 1
    ring
  exact hBasic.trans (by
    calc
      B*L^C*(1-∑ t ∈ Fintype.piFinset S,
        if good t then sourceSharedLaw434 μ t else 0)
        ≤ B*L^C*L^(-(D+C)) :=
          mul_le_mul_of_nonneg_left hDef
            (mul_nonneg hB (Real.rpow_nonneg hLpos.le C))
      _ = B*L^(-D) := by rw [mul_assoc,hPower])
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedArbitraryEnvelopeSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The actual shared-draw dirty loss works for a position-dependent
envelope B(w,w'), which may be MUCH larger than every log power.
The source saving is uniform in B, so one can sum envelopes later
using genuine endpoint L2 moments instead of a false pointwise cap. -/
theorem eventually_source_actual_shared_arbitrary_envelope434
    (a v Cs Ca D : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (V : ι → ℝ) (w wp : ℕ)
      (aux : Finset ℕ) (K : (ι → ℕ) → ℂ) (B : ℝ),
    0 ≤ B → 0 < w → 0 < wp →
    (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
    (Fintype.card ι:ℝ) ≤ Cs*Real.log L →
    (aux.card:ℝ) ≤ Ca*Real.log L →
    (∀ i,V i=∑ p ∈ S i,1/(p:ℝ)) →
    (∀ i,v ≤ V i) →
    (∀ i p,p ∈ S i → Real.exp (L^a) ≤ (p:ℝ)) →
    (∀ t ∈ Fintype.piFinset S, ‖K t‖ ≤ B) →
    ‖∑ t ∈ Fintype.piFinset S,
      if sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux) t
      then (0:ℂ)
      else (sourceSharedLaw434
        (fun i => sourcePrimeSharedAtom434 (V i)) t:ℂ)*K t‖ ≤
    B*L^(-D) := by
  filter_upwards [eventually_source_actual_shared_defect_saving434
    a v Cs Ca D ha hv hCs hCa,
    eventually_ge_atTop (1:ℝ)] with L hDefect hL
  intro ι _ _ S V w wp aux K B hB hw hwp hwSize hwpSize hSlots haux
    hV hVmin hPmin hK
  classical
  let μ : ι → ℕ → ℝ := fun i => sourcePrimeSharedAtom434 (V i)
  have hmu : ∀ i p, p ∈ S i → 0 ≤ μ i p := by
    intro i p hp
    have hVp : 0 < V i := hv.trans_le (hVmin i)
    have hpR : (0:ℝ) < p :=
      (Real.exp_pos _).trans_le (hPmin i p hp)
    dsimp only [μ,sourcePrimeSharedAtom434]
    positivity
  have hmass : ∀ i, ∑ p ∈ S i, μ i p = 1 := by
    intro i
    exact source_prime_shared_atom_total434 (S i) (V i)
      (hV i) (hv.trans_le (hVmin i)).ne'
  let good : (ι → ℕ) → Prop :=
    sourceSharedClean434 (fun _ => sourceSharedForbidden434 w wp aux)
  have hBasic := source_shared_dirty_weighted_mass434
    S μ hmu hmass good K B hB hK
  have hDef := hDefect S V w wp aux
    hw hwp hwSize hwpSize hSlots haux hV hVmin hPmin
  exact hBasic.trans (mul_le_mul_of_nonneg_left hDef hB)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedMarkedTests -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem source_shared_extract_assemble434 {M t : ℕ} (E : Finset (Fin M))
    (s : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E}) (b : Fin t → ℕ) :
    (fun j => sourceSharedAssemble434 E s e b (e j))=b := by
  funext j
  simp only [sourceSharedAssemble434,dif_neg (e j).property]
  change b (e.symm (e j))=b j
  exact congrArg b (e.symm_apply_apply j)

theorem source_big_mark_prefactor_star434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (t : G → ℕ) (q : ℝ) (V : G → ℝ) (n : ℕ) :
    star (bigMarkPrefactor P t q V n)=bigMarkPrefactor P t q V n := by
  simp only [bigMarkPrefactor,star_prod,Complex.star_def,map_natCast,
    Complex.conj_ofReal]

/-- The two genuine marked-list sums become the exact endpoint weights,
with conjugation on the first test and no normalization factor lost. -/
theorem source_two_marked_tests434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (t : G → ℕ) (q : ℝ) (V : G → ℝ)
    (b1 b2 : (∀ g,Fin (t g) → ℕ) → ℂ) (w wp : ℕ) :
    bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
      (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,star (b1 a)*b2 b) =
    star (actualBigMarkDecoration P t q V b1 w)*actualBigMarkDecoration P t q V b2 wp := by
  simp only [actualBigMarkDecoration,star_mul,source_big_mark_prefactor_star434,
    star_sum,←Finset.mul_sum,←Finset.sum_mul]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCleanFactoredPairing -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ACTUAL separable comparison tests on unshared endpoint marks.
The original full lists are restricted at their exact source slot indices;
the result is the same two marked endpoint weights used by C's analysis. -/
theorem source_original_clean_factored_pairing434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ)
    (J ell : ℕ) (C : G → Finset (Fin J))
    (shared : ∀ g, sourceOriginalSharedSlots434 J ell (C g) → ℕ)
    (w wp : ℕ) (q : ℝ) (V : G → ℝ) (hq : 0 < q)
    (hP : ∀ g p,p ∈ P g → p.Prime) (hs : ∀ g i,shared g i ∈ P g)
    (hInj : ∀ g,Function.Injective (shared g))
    (hAvoid : ∀ g i,¬shared g i ∣ w) (hAvoid' : ∀ g i,¬shared g i ∣ wp)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (b1 b2 : (∀ g,Fin (ell+(C g).card) → ℕ) → ℂ) :
    let E := fun g => sourceOriginalSharedSlots434 J ell (C g)
    let R := fun g => sourceSharedPrimeSet434 (E g) (shared g)
    let d := ∏ p ∈ Finset.univ.biUnion R,p
    let t := fun g => ell+(C g).card
    let e := fun g => sourceOriginalFreeSlotEquiv434 J ell (C g)
    (∏ g,((V g:ℂ)^(J+ell))⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*(d:ℂ)⁻¹*
      ((sourcePhysicalGroupedHalf434 P (J+ell) q (d*w))^2:ℝ)*
      ((sourcePhysicalGroupedHalf434 P (J+ell) q (d*wp))^2:ℝ)*
      (∑ a ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P (J+ell) E shared wp,
          star (b1 (fun g j => a g (e g j)))*b2 (fun g j => b g (e g j))) =
    (∏ g,∏ i : E g,((V g:ℂ)*(shared g i:ℂ))⁻¹)*
      star (actualBigMarkDecoration P t q V b1 w)*actualBigMarkDecoration P t q V b2 wp := by
  classical
  dsimp only
  let E := fun g => sourceOriginalSharedSlots434 J ell (C g)
  let t := fun g => ell+(C g).card
  let e := fun g => sourceOriginalFreeSlotEquiv434 J ell (C g)
  let K := fun a b : G → Fin (J+ell) → ℕ =>
    star (b1 (fun g j => a g (e g j)))*b2 (fun g j => b g (e g j))
  have h := source_original_clean_global_pairing434 P J ell C shared w wp q V hq
    hP hs hInj hAvoid hAvoid' hDisj K
  dsimp only at h
  have hK (a b : ∀ g,Fin (t g) → ℕ) :
      K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (a g))
        (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g)) = star (b1 a)*b2 b := by
    have hA : (fun g j => sourceSharedAssemble434 (E g) (shared g) (e g) (a g) (e g j))=a := by
      funext g
      exact source_shared_extract_assemble434 (E g) (shared g) (e g) (a g)
    have hB : (fun g j => sourceSharedAssemble434 (E g) (shared g) (e g) (b g) (e g j))=b := by
      funext g
      exact source_shared_extract_assemble434 (E g) (shared g) (e g) (b g)
    dsimp only [K]
    rw [hA,hB]
  change _ = (∏ g,∏ i : E g,((V g:ℂ)*(shared g i:ℂ))⁻¹)*
    bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
      K (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (a g))
        (fun g => sourceSharedAssemble434 (E g) (shared g) (e g) (b g))) at h
  simp_rw [hK] at h
  calc
    _ = (∏ g,∏ i : E g,((V g:ℂ)*(shared g i:ℂ))⁻¹)*
        bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
        (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,star (b1 a)*b2 b) := h
    _ = (∏ g,∏ i : E g,((V g:ℂ)*(shared g i:ℂ))⁻¹)*
        (bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
        (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,star (b1 a)*b2 b)) := by ring
    _ = _ := by rw [source_two_marked_tests434]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedPositiveMarkedRow -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Absolute bound by the genuine POSITIVE marked endpoint masses.
This retains the dependence on w and w' which was lost in the coarse
uniform K^(#groups) bound. Crucially the actual complex-valued mark
tests may cancel and cannot replace the positive all-ones count. -/
theorem source_actual_dirty_two_row_positive_majorant434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
      ‖F a b‖ ≤ B) :
    ‖bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
      (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b)‖ ≤
      B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ := by
  have hRows := source_global_dirty_two_row_bound434
    P M E s t e w wp hP hs hDisj F B hB hF
  let nw : ℝ := (bigMarkLists P t w).card
  let np : ℝ := (bigMarkLists P t wp).card
  have hOne (n : ℕ) :
      ‖actualBigMarkDecoration P t q V (fun _ => 1) n‖ =
        ‖bigMarkPrefactor P t q V n‖*(bigMarkLists P t n).card := by
    simp only [actualBigMarkDecoration, Finset.sum_const_zero]
    simp [norm_mul, Complex.norm_natCast]
  calc
    _ = ‖bigMarkPrefactor P t q V w‖*
        ‖bigMarkPrefactor P t q V wp‖*
          ‖∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
            ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b‖ := by
              rw [norm_mul,norm_mul]
    _ ≤ ‖bigMarkPrefactor P t q V w‖*
        ‖bigMarkPrefactor P t q V wp‖*(B*nw*np) :=
      mul_le_mul_of_nonneg_left hRows
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ := by
      rw [hOne,hOne]
      dsimp only [nw,np]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceWeightedEndpointBridge -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

noncomputable def sourceWeightedFullPeelingResidualFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (Lambda : ℕ → ℂ) : C(AddCircle (1:ℝ),ℂ) :=
  let groupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => Lambda n * literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart groupPrimes)
        (sourcePeelingError S Vs
          (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
          (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k))
        primeSlot α c q χ σ₀ σ₁ n)


/-- Original physical endpoint Fourier polynomial *before* small-prime
peeling. Exact outside core, full source marks and parity, no
squarefree restriction and no coefficient renormalization. -/
noncomputable def sourceWeightedFullMarkedFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (Lambda : ℕ → ℂ) :
    C(AddCircle (1:ℝ),ℂ) :=
  let allGroupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => Lambda n * literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
        primeSlot α c q χ σ₀ σ₁ n)

/-- Exactly the endpoint after extracting the designated small-group
mark. The original core and parity stay at n, while only the remaining
small-prime marked weight is evaluated at n/p. -/
noncomputable def sourceWeightedPeeledMarkedFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (Lambda : ℕ → ℂ) :
    C(AddCircle (1:ℝ),ℂ) :=
  let allGroupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => Lambda n * literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (fun n => ((1/Vs:ℝ):ℂ) *
           ∑ p ∈ smallPrimeSupport S n,
             literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k (n/p))
        primeSlot α c q χ σ₀ σ₁ n)

/-- Exact, global *source physical* Fourier identity:
raw endpoint = peeled endpoint + full exceptional square residual.
All frequency centers and signs are allowed. No estimates or
squarefree hypotheses enter this algebraic identity. -/
theorem source_weighted_full_marked_fourier_eq_peeled_add_error
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (Lambda : ℕ → ℂ)
    (theta : AddCircle (1:ℝ)) :
    sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ Lambda theta =
    sourceWeightedPeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ Lambda theta +
    sourceWeightedFullPeelingResidualFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ Lambda theta := by
  classical
  simp only [sourceWeightedFullMarkedFourier,sourceWeightedPeeledMarkedFourier,
     sourceWeightedFullPeelingResidualFourier,source_nat_fourier_literal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sourceEndpoint,sourcePeelingError]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceWeightedFourierLocalization -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1700000

/-- Exact finite Fourier localization at the genuine support scale. -/
theorem source_nat_fourier_cutoff434 (N M : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n, M < n → a n = 0) :
    sourceNatFourierPoly (Finset.Icc 1 N) a =
      sourceNatFourierPoly (Finset.Icc 1 (min N M)) a := by
  ext theta
  rw [source_nat_fourier_literal,source_nat_fourier_literal]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (min_le_left _ _)⟩
  · intro n hn hnot
    have hMN : M < n := by
      simp only [Finset.mem_Icc] at hn hnot
      omega
    simp only [ha n hMN,zero_mul]

/-- The smooth original cutoff itself vanishes past ceil(A*Y),
so localization also applies to FULL and square-error coefficients. -/
theorem source_smooth_weight_cutoff434 (Y A : ℝ) (hY : 0 < Y)
    (psi : ℝ → ℂ) (phase : ℕ → ℂ)
    (hUpper : ∀ u, psi u ≠ 0 → u ≤ A) :
    ∀ n : ℕ, Nat.ceil (A*Y) < n → psi ((n:ℝ)/Y)*phase n = 0 := by
  intro n hn
  have hGt : A*Y < (n:ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
  have hz : psi ((n:ℝ)/Y) = 0 := by
    by_contra hNZ
    have hle := (div_le_iff₀ hY).mp (hUpper _ hNZ)
    exact (not_lt_of_ge hle) hGt
  simp only [hz,zero_mul]

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable (N M q : ℕ) (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (Lambda : ℕ → ℂ) (hLambda : ∀ n, M < n → Lambda n = 0)

include hLambda

theorem source_weighted_full_fourier_localize434 :
    sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda =
    sourceWeightedFullMarkedFourier (min N M) q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda := by
  unfold sourceWeightedFullMarkedFourier
  apply source_nat_fourier_cutoff434
  intro n hn
  simp only [hLambda n hn,zero_mul]

theorem source_weighted_peeled_fourier_localize434 :
    sourceWeightedPeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda =
    sourceWeightedPeeledMarkedFourier (min N M) q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda := by
  unfold sourceWeightedPeeledMarkedFourier
  apply source_nat_fourier_cutoff434
  intro n hn
  simp only [hLambda n hn,zero_mul]

theorem source_weighted_error_fourier_localize434 :
    sourceWeightedFullPeelingResidualFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda =
    sourceWeightedFullPeelingResidualFourier (min N M) q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda := by
  unfold sourceWeightedFullPeelingResidualFourier
  apply source_nat_fourier_cutoff434
  intro n hn
  simp only [hLambda n hn,zero_mul]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupWeightedError -/

section

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Polynomially bounded Fourier/Mellin cutoff multipliers cost only
their squared norm in the *full physical* square-exception bound,
even though they can redistribute Fourier energy across arcs.
No unweighted-local-energy implication is assumed here. -/
theorem source_full_weighted_original_group_peeling_beta_energy434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        (∀ p ∈ S, p.Prime) →
        (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
        (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
        (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
        (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
        ∀ (N q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (α cseq Lambda : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C M L a D center H Vplus : ℝ),
          0 ≤ A → 0 ≤ C → 0 ≤ M →
          (∀ m, ‖α m‖ ≤ A) →
          (∀ r, ‖cseq r‖ ≤ C) →
          (∀ n ∈ Finset.Icc 1 N, ‖Lambda n‖ ≤ M) →
          1 ≤ N →
          (∀ p ∈ S, Real.exp (L^a) ≤ (p:ℝ)) →
          (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Vplus →
          1 ≤ L → 0 ≤ D →
          Real.log (N:ℝ) ≤ D*L →
          2 ≤ H →
          let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
          (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
            ‖sourceWeightedFullPeelingResidualFourier
              N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
              primeSlot Ptwist α cseq χ σ₀ σ₁ Lambda
              ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
            M^2*Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
              (N:ℝ)*(1+Real.log (N:ℝ))^16*
              Real.exp (-(L^a)) := by
  obtain ⟨K,hK,hWeight⟩ :=
    source_literal_weight_uniform_all_groups
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB
    N q primeSlot Ptwist α cseq Lambda χ
    σ₀ σ₁ A C M L a D center H Vplus
    hA hC hM hα hc hLambda hN hmin hHarmonic hL hD hLog hH
  dsimp only
  let G : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  let Wh : ℕ → ℂ := literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1)
  let Wl : ℕ → ℂ := literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k
  let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
  let Err : ℕ → ℂ := fun n =>
    sourceEndpoint (sourceOutsidePart G)
      (sourcePeelingError S Vs Wh Wl)
      primeSlot α cseq q χ σ₀ σ₁ n
  let FullErr : ℕ → ℂ := fun n =>
    Lambda n * literalSourceParity Ptwist n * Err n
  have hGroups : S ⊆ G := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk' : k ≤ tmax := by omega
  have hWh : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ‖Wh n‖ ≤ B := by
    intro n hn
    exact hWeight S Ts Tb Vs Vsmall Vbig ts tb b (k+1) n
      hk hVs hts htb hVsmall hVbig hb
  have hWl : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ∀ p ∈ smallPrimeSupport S n, ‖Wl (n/p)‖ ≤ B := by
    intro n hn p hp
    exact hWeight S Ts Tb Vs Vsmall Vbig ts tb b k (n/p)
      hk' hVs hts htb hVsmall hVbig hb
  have hMass := source_peeling_original_group_square_union434
    G S Wh Wl primeSlot α cseq N q χ
    σ₀ σ₁ A C B Vs vmin L a D Vplus
    hA hC hB hα hc hN hGroups hS
    hmin hHarmonic hL hD hv hVs hLog hWh hWl
  have hSupport : sourceSquareExceptionalSupport N S ⊆ Finset.Icc 1 N :=
    Finset.filter_subset _ _
  have hZero : ∀ n ∈ Finset.Icc 1 N,
      n ∉ sourceSquareExceptionalSupport N S → Err n = 0 := by
    intro n hn hGood
    exact source_physical_peeling_zero_off_exception
      N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k n G
      primeSlot α cseq χ σ₀ σ₁
      hS hTs hDisjS hTb hDisjB hn hGood
  have hFullZero : ∀ n ∈ Finset.Icc 1 N,
      n ∉ sourceSquareExceptionalSupport N S → FullErr n = 0 := by
    intro n hn hGood
    simp [FullErr,hZero n hn hGood]
  have hMassSupport :
      (∑ n ∈ Finset.Icc 1 N, ‖FullErr n‖^2) =
      (∑ n ∈ sourceSquareExceptionalSupport N S, ‖FullErr n‖^2) := by
    symm
    exact Finset.sum_subset hSupport (by
      intro n hn hGood
      rw [hFullZero n hn hGood]
      simp)
  have hCutSquare : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ‖FullErr n‖^2 ≤ M^2*‖Err n‖^2 := by
    intro n hn
    have hBound := hLambda n (hSupport hn)
    have hquad : ‖Lambda n‖^2 ≤ M^2 := by
      have hmnorm : 0 ≤ ‖Lambda n‖ := norm_nonneg _
      nlinarith
    have hMod : ‖FullErr n‖^2 = ‖Lambda n‖^2*‖Err n‖^2 := by
      dsimp [FullErr]
      rw [norm_mul,norm_mul,literal_source_parity_norm_one]
      ring
    rw [hMod]
    exact mul_le_mul_of_nonneg_right hquad (sq_nonneg _)
  have hWeightedMass :
      (∑ n ∈ Finset.Icc 1 N, ‖FullErr n‖^2) ≤
        M^2 * (Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
          (N:ℝ)*(1+Real.log (N:ℝ))^16*
          Real.exp (-(L^a))) := by
    rw [hMassSupport]
    calc
      _ ≤ ∑ n ∈ sourceSquareExceptionalSupport N S, M^2*‖Err n‖^2 :=
        Finset.sum_le_sum (fun n hn => hCutSquare n hn)
      _ = M^2 * ∑ n ∈ sourceSquareExceptionalSupport N S,
            ‖Err n‖^2 := by rw [Finset.mul_sum]
      _ ≤ M^2 * (Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
           (N:ℝ)*(1+Real.log (N:ℝ))^16*Real.exp (-(L^a))) :=
        mul_le_mul_of_nonneg_left hMass (sq_nonneg _)
  have hFourier := source_beta_window_fourier_energy_le_coeff_l2
    (Finset.Icc 1 N) FullErr center H hH
  have hLeft : (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
      ‖sourceWeightedFullPeelingResidualFourier
        N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
        primeSlot Ptwist α cseq χ σ₀ σ₁ Lambda
        ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
       M^2 * (Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
          (N:ℝ)*(1+Real.log (N:ℝ))^16*Real.exp (-(L^a))) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖FullErr n‖^2 := by
        simpa only [sourceWeightedFullPeelingResidualFourier,
          FullErr,Err,G,Wh,Wl] using hFourier
      _ ≤ _ := hWeightedMass
  convert hLeft using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullGlobal -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 4500000

/-- Full, unpeeled source endpoint global L2 bound. All marked weights,
parity multiplicities and the invariant prime-slot core are literal.
No discrepancy is required, so this applies to the second endpoint. -/
theorem source_original_full_fourier_global434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax → vmin ≤ Vs →
        (∀ g, ts g ≤ tmax) → (∀ g, tb g ≤ tmax) →
        (∀ g, vmin ≤ Vsmall g) → (∀ g, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (N q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (alpha c Lambda : ℕ → ℂ) (chi : DirichletCharacter ℂ q)
          (s0 s1 A C M : ℝ),
          0 ≤ A → 0 ≤ C → 0 ≤ M →
          (∀ m, ‖alpha m‖ ≤ A) → (∀ r, ‖c r‖ ≤ C) →
          (∀ n ∈ Finset.Icc 1 N, ‖Lambda n‖ ≤ M) →
          (∫ θ : AddCircle (1:ℝ),
            ‖sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k primeSlot Ptwist alpha c chi s0 s1 Lambda θ‖^2
            ∂AddCircle.haarAddCircle) ≤
          (A*C*(M*K^(Fintype.card ι+Fintype.card β+1)))^2*
            (N:ℝ)*(1+Real.log (N:ℝ))^16 := by
  obtain ⟨K,hK,hWeight⟩ := source_literal_weight_uniform_all_groups
    q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    N q primeSlot Ptwist alpha c Lambda chi s0 s1 A C M hA hC hM hAlpha hCseq hLambda
  let G := S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪ ((Finset.univ : Finset β).biUnion Tb)
  let W := literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1)
  let B := K^(Fintype.card ι+Fintype.card β+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : ∀ n ∈ Finset.Icc 1 N, ‖W n‖ ≤ B := fun n _ =>
    hWeight S Ts Tb Vs Vsmall Vbig ts tb b (k+1) n hk hVs hts htb hVsmall hVbig hb
  have hMom := source_original_endpoint_global_square434 G W Lambda
    (literalSourceParity Ptwist) primeSlot alpha c N q chi s0 s1 A C B M
    hA hC hB hM hAlpha hCseq hW hLambda
    (fun n _ => literal_source_parity_norm_one Ptwist n)
  let coeff := fun n => Lambda n*literalSourceParity Ptwist n*
    sourceEndpoint (sourceOutsidePart G) W primeSlot alpha c q chi s0 s1 n
  have hFourier := source_nat_fourier_arc_energy (Finset.Icc 1 N) coeff Set.univ
  simp only [Measure.restrict_univ] at hFourier
  exact hFourier.trans hMom
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyMarkedBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL q-damped, V-normalized marked count is uniformly bounded.
The all-ones mark test makes the entire count literal: not a surrogate mass. -/
theorem source_actual_prefactor_mark_count_bound434
    (q vmin : ℝ) (tmax : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (t : G → ℕ) (V : G → ℝ),
        (∀ g, t g ≤ tmax) → (∀ g, vmin ≤ V g) →
        ∀ n,
          ‖bigMarkPrefactor P t q V n‖ *
            ((bigMarkLists P t n).card:ℝ) ≤ K^(Fintype.card G) := by
  obtain ⟨K,hK,hBound⟩ :=
    uniform_full_marked_weight q vmin tmax hq hq1 hv
  refine ⟨K,hK,?_⟩
  intro G _ _ P t V ht hV n
  have h := hBound P t V (fun _ => (1:ℂ)) ht hV (fun _ => by simp) n
  have hOne : actualBigMarkDecoration P t q V (fun _ => (1:ℂ)) n =
      bigMarkPrefactor P t q V n * ((bigMarkLists P t n).card:ℂ) := by
    simp [actualBigMarkDecoration]
  rw [hOne,norm_mul,Complex.norm_natCast] at h
  exact h

/-- Exactly the TRUE two physical completion lists, with their
q-damped marked normalizations and completely coupled kernel test.
There is no exponential number of choices hidden inside B. -/
theorem source_actual_dirty_marked_pairing_bound434
    (q vmin : ℝ) (tmax : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < vmin) :
    ∃ Kmark : ℝ, 1 ≤ Kmark ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
        (s : ∀ g,E g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
        (V : G → ℝ) (w wp : ℕ),
        (∀ g p,p ∈ P g → p.Prime) →
        (∀ g i,s g i ∈ P g) →
        (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
        (∀ g,t g ≤ tmax) → (∀ g,vmin ≤ V g) →
        ∀ (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
          (B : ℝ), 0 ≤ B →
        (∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
          ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
            ‖F a b‖ ≤ B) →
        ‖bigMarkPrefactor P t q V w * bigMarkPrefactor P t q V wp *
          (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
            ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b)‖ ≤
          B*Kmark^(2*Fintype.card G) := by
  obtain ⟨Kmark,hKmark,hBound⟩ :=
    source_actual_prefactor_mark_count_bound434 q vmin tmax hq hq1 hv
  refine ⟨Kmark,hKmark,?_⟩
  intro G _ _ P M E s t e V w wp hP hs hDisj ht hV F B hB hF
  let Nw : ℝ := ((bigMarkLists P t w).card:ℝ)
  let Nwp : ℝ := ((bigMarkLists P t wp).card:ℝ)
  have hw := hBound P t V ht hV w
  have hwp := hBound P t V ht hV wp
  have hRows := source_global_dirty_two_row_bound434 P M E s t e w wp
    hP hs hDisj F B hB hF
  change ‖∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b‖ ≤ B*Nw*Nwp at hRows
  have hCap : (‖bigMarkPrefactor P t q V w‖*Nw) *
      (‖bigMarkPrefactor P t q V wp‖*Nwp) ≤
      Kmark^(Fintype.card G)*Kmark^(Fintype.card G) :=
    mul_le_mul hw hwp (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (by linarith) _)
  calc
    _ = ‖bigMarkPrefactor P t q V w‖*
        ‖bigMarkPrefactor P t q V wp‖*
        ‖∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
          ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b‖ := by
        rw [norm_mul,norm_mul]
    _ ≤ ‖bigMarkPrefactor P t q V w‖*
        ‖bigMarkPrefactor P t q V wp‖*(B*Nw*Nwp) :=
          mul_le_mul_of_nonneg_left hRows (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B*((‖bigMarkPrefactor P t q V w‖*Nw)*
        (‖bigMarkPrefactor P t q V wp‖*Nwp)) := by ring
    _ ≤ B*(Kmark^(Fintype.card G)*Kmark^(Fintype.card G)) :=
      mul_le_mul_of_nonneg_left hCap hB
    _ = B*Kmark^(2*Fintype.card G) := by
      rw [two_mul,pow_add]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyNormalization -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Even when shared labels overlap endpoint primes, this is the exact
algebraic source normalization of the DOMINATING marked factors.
All shared V powers occur once, not twice. -/
theorem source_dirty_normalization_identity434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (t s : G → ℕ)
    (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (hM : ∀ g, s g+t g=M) :
    (∏ g,((V g:ℂ)^M)⁻¹) *
      (∏ g,((V g:ℂ)^(t g))⁻¹) *
      (∏ g,((q^((smallPrimeCount (P g) w:ℤ)-(t g:ℤ)):ℝ):ℂ)) *
      (∏ g,((q^((smallPrimeCount (P g) wp:ℤ)-(t g:ℤ)):ℝ):ℂ)) =
    (∏ g,((V g:ℂ)^(s g))⁻¹)*
      bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp := by
  simp only [bigMarkPrefactor,Complex.ofReal_div,Complex.ofReal_pow]
  simp only [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [←hM g,source_shared_joint_normalization434]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyScalarEnvelope -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exact physical two-end normalizations in the DIRTY case. This is
an inequality, not the clean normalization identity; each endpoint
pays the explicit q^(-M*#groups) loss. -/
theorem source_dirty_physical_scalar_envelope434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M d : ℕ) (t s : G → ℕ)
    (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hM : ∀ g, s g+t g=M) :
    ‖(∏ g,((V g:ℂ)^M)⁻¹) *
      (∏ g,((V g:ℂ)^(t g))⁻¹) *
      ((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ) *
      ((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ)‖ ≤
      q^(-2*(M*Fintype.card G:ℝ)) *
        ‖(∏ g,((V g:ℂ)^(s g))⁻¹)*
          bigMarkPrefactor P t q V w*
          bigMarkPrefactor P t q V wp‖ := by
  let a : ℂ := (∏ g,((V g:ℂ)^M)⁻¹) *
    (∏ g,((V g:ℂ)^(t g))⁻¹)
  let b : ℂ := (∏ g,((V g:ℂ)^(s g))⁻¹) *
    bigMarkPrefactor P t q V w * bigMarkPrefactor P t q V wp
  let p1 : ℝ := ∏ g,(q^((smallPrimeCount (P g) w:ℤ)-(t g:ℤ)):ℝ)
  let p2 : ℝ := ∏ g,(q^((smallPrimeCount (P g) wp:ℤ)-(t g:ℤ)):ℝ)
  let qs : ℝ := q^(-(M*Fintype.card G:ℝ))
  let u : ℝ := (sourcePhysicalGroupedHalf434 P M q (d*w))^2
  let v : ℝ := (sourcePhysicalGroupedHalf434 P M q (d*wp))^2
  have hqs : 0 ≤ qs := (Real.rpow_pos_of_pos hq _).le
  have hp1 : 0 ≤ p1 := (Finset.prod_pos (fun g _ => zpow_pos hq _)).le
  have hp2 : 0 ≤ p2 := (Finset.prod_pos (fun g _ => zpow_pos hq _)).le
  have hu : 0 ≤ u := sq_nonneg _
  have hv : 0 ≤ v := sq_nonneg _
  have hdom1 : u ≤ qs*p1 := by
    simpa only [u,qs,p1,Nat.cast_mul] using
      source_global_dirty_damping_le434 P M d w t q hq hq1
  have hdom2 : v ≤ qs*p2 := by
    simpa only [v,qs,p2,Nat.cast_mul] using
      source_global_dirty_damping_le434 P M d wp t q hq hq1
  have hnormal : a*(p1:ℂ)*(p2:ℂ)=b := by
    dsimp only [a,b,p1,p2]
    have hh := source_dirty_normalization_identity434 P M t s V q w wp hM
    push_cast at hh ⊢
    exact hh
  have hnorm : ‖a‖*p1*p2=‖b‖ := by
    calc
      _ = ‖a*(p1:ℂ)*(p2:ℂ)‖ := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hp1,abs_of_nonneg hp2]
      _ = ‖b‖ := congrArg norm hnormal
  have hmult : u*v ≤ (qs*p1)*(qs*p2) :=
    mul_le_mul hdom1 hdom2 hv (mul_nonneg hqs hp1)
  have hpow : qs^2=q^(-2*(M*Fintype.card G:ℝ)) := by
    dsimp [qs]
    rw [pow_two,←Real.rpow_add hq]
    congr 1
    ring
  change ‖a*(u:ℂ)*(v:ℂ)‖ ≤ _
  calc
    _ = ‖a‖*(u*v) := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hu,abs_of_nonneg hv]
      ring
    _ ≤ ‖a‖*((qs*p1)*(qs*p2)) :=
      mul_le_mul_of_nonneg_left hmult (norm_nonneg _)
    _ = qs^2*(‖a‖*p1*p2) := by ring
    _ = _ := by rw [hnorm,hpow]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullGlobalSaving -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 6500000

/-- The logarithm of the actual localized support, including the zero case. -/
theorem source_localized_support_log434 (N : ℕ) (A Y L : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hYmax : Y ≤ Real.exp (3*L/2)) :
    Real.log ((min N (Nat.ceil (A*Y)):ℕ):ℝ) ≤
      (Real.log (A+1)+3/2)*L := by
  have hlogA : 0 ≤ Real.log (A+1) := Real.log_nonneg (by linarith)
  by_cases hN : min N (Nat.ceil (A*Y)) = 0
  · simp only [hN,Nat.cast_zero,Real.log_zero]
    positivity
  have hNp : 0 < ((min N (Nat.ceil (A*Y)):ℕ):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have hSupport := source_localized_support_scale434 N A Y (by linarith) hY
  have hLog := Real.log_le_log hNp hSupport
  rw [Real.log_mul (by linarith : A+1 ≠ 0) (by linarith : Y ≠ 0)] at hLog
  have hLogY := Real.log_le_log (by linarith : 0 < Y) hYmax
  rw [Real.log_exp] at hLogY
  nlinarith

/-- Original FULL endpoint global L2, localized on Y rather than Ncap.
The fixed logarithmic loss includes both growing group counts.
No discrepancy or peeled-main energy is assumed. -/
theorem source_original_full_global_log_budget434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax → vmin ≤ Vs →
        (∀ g, ts g ≤ tmax) → (∀ g, tb g ≤ tmax) →
        (∀ g, vmin ≤ Vsmall g) → (∀ g, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (N q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (alpha c Lambda : ℕ → ℂ) (chi : DirichletCharacter ℂ q)
          (s0 s1 A Y L C0 K0 Cpsi : ℝ) (ea ec : ℕ),
          1 ≤ A → 1 ≤ Y → 1 ≤ L → Y ≤ Real.exp (3*L/2) →
          0 ≤ C0 → 0 ≤ K0 →
          (Fintype.card ι:ℝ) ≤ C0*Real.log L →
          (Fintype.card β:ℝ) ≤ C0*Real.log L →
          (∀ m, ‖alpha m‖ ≤ L^ea) → (∀ r, ‖c r‖ ≤ L^ec) →
          (∀ n ∈ Finset.Icc 1 N, ‖Lambda n‖ ≤ K0*L^Cpsi) →
          (∀ n, Nat.ceil (A*Y) < n → Lambda n = 0) →
          (∫ θ : AddCircle (1:ℝ),
            ‖sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k primeSlot Ptwist alpha c chi s0 s1 Lambda θ‖^2
            ∂AddCircle.haarAddCircle) ≤
          (K0*K)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16*Y*
            L^(2*(Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log K)+16) := by
  obtain ⟨K,hK,hFull⟩ := source_original_full_fourier_global434
    q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    N q primeSlot Ptwist alpha c Lambda chi s0 s1 A Y L C0 K0 Cpsi ea ec
    hA hY hL hYmax hC0 hK0 hns hnb hAlpha hCseq hLambda hSupport
  let Nloc := min N (Nat.ceil (A*Y))
  have hLp : 0 < L := by linarith
  have hM : 0 ≤ K0*L^Cpsi := by positivity
  have hLambdaLoc : ∀ n ∈ Finset.Icc 1 Nloc, ‖Lambda n‖ ≤ K0*L^Cpsi := by
    intro n hn
    exact hLambda n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (min_le_left _ _)⟩)
  have hFullLoc := hFull S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb Nloc q primeSlot Ptwist alpha c Lambda chi
    s0 s1 (L^ea) (L^ec) (K0*L^Cpsi)
    (by positivity) (by positivity) hM hAlpha hCseq hLambdaLoc
  have hGroup := source_literal_group_card_log_budget K L C0 hK hL hC0
    (Fintype.card ι) (Fintype.card β) hns hnb
  let E : ℝ := Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log K
  let Amp : ℝ := L^ea*L^ec*(K0*L^Cpsi*K^(Fintype.card ι+Fintype.card β+1))
  have hAmp0 : 0 ≤ Amp := by dsimp [Amp]; positivity
  have hAmp : Amp ≤ (K0*K)*L^E := by
    calc
      Amp ≤ L^ea*L^ec*(K0*L^Cpsi*(K*L^(2*C0*Real.log K))) := by
        dsimp only [Amp]
        gcongr
      _ = _ := by
        dsimp only [E]
        simp only [Real.rpow_add hLp,Real.rpow_natCast]
        ring
  have hLog0 : 0 ≤ Real.log (A+1)+3/2 := by
    have := Real.log_nonneg (by linarith : 1 ≤ A+1)
    linarith
  have hScalar := source_global_moment_power434 Nloc Amp (K0*K) E (A+1)
    (Real.log (A+1)+3/2) Y L hL (by linarith) hAmp0 (by positivity)
    (by linarith) hLog0
    (source_localized_support_scale434 N A Y (by linarith) hY)
    (source_localized_support_log434 N A Y L hA hY hL hYmax) hAmp
  rw [source_weighted_full_fourier_localize434 N (Nat.ceil (A*Y)) q S Ts Tb
    q0 Vs Vsmall Vbig ts tb b k primeSlot Ptwist alpha c chi s0 s1 Lambda hSupport]
  exact hFullLoc.trans hScalar
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLocalizedError -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 7000000

/-- Localize the actual FULL square-error Fourier polynomial, not merely
its norm surrogate. Ncut is the true endpoint cutoff, independent of N. -/
theorem source_full_weighted_original_group_localized_error434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        (∀ p ∈ S, p.Prime) →
        (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
        (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
        (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
        (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
        ∀ (N Ncut q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (α cseq Lambda : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C M L a D center H Vplus : ℝ),
          0 ≤ A → 0 ≤ C → 0 ≤ M →
          (∀ m, ‖α m‖ ≤ A) →
          (∀ r, ‖cseq r‖ ≤ C) →
          (∀ n ∈ Finset.Icc 1 N, ‖Lambda n‖ ≤ M) →
          1 ≤ Ncut → Ncut ≤ N →
          (∀ n, Ncut < n → Lambda n = 0) →
          (∀ p ∈ S, Real.exp (L^a) ≤ (p:ℝ)) →
          (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Vplus →
          1 ≤ L → 0 ≤ D →
          Real.log (Ncut:ℝ) ≤ D*L →
          2 ≤ H →
          let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
          (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
            ‖sourceWeightedFullPeelingResidualFourier
              N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
              primeSlot Ptwist α cseq χ σ₀ σ₁ Lambda
              ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
            M^2*Vplus*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
              (Ncut:ℝ)*(1+Real.log (Ncut:ℝ))^16*
              Real.exp (-(L^a)) := by
  obtain ⟨K,hK,hMain⟩ := source_full_weighted_original_group_peeling_beta_energy434
    q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb hS hTs hDisjS hTb hDisjB
    N Ncut q primeSlot Ptwist α cseq Lambda χ
    σ₀ σ₁ A C M L a D center H Vplus
    hA hC hM hα hc hLambda hNcut hCut hZero hmin hHarmonic hL hD hLog hH
  have hLocal := source_weighted_error_fourier_localize434
    N Ncut q S Ts Tb q0 Vs Vsmall Vbig ts tb b k primeSlot Ptwist
    α cseq χ σ₀ σ₁ Lambda hZero
  rw [min_eq_right hCut] at hLocal
  rw [hLocal]
  exact hMain S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb hS hTs hDisjS hTb hDisjB
    Ncut q primeSlot Ptwist α cseq Lambda χ
    σ₀ σ₁ A C M L a D center H Vplus
    hA hC hM hα hc
    (fun n hn => hLambda n (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hCut⟩))
    hNcut hmin hHarmonic hL hD hLog hH
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedVInverseBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The remaining shared-slot normalization is bounded only by
vmin and the fixed number of slots; it is polynomial in L when the
number of groups is O(log L). -/
theorem source_shared_actual_inverse_V_budget434
    {G : Type} [Fintype G] (V : G → ℝ) (s : G → ℕ)
    (M : ℕ) (vmin : ℝ)
    (hv : 0 < vmin) (hV : ∀ g,vmin ≤ V g) (hs : ∀ g,s g ≤ M) :
    ‖∏ g,((V g:ℂ)^(s g))⁻¹‖ ≤
      (max (1:ℝ) vmin⁻¹)^(M*Fintype.card G) := by
  let C : ℝ := max 1 vmin⁻¹
  have hC : 1 ≤ C := le_max_left _ _
  have hItem (g : G) : ‖((V g:ℂ)^(s g))⁻¹‖ ≤ C^M := by
    have hVp : 0 < V g := hv.trans_le (hV g)
    have hInv : (V g)⁻¹ ≤ C := by
      have hh : (V g)⁻¹ ≤ vmin⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hv (hV g)
      exact hh.trans (le_max_right _ _)
    have hInvP : 0 ≤ (V g)⁻¹ := (inv_pos.mpr hVp).le
    simp only [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hVp]
    rw [←inv_pow]
    exact (pow_le_pow_left₀ hInvP hInv _).trans
      (pow_le_pow_right₀ hC (hs g))
  calc
    _ = ∏ g, ‖((V g:ℂ)^(s g))⁻¹‖ := norm_prod _ _
    _ ≤ ∏ _g : G,C^M := Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _) (fun g _ => hItem g)
    _ = C^(M*Fintype.card G) := by
      simp only [Finset.prod_const,Finset.card_univ,nsmul_eq_mul]
      rw [←pow_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyPhysicalBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The FULL actual dirty physical pairing with the original V^(-M-t),
two endpoint q-half factors and coupled physical marks. A fixed shared
dilation is allowed, but not assumed clean. No ideal/residual theorem. -/
theorem source_actual_dirty_physical_two_row_budget434
    (q vmin : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < vmin) :
    ∃ Kmark : ℝ, 1 ≤ Kmark ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (E : G → Finset (Fin M))
      (s : ∀ g,E g → ℕ) (t : G → ℕ)
      (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
      (V : G → ℝ) (d w wp : ℕ),
      (∀ g p,p ∈ P g → p.Prime) →
      (∀ g i,s g i ∈ P g) →
      (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
      (∀ g,(E g).card+t g=M) →
      (∀ g,t g ≤ tmax) → (∀ g,vmin ≤ V g) →
      ∀ (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
        (B : ℝ), 0 ≤ B →
      (∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
        ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
          ‖F a b‖ ≤ B) →
      ‖(∏ g,((V g:ℂ)^M)⁻¹)*
        (∏ g,((V g:ℂ)^(t g))⁻¹)*
        (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
        (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)*
        (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
          ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b)‖ ≤
        B*q^(-2*(M*Fintype.card G:ℝ))*
          (max (1:ℝ) vmin⁻¹)^(M*Fintype.card G)*
          Kmark^(2*Fintype.card G) := by
  obtain ⟨Kmark,hKmark,hRows⟩ :=
    source_actual_dirty_marked_pairing_bound434 q vmin tmax hq hq1 hv
  refine ⟨Kmark,hKmark,?_⟩
  intro G _ _ P E s t e V d w wp hP hs hDisj hM ht hV F B hB hF
  let I : ℂ := ∏ g,((V g:ℂ)^((E g).card))⁻¹
  let pw : ℂ := bigMarkPrefactor P t q V w
  let pwp : ℂ := bigMarkPrefactor P t q V wp
  let row : ℂ := ∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b
  let A : ℂ := (∏ g,((V g:ℂ)^M)⁻¹)*
    (∏ g,((V g:ℂ)^(t g))⁻¹)*
    (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
    (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)
  let Q : ℝ := q^(-2*(M*Fintype.card G:ℝ))
  let C : ℝ := (max (1:ℝ) vmin⁻¹)^(M*Fintype.card G)
  have hQ : 0 ≤ Q := (Real.rpow_pos_of_pos hq _).le
  have hI : ‖I‖ ≤ C :=
    source_shared_actual_inverse_V_budget434 V (fun g => (E g).card)
      M vmin hv hV (fun g => by have hh := hM g; omega)
  have hEnv : ‖A‖ ≤ Q*‖I*pw*pwp‖ := by
    simpa only [A,Q,I,pw,pwp] using
      source_dirty_physical_scalar_envelope434 P M d t
        (fun g => (E g).card) V q w wp hq hq1.le hM
  have hRow : ‖pw*pwp*row‖ ≤ B*Kmark^(2*Fintype.card G) := by
    simpa only [pw,pwp,row] using
      hRows P M E s t e V w wp hP hs hDisj ht hV F B hB hF
  change ‖A*row‖ ≤ _
  calc
    _ = ‖A‖*‖row‖ := norm_mul _ _
    _ ≤ (Q*‖I*pw*pwp‖)*‖row‖ :=
      mul_le_mul_of_nonneg_right hEnv (norm_nonneg _)
    _ = Q*‖I‖*‖pw*pwp*row‖ := by
      simp only [norm_mul]
      ring
    _ ≤ Q*C*(B*Kmark^(2*Fintype.card G)) := by
      have hPos : 0 ≤ B*Kmark^(2*Fintype.card G) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hRow
        (mul_nonneg hQ (norm_nonneg I))
      have hstep2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hI hQ) hPos
      exact hstep.trans hstep2
    _ = _ := by
      dsimp only [Q,C]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedHarmonicDilation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The ORIGINAL reciprocal shared dilation 1/D_R is a contraction
at a positive integer D_R. Thus including it does not increase the
already verified physical dirty-row envelope. -/
theorem source_actual_shared_dilation_contract434
    (A R : ℂ) (d : ℕ) (hd : 0 < d) :
    ‖A*((d:ℂ)⁻¹)*R‖ ≤ ‖A*R‖ := by
  have hD : (1:ℝ) ≤ (d:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
  have hDen : ‖((d:ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hD
    simpa only [one_div,inv_one] using hh
  calc
    _ = ‖A*R‖*‖((d:ℂ)⁻¹)‖ := by
      simp only [norm_mul]
      ring
    _ ≤ ‖A*R‖*1 :=
      mul_le_mul_of_nonneg_left hDen (norm_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyGroupExponent -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The complete dirty q/V/mark cost is a FIXED polynomial in L, for
growing original groups. There is no dependence of the base on L. -/
theorem source_shared_dirty_group_log_power434
    (q v K Cs L : ℝ) (M : ℕ)
    (hq : 0 < q) (hv : 0 < v) (hK : 1 ≤ K)
    (hCs : 0 ≤ Cs) (hL : 1 ≤ L) :
    let C := q^(-2*(M:ℝ)) * (max (1:ℝ) v⁻¹)^M * K^2
    let Kg := max (1:ℝ) C
    1 ≤ Kg ∧
    ∀ {G : Type} [Fintype G],
      (Fintype.card G:ℝ) ≤ Cs*Real.log L →
      q^(-2*(M*Fintype.card G:ℝ)) *
        (max (1:ℝ) v⁻¹)^(M*Fintype.card G) *
        K^(2*Fintype.card G) ≤
      Kg*L^(2*Cs*Real.log Kg) := by
  dsimp only
  let C : ℝ := q^(-2*(M:ℝ)) * (max (1:ℝ) v⁻¹)^M * K^2
  let Kg : ℝ := max (1:ℝ) C
  have hKg : 1 ≤ Kg := le_max_left _ _
  refine ⟨hKg,?_⟩
  intro G _ hcard
  have hbase : 0 ≤ C := by
    dsimp [C]
    positivity
  have hqp : q^(-2*(M*Fintype.card G:ℝ)) =
      (q^(-2*(M:ℝ)))^(Fintype.card G) := by
    calc
      _ = q^((-2*(M:ℝ))*(Fintype.card G:ℝ)) := by
        congr 1
        push_cast
        ring
      _ = _ := by
        rw [Real.rpow_mul hq.le,Real.rpow_natCast]
  have hFactor : q^(-2*(M*Fintype.card G:ℝ)) *
        (max (1:ℝ) v⁻¹)^(M*Fintype.card G) *
        K^(2*Fintype.card G) = C^(Fintype.card G) := by
    rw [hqp]
    dsimp only [C]
    simp only [mul_pow,pow_mul]
  have hLlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hBound := source_literal_group_card_log_budget Kg L Cs hKg hL hCs
    (Fintype.card G) 0 hcard (by simpa using mul_nonneg hCs hLlog)
  calc
    _ = C^(Fintype.card G) := hFactor
    _ ≤ Kg^(Fintype.card G) :=
      pow_le_pow_left₀ hbase (le_max_right _ _) _
    _ ≤ Kg^(Fintype.card G+1) :=
      pow_le_pow_right₀ hKg (Nat.le_succ _)
    _ ≤ Kg*L^(2*Cs*Real.log Kg) := by
      simpa only [Nat.add_zero] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyPhysicalLogBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Uniform FIXED logarithmic cost of the original two-end physical
dirty rows, including ALL V^{-M-t}, both original q-half factors,
the actual shared free-mark completions and arbitrarily coupled K.
It is a per-(w,w') estimate, NOT the final summed source correlation. -/
theorem source_actual_dirty_physical_group_log_budget434
    (q vmin Cs : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < vmin) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ (L : ℝ), 1 ≤ L →
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (V : G → ℝ) (d w wp : ℕ),
        (Fintype.card G:ℝ) ≤ Cs*Real.log L →
        (∀ g p,p ∈ P g → p.Prime) →
        (∀ g i,s g i ∈ P g) →
        (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
        (∀ g,(Eshare g).card+t g=M) →
        (∀ g,t g ≤ tmax) → (∀ g,vmin ≤ V g) →
        ∀ (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
          (B : ℝ), 0 ≤ B →
        (∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s w,
          ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s wp,
            ‖F a b‖ ≤ B) →
        ‖(∏ g,((V g:ℂ)^M)⁻¹)*
          (∏ g,((V g:ℂ)^(t g))⁻¹)*
          (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
          (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)*
          (∑ a ∈ sourceGlobalSharedCompletions434 P M Eshare s w,
            ∑ b ∈ sourceGlobalSharedCompletions434 P M Eshare s wp,F a b)‖ ≤
          B*Kg*L^E := by
  obtain ⟨Kmark,hKmark,hRows⟩ :=
    source_actual_dirty_physical_two_row_budget434 q vmin tmax M hq hq1 hv
  let C : ℝ := q^(-2*(M:ℝ))*(max (1:ℝ) vmin⁻¹)^M*Kmark^2
  let Kg : ℝ := max (1:ℝ) C
  let E : ℝ := 2*Cs*Real.log Kg
  have hKg : 1 ≤ Kg := le_max_left _ _
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (by norm_num) hCs) (Real.log_nonneg hKg)
  refine ⟨Kg,E,hKg,hE,?_⟩
  intro L hL G _ _ P Eshare s t e V d w wp hCard hP hs hDisj
    hM ht hV F B hB hF
  have hRaw := hRows P Eshare s t e V d w wp
    hP hs hDisj hM ht hV F B hB hF
  have hCost := (source_shared_dirty_group_log_power434
    q vmin Kmark Cs L M hq hv hKmark hCs hL).2 (G := G) hCard
  change q^(-2*(M*Fintype.card G:ℝ))*
    (max (1:ℝ) vmin⁻¹)^(M*Fintype.card G)*
    Kmark^(2*Fintype.card G) ≤ Kg*L^E at hCost
  calc
    _ ≤ B*(q^(-2*(M*Fintype.card G:ℝ))*
       (max (1:ℝ) vmin⁻¹)^(M*Fintype.card G)*
       Kmark^(2*Fintype.card G)) := by
        simpa only [mul_assoc] using hRaw
    _ ≤ B*(Kg*L^E) := mul_le_mul_of_nonneg_left hCost hB
    _ = B*Kg*L^E := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryPhysicalMarkedKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact ORIGINAL two-end positive physical scalar, with all
V_g^{-M-t_g}, both squared source half-dampings, and coupled
physical marked completions. It intentionally does NOT include
the invariant complex prime-slot core, which is mark independent. -/
noncomputable def sourceAuxiliaryPhysicalMarkedPair434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (Eshare : G → Finset (Fin M))
    (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
    (V : G → ℝ) (q : ℝ) (d w wp : ℕ)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) : ℂ :=
  (∏ g,((V g:ℂ)^M)⁻¹)*
  (∏ g,((V g:ℂ)^(t g))⁻¹)*
  (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
  (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)*
  (∑ a ∈ sourceGlobalSharedCompletions434 P M Eshare s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M Eshare s wp,F a b)

/-- A true physical row multiplying ANY mark-independent source
prime-slot core is bounded by a fixed log power times the core's
absolute value, provided the source pattern's coupled K_nu
mark test has the original bounded sup norm. -/
theorem source_auxiliary_actual_physical_marked_kernel_bound434
    (q vmin Cs : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < vmin) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
    ∀ L : ℝ, 1 ≤ L →
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (V : G → ℝ) (d w wp : ℕ),
        (Fintype.card G:ℝ) ≤ Cs*Real.log L →
        (∀ g p,p ∈ P g → p.Prime) →
        (∀ g i,s g i ∈ P g) →
        (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
        (∀ g,(Eshare g).card+t g=M) →
        (∀ g,t g ≤ tmax) → (∀ g,vmin ≤ V g) →
        ∀ (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
          (B : ℝ), 0 ≤ B →
        (∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s w,
          ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s wp,
            ‖F a b‖ ≤ B) →
        ∀ (A : ℂ),
        ‖A * sourceAuxiliaryPhysicalMarkedPair434
          P M Eshare s t V q d w wp F‖ ≤
          (B*Kg*L^E)*‖A‖ := by
  obtain ⟨Kg,E,hKg,hE,hPhysical⟩ :=
    source_actual_dirty_physical_group_log_budget434
      q vmin Cs tmax M hq hq1 hv hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  intro L hL G _ _ P Eshare s t e V d w wp hCard hP hs hDisj
    hM ht hV F B hB hF A
  have hRow := hPhysical L hL P Eshare s t e V d w wp
    hCard hP hs hDisj hM ht hV F B hB hF
  change ‖sourceAuxiliaryPhysicalMarkedPair434
    P M Eshare s t V q d w wp F‖ ≤ B*Kg*L^E at hRow
  calc
    _ = ‖A‖*‖sourceAuxiliaryPhysicalMarkedPair434
      P M Eshare s t V q d w wp F‖ := norm_mul A _
    _ ≤ ‖A‖*(B*Kg*L^E) :=
      mul_le_mul_of_nonneg_left hRow (norm_nonneg A)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryLiftedPhysicalRow -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The REAL source03 prime-slot arithmetic kernel, with its own
independent parity set Ptw, multiplied by the FULL physical
two-end marked row after w=p*y and w'=p*(y+kD).
The positive q/V normalization costs ONLY a fixed log-power,
uniformly in p,y and for all four parity sign choices.
The original coefficient K_nu is retained as a COMPLETELY
COUPLED Fmark, not silently separated across endpoints. -/
theorem source_auxiliary_lifted_physical_row_bound434
    (q vmin Cs : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < vmin) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ L : ℝ, 1 ≤ L →
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (V : G → ℝ) (dShared : ℕ),
        (Fintype.card G:ℝ) ≤ Cs*Real.log L →
        (∀ g p,p ∈ P g → p.Prime) →
        (∀ g i,s g i ∈ P g) →
        (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
        (∀ g,(Eshare g).card+t g=M) →
        (∀ g,t g ≤ tmax) → (∀ g,vmin ≤ V g) →
        ∀ (Ptw prime1 prime2 : Finset ℕ) (p y D q1 q2 : ℕ)
          (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
          (chi1 : DirichletCharacter ℂ q1)
          (chi2 : DirichletCharacter ℂ q2)
          (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
          (eps1 eps2 : Bool)
          (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
          (B : ℝ), 0 ≤ B →
        (∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s (p*y),
          ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
            (p*((y:ℤ)+k*(D:ℤ)).toNat),
            ‖Fmark a b‖ ≤ B) →
        ‖sourceAuxiliaryGeneralLifted434
          (Finset.univ.biUnion P) Ptw prime1 prime2 p y D q1 q2
          k alpha1 alpha2 c1 c2 chi1 chi2 s01 s11 s02 s12
          Z a1 a2 psi eps1 eps2 *
          sourceAuxiliaryPhysicalMarkedPair434
            P M Eshare s t V q dShared
            (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat) Fmark‖ ≤
        (B*Kg*L^E)*
          ‖sourceAuxiliaryGeneralLifted434
            (Finset.univ.biUnion P) Ptw prime1 prime2 p y D q1 q2
            k alpha1 alpha2 c1 c2 chi1 chi2 s01 s11 s02 s12
            Z a1 a2 psi eps1 eps2‖ := by
  obtain ⟨Kg,E,hKg,hE,hPhysical⟩ :=
    source_auxiliary_actual_physical_marked_kernel_bound434
      q vmin Cs tmax M hq hq1 hv hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  intro L hL G _ _ P Eshare s t e V dShared
    hCard hP hs hDisj hM ht hV
    Ptw prime1 prime2 p y D q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    Fmark B hB hF
  let A : ℂ := sourceAuxiliaryGeneralLifted434
    (Finset.univ.biUnion P) Ptw prime1 prime2 p y D q1 q2
    k alpha1 alpha2 c1 c2 chi1 chi2 s01 s11 s02 s12
    Z a1 a2 psi eps1 eps2
  have hh := hPhysical L hL P Eshare s t e V dShared
    (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat)
    hCard hP hs hDisj hM ht hV Fmark B hB hF A
  simpa only [A] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTuplePhysical -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- ACTUAL original complete free-dilation source kernel, multiplied
by the fully normalized two-end physical marked row. Charging any
labelled auxiliary slot gives the ORIGINAL 1/p saving, retaining
arbitrary coupled K_nu and BOTH endpoint marked lists.
Other auxiliary labels need neither be distinct nor avoid p. -/
theorem source_auxiliary_full_tuple_physical_row_bound434
    (q vmin Cs : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < vmin) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ L : ℝ, 1 ≤ L →
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
        (labels : ι → ℕ) (slot : ι)
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (V : G → ℝ) (dShared : ℕ)
        (Ptw prime1 prime2 : Finset ℕ)
        (y q1 q2 : ℕ) (k : ℤ)
        (alpha1 alpha2 c1 c2 : ℕ → ℂ)
        (chi1 : DirichletCharacter ℂ q1)
        (chi2 : DirichletCharacter ℂ q2)
        (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
        (eps1 eps2 : Bool)
        (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
        (B : ℝ),
      (Fintype.card G:ℝ) ≤ Cs*Real.log L →
      (∀ g p,p ∈ P g → p.Prime) →
      (∀ g i,s g i ∈ P g) →
      (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
      (∀ g,(Eshare g).card+t g=M) →
      (∀ g,t g ≤ tmax) →
      (∀ g,vmin ≤ V g) →
      (∀ j,(labels j).Prime) →
      (labels slot).Prime →
      labels slot ∈ Finset.univ.biUnion P →
      0 < y → 0 < Z →
      0 < (y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ) →
      0 ≤ B →
      (∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s
        (labels slot*y),
       ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
        (labels slot*(((y:ℤ)+k*
          (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat)),
        ‖Fmark a b‖ ≤ B) →
      ‖sourceAuxiliaryOriginalFullTupleKernel434
        labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
        y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          V q dShared (labels slot*y)
          (labels slot*(((y:ℤ)+k*
            (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat))
          Fmark‖ ≤
        (B*Kg*L^E)*(labels slot:ℝ)⁻¹*
          ‖sourceAuxiliaryGeneralStripped434
            (Finset.univ.biUnion P) Ptw prime1 prime2
            y (sourceAuxiliaryOtherProduct434 labels slot)
            q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
            s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ := by
  obtain ⟨Kg,E,hKg,hE,hRow⟩ :=
    source_auxiliary_lifted_physical_row_bound434
      q vmin Cs tmax M hq hq1 hv hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  intro L hL ι G _ _ _ _ labels slot P Eshare s t e V dShared
    Ptw prime1 prime2 y q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    Fmark B hCard hP hs hDisj hM ht hV
    hPrimeAll hp hpIn hy hZ hShift hB hF
  let d : ℕ := sourceAuxiliaryOtherProduct434 labels slot
  let p : ℕ := labels slot
  have hd : 0 < d :=
    source_auxiliary_original_other_product_pos434 labels slot hPrimeAll
  have hEq := source_auxiliary_full_tuple_literal_lifted434
    labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
    y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
  have hPhysical := hRow L hL P Eshare s t e V dShared
    hCard hP hs hDisj hM ht hV
    Ptw prime1 prime2 p y d q1 q2 k
    alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    Fmark B hB hF
  have hN := source_auxiliary_general_pointwise_norm434
    (Finset.univ.biUnion P) Ptw prime1 prime2 p y d q1 q2 k
    alpha1 alpha2 c1 c2 chi1 chi2
    s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    hp hpIn hy hd hZ hShift
  rw [hEq]
  calc
    _ ≤ (B*Kg*L^E)*
      ‖sourceAuxiliaryGeneralLifted434
        (Finset.univ.biUnion P) Ptw prime1 prime2 p y d q1 q2 k
        alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ :=
      hPhysical
    _ = _ := by rw [hN]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTuplePhysicalFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- Genuine original FULL auxiliary free product D_C including the
selected colliding p, ORIGINAL complex prime-slot arithmetic, and
the fully normalized two-ended physical marked pairing. An
UNWEIGHTED source L2 fibre bound at the REDUCED shift k*D_other
transfers to the original charged physical fibre with EXACTLY
one 1/p factor. Fmark is arbitrary and may encode the entire
coupled signed source comparison kernel K_nu. -/
theorem source_auxiliary_full_tuple_physical_fibre_bound434
    (q vmin Cs : ℝ) (tmax M : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < vmin) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ L : ℝ, 1 ≤ L →
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
        (labels : ι → ℕ) (slot : ι)
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (V : G → ℝ) (dShared : ℕ)
        (Ptw prime1 prime2 : Finset ℕ)
        (q1 q2 : ℕ) (k : ℤ)
        (alpha1 alpha2 c1 c2 : ℕ → ℂ)
        (chi1 : DirichletCharacter ℂ q1)
        (chi2 : DirichletCharacter ℂ q2)
        (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
        (eps1 eps2 : Bool)
        (Fmark : ℕ → (G → Fin M → ℕ) →
          (G → Fin M → ℕ) → ℂ)
        (S : Finset ℕ) (Bmark Bcore : ℝ),
      (Fintype.card G:ℝ) ≤ Cs*Real.log L →
      (∀ g p,p ∈ P g → p.Prime) →
      (∀ g i,s g i ∈ P g) →
      (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
      (∀ g,(Eshare g).card+t g=M) →
      (∀ g,t g ≤ tmax) →
      (∀ g,vmin ≤ V g) →
      (∀ j,(labels j).Prime) →
      labels slot ∈ Finset.univ.biUnion P →
      0 < Z → 0 ≤ Bmark → 0 ≤ Bcore →
      (∀ y ∈ S,0 < y ∧
        0 < (y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ)) →
      (∀ y ∈ S,
        ∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*y),
        ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*((((y:ℤ)+k*
            (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat):ℕ)),
        ‖Fmark y a b‖ ≤ Bmark) →
      (∑ y ∈ S,
        ‖sourceAuxiliaryGeneralStripped434
          (Finset.univ.biUnion P) Ptw prime1 prime2
          y (sourceAuxiliaryOtherProduct434 labels slot)
          q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖) ≤ Bcore →
      ‖∑ y ∈ S,
        sourceAuxiliaryOriginalFullTupleKernel434
          labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
          y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          V q dShared (labels slot*y)
          (labels slot*(((y:ℤ)+k*
            (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat))
          (Fmark y)‖ ≤
       (labels slot:ℝ)⁻¹*((Bmark*Kg*L^E)*Bcore) := by
  obtain ⟨Kg,E,hKg,hE,hRow⟩ :=
    source_auxiliary_full_tuple_physical_row_bound434
      q vmin Cs tmax M hq hq1 hv hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  intro L hL ι G _ _ _ _ labels slot P Eshare s t e V dShared
    Ptw prime1 prime2 q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    Fmark S Bmark Bcore hCard hP hs hDisj hM ht hV
    hPrimeAll hpIn hZ hBmark hBcore hS hFM hCore
  have hFactor : 0 ≤ (Bmark*Kg*L^E)*(labels slot:ℝ)⁻¹ := by
    have hp := (hPrimeAll slot).pos
    have hpNonneg : (0:ℝ) ≤ labels slot := by exact_mod_cast hp.le
    have hLp : 0 < L := by linarith
    positivity
  have hEach (y : ℕ) (hy : y ∈ S) :
      ‖sourceAuxiliaryOriginalFullTupleKernel434
          labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
          y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          V q dShared (labels slot*y)
          (labels slot*(((y:ℤ)+k*
            (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat))
          (Fmark y)‖ ≤
      ((Bmark*Kg*L^E)*(labels slot:ℝ)⁻¹)*
        ‖sourceAuxiliaryGeneralStripped434
          (Finset.univ.biUnion P) Ptw prime1 prime2
          y (sourceAuxiliaryOtherProduct434 labels slot)
          q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ := by
    have hh := hRow L hL labels slot P Eshare s t e V dShared
      Ptw prime1 prime2 y q1 q2 k alpha1 alpha2 c1 c2
      chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
      (Fmark y) Bmark hCard hP hs hDisj hM ht hV
      hPrimeAll (hPrimeAll slot) hpIn (hS y hy).1
      hZ (hS y hy).2 hBmark (hFM y hy)
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ∑ y ∈ S,
      ‖sourceAuxiliaryOriginalFullTupleKernel434
          labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
          y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          V q dShared (labels slot*y)
          (labels slot*(((y:ℤ)+k*
            (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat))
          (Fmark y)‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ S,((Bmark*Kg*L^E)*(labels slot:ℝ)⁻¹)*
        ‖sourceAuxiliaryGeneralStripped434
          (Finset.univ.biUnion P) Ptw prime1 prime2
          y (sourceAuxiliaryOtherProduct434 labels slot)
          q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ :=
      Finset.sum_le_sum hEach
    _ = ((Bmark*Kg*L^E)*(labels slot:ℝ)⁻¹)*
        (∑ y ∈ S,‖sourceAuxiliaryGeneralStripped434
          (Finset.univ.biUnion P) Ptw prime1 prime2
          y (sourceAuxiliaryOtherProduct434 labels slot)
          q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
          s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖) := by
      rw [Finset.mul_sum]
    _ ≤ ((Bmark*Kg*L^E)*(labels slot:ℝ)⁻¹)*Bcore :=
      mul_le_mul_of_nonneg_left hCore hFactor
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryPhysicalExclusionSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- The literal source03 FREE physical marked-row exclusion is
EXACTLY a finite partition, not a heuristic small-probability
event. Both endpoint physical lists remain coupled by the genuine
shared slot constraints and any pattern kernel K_nu. -/
theorem source_auxiliary_physical_exclusion_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (p w wp : ℕ)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
        Fmark a b) =
    (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
        if (∃ g j,a g (e g j)=p) ∨ (∃ g j,b g (e g j)=p)
        then 0 else Fmark a b) +
    sourceAuxiliaryPhysicalCollisionMask434 P M E s t e
      p w wp Fmark := by
  classical
  unfold sourceAuxiliaryPhysicalCollisionMask434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hCollision :
      ((∃ g j,a g (e g j)=p) ∨ (∃ g j,b g (e g j)=p))
  · simp [hCollision]
  · simp [hCollision]

/-- Retain original physical q/V normalizations EXACTLY while
partitioning a row into the source allowed graph transition and
the error removed because an auxiliary free p collides with
an unshared endpoint mark. No nonnegative surrogate is inserted. -/
theorem source_auxiliary_physical_exclusion_weighted_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ) (d w wp p : ℕ)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    sourceAuxiliaryPhysicalMarkedPair434
      P M E s t V q d w wp Fmark =
    sourceAuxiliaryPhysicalMarkedPair434
      P M E s t V q d w wp
      (fun a b => if (∃ g j,a g (e g j)=p) ∨
          (∃ g j,b g (e g j)=p) then 0 else Fmark a b) +
    sourceAuxiliaryPhysicalMarkedPair434
      P M E s t V q d w wp
      (fun a b => if (∃ g j,a g (e g j)=p) ∨
          (∃ g j,b g (e g j)=p) then Fmark a b else 0) := by
  classical
  unfold sourceAuxiliaryPhysicalMarkedPair434
  have hSplit := source_auxiliary_physical_exclusion_split434
    P M E s t e p w wp Fmark
  unfold sourceAuxiliaryPhysicalCollisionMask434 at hSplit
  rw [hSplit]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedDirtyPositivePhysical -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The literal physically weighted dirty two-end row is dominated
by the unweighted POSITIVE source marked endpoints, not by a possibly
cancelling complex marked test. D_R^{-1} is included exactly once. -/
theorem source_actual_dirty_physical_positive_pair434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M d : ℕ) (hd : 0 < d)
    (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (hM : ∀ g,(E g).card+t g=M)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,
        ‖F a b‖ ≤ B) :
    ‖(∏ g,((V g:ℂ)^M)⁻¹)*
      (∏ g,((V g:ℂ)^(t g))⁻¹)*
      (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
      (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)*
      ((d:ℂ)⁻¹)*
      (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b)‖ ≤
    q^(-2*(M*Fintype.card G:ℝ))*
      ‖∏ g,((V g:ℂ)^((E g).card))⁻¹‖*
      B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ := by
  let A : ℂ := (∏ g,((V g:ℂ)^M)⁻¹)*
    (∏ g,((V g:ℂ)^(t g))⁻¹)*
    (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
    (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)
  let I : ℂ := ∏ g,((V g:ℂ)^((E g).card))⁻¹
  let p1 : ℂ := bigMarkPrefactor P t q V w
  let p2 : ℂ := bigMarkPrefactor P t q V wp
  let R : ℂ := ∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b
  let Q : ℝ := q^(-2*(M*Fintype.card G:ℝ))
  have hQ : 0 ≤ Q := (Real.rpow_pos_of_pos hq _).le
  have hOriginal := source_dirty_physical_scalar_envelope434
    P M d t (fun g => (E g).card) V q w wp hq hq1 hM
  have hRow := source_actual_dirty_two_row_positive_majorant434
    P M E s t e V q w wp hP hs hDisj F B hB hF
  change ‖p1*p2*R‖ ≤
    B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
      ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ at hRow
  have hEnv : ‖A‖ ≤ Q*‖I*p1*p2‖ := by
    simpa only [A,Q,I,p1,p2] using hOriginal
  change ‖A*((d:ℂ)⁻¹)*R‖ ≤ _
  calc
    _ ≤ ‖A*R‖ := source_actual_shared_dilation_contract434 A R d hd
    _ = ‖A‖*‖R‖ := norm_mul A R
    _ ≤ (Q*‖I*p1*p2‖)*‖R‖ :=
      mul_le_mul_of_nonneg_right hEnv (norm_nonneg _)
    _ = Q*‖I‖*‖p1*p2*R‖ := by
      simp only [norm_mul]
      ring
    _ ≤ Q*‖I‖*(B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
      ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖) :=
      mul_le_mul_of_nonneg_left hRow
        (mul_nonneg hQ (norm_nonneg _))
    _ = _ := by dsimp only [Q,I]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliarySharedReciprocal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The EXACT original global shared dilation D_R is positive.
No exceptional zero product is possible: every shared slot lies
in a genuine prime group. Repeated shared labels and cross-group
constraints are not changed or silently conditioned away. -/
theorem source_original_global_shared_dilation_pos434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g) :
    0 < ∏ p ∈ Finset.univ.biUnion
      (fun g => sourceSharedPrimeSet434 (E g) (s g)),p := by
  classical
  apply Finset.prod_pos
  intro p hp
  obtain ⟨g,hg,hps⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨i,hi,hpi⟩ := Finset.mem_image.mp hps
  subst p
  exact (hP g (s g i) (hs g i)).pos

/-- The ORIGINAL shared reciprocal factor 1/D_R, absent from
the stripped source harmonic summand, is a contraction on every
complex physical pairing. This justifies retaining it in the
full physical auxiliary error without paying a new log power. -/
theorem source_original_shared_reciprocal_contraction434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (A R : ℂ) :
    ‖A * ((∏ p ∈ Finset.univ.biUnion
      (fun g => sourceSharedPrimeSet434 (E g) (s g)),p:ℕ):ℂ)⁻¹ * R‖
      ≤ ‖A*R‖ := by
  exact source_actual_shared_dilation_contract434 A R
    (∏ p ∈ Finset.univ.biUnion
      (fun g => sourceSharedPrimeSet434 (E g) (s g)),p)
    (source_original_global_shared_dilation_pos434 P M E s hP hs)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueSharedDilation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The TRUE ORIGINAL shared dilation is a MULTISET PRODUCT over
every labelled shared slot, NOT the product over its set of distinct
prime values. Repeated labels are deliberately retained. -/
noncomputable def sourceAuxiliaryTrueSharedDilation434
    {G : Type} [Fintype G] [DecidableEq G]
    {M : ℕ} (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) : ℕ :=
  ∏ g : G, ∏ i : E g, s g i

/-- The literal shared labelled product remains positive even when
several slots use the SAME prime value. -/
theorem source_auxiliary_true_shared_dilation_pos434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p∈P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g) :
    0 < sourceAuxiliaryTrueSharedDilation434 E s := by
  classical
  unfold sourceAuxiliaryTrueSharedDilation434
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact (hP g (s g i) (hs g i)).pos

/-- The ACTUAL harmonic 1/D_R contraction, with multiplicities.
Unlike the set-based surrogate, this is valid without assuming
shared labels are distinct or disjoint from endpoint marks. -/
theorem source_auxiliary_true_shared_reciprocal_contract434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p∈P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (A R : ℂ) :
    ‖A*((sourceAuxiliaryTrueSharedDilation434 E s:ℕ):ℂ)⁻¹*R‖ ≤
      ‖A*R‖ :=
  source_actual_shared_dilation_contract434 A R
    (sourceAuxiliaryTrueSharedDilation434 E s)
    (source_auxiliary_true_shared_dilation_pos434 P M E s hP hs)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFullTupleExclusion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The TRUE source03 auxiliary free-exclusion event, with a full
labelled prime tuple and a selected auxiliary slot. The event
depends separately on BOTH actual ordered physical marked lists,
not just the unordered set of prime divisors. -/
noncomputable def sourceAuxiliaryFullTupleCollisionMark434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
    [Fintype G] [DecidableEq G]
    (labels : ι → ℕ) (slot : ι) (M : ℕ)
    (E : G → Finset (Fin M))
    (e : ∀ g,Fin (M-(E g).card) ≃ {i : Fin M // i ∉ E g})
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
    (a b : G → Fin M → ℕ) : ℂ :=
  if (∃ g j,a g (e g j)=labels slot) ∨
     (∃ g j,b g (e g j)=labels slot)
  then Fmark a b else 0

/-- Exactly the original allowed/forbidden physical-row partition
for a selected prime slot of the complete source free product.
The complex full two-end row, including BOTH q-halves, M,t and V
normalizations, is partitioned without approximation. -/
theorem source_auxiliary_full_tuple_physical_row_split434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
    [Fintype G] [DecidableEq G]
    (labels : ι → ℕ) (slot : ι)
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ) (d w wp : ℕ)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q d w wp Fmark =
    sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q d w wp
      (fun a b => if (∃ g j,a g (e g j)=labels slot) ∨
          (∃ g j,b g (e g j)=labels slot) then 0 else Fmark a b) +
    sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q d w wp
      (fun a b => if (∃ g j,a g (e g j)=labels slot) ∨
          (∃ g j,b g (e g j)=labels slot) then Fmark a b else 0) :=
  source_auxiliary_physical_exclusion_weighted_split434
    P M E s t e V q d w wp (labels slot) Fmark

/-- Multiply the ACTUAL split by the literal complete tuple
arithmetic kernel and by 1/D_R where D_R keeps multiplicities.
The full raw/comparison source expression is unchanged, including
k*(product all free labelled slots), four signs and 1/w. -/
theorem source_auxiliary_full_tuple_physical_pair_split434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
    [Fintype G] [DecidableEq G]
    (labels : ι → ℕ) (slot : ι)
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ)
    (Ptw prime1 prime2 : Finset ℕ) (y q1 q2 : ℕ) (k : ℤ)
    (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool)
    (Fmark : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    let w := labels slot*y
    let wp := labels slot*
      (((y:ℤ)+k*(sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat)
    let dShared := sourceAuxiliaryTrueSharedDilation434 E s
    let A := sourceAuxiliaryOriginalFullTupleKernel434
      labels slot (Finset.univ.biUnion P) Ptw prime1 prime2
      y q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    A*(dShared:ℂ)⁻¹*
      sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q dShared w wp Fmark =
    A*(dShared:ℂ)⁻¹*
      sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q dShared w wp
      (fun a b => if (∃ g j,a g (e g j)=labels slot) ∨
          (∃ g j,b g (e g j)=labels slot) then 0 else Fmark a b) +
    A*(dShared:ℂ)⁻¹*
      sourceAuxiliaryPhysicalMarkedPair434 P M E s t V q dShared w wp
      (fun a b => if (∃ g j,a g (e g j)=labels slot) ∨
          (∃ g j,b g (e g j)=labels slot) then Fmark a b else 0) := by
  dsimp only
  rw [source_auxiliary_full_tuple_physical_row_split434
    labels slot P M E s t e V q
    (sourceAuxiliaryTrueSharedDilation434 E s)
    (labels slot*y)
    (labels slot*(((y:ℤ)+k*
      (sourceAuxiliaryOtherProduct434 labels slot:ℤ)).toNat))
    Fmark]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueSharedParity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The source Omega-parity character always squares to one.
This is multiplicity-counted valuation parity, not parity of
the distinct prime-support set. -/
theorem source_original_true_parity_square434
    (P : Finset ℕ) (n : ℕ) :
    literalSourceParity P n * literalSourceParity P n = 1 := by
  simp only [literalSourceParity,←pow_add]
  rw [show (∑ p ∈ P,n.factorization p)+(∑ p ∈ P,n.factorization p) =
      2*(∑ p ∈ P,n.factorization p) by omega]
  rw [pow_mul]
  norm_num

/-- With the same original parity choice on both ends, the FULL
shared dilation cancels exactly, including duplicate labelled
shared primes and arbitrary overlap with the stripped endpoints.
There is NO probabilistic clean-event hypothesis in this identity. -/
theorem source_original_true_shared_common_parity434
    (P : Finset ℕ) (D w wp : ℕ)
    (hD : D ≠ 0) (hw : w ≠ 0) (hwp : wp ≠ 0)
    (choice : Bool) :
    sourceEndpointSign434 P choice (D*w)*
      sourceEndpointSign434 P choice (D*wp) =
    sourceEndpointSign434 P choice w*
      sourceEndpointSign434 P choice wp := by
  cases choice with
  | false => simp [sourceEndpointSign434]
  | true =>
    simp only [sourceEndpointSign434,if_true]
    rw [source_literal_parity_mul434 P D w hD hw,
      source_literal_parity_mul434 P D wp hD hwp]
    calc
      _ = (literalSourceParity P D * literalSourceParity P D)*
          (literalSourceParity P w*literalSourceParity P wp) := by ring
      _ = _ := by rw [source_original_true_parity_square434]; ring

/-- Instantiate at the genuine ORIGINAL multiset D_R, rather than
the deduplicated set-product surrogate used only for clean geometry. -/
theorem source_original_true_shared_full_common_parity434
    {G : Type} [Fintype G] [DecidableEq G]
    (groups : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p∈groups g → p.Prime)
    (hs : ∀ g i,s g i ∈ groups g)
    (Ptw : Finset ℕ) (w wp : ℕ)
    (hw : w ≠ 0) (hwp : wp ≠ 0) (choice : Bool) :
    let dR : ℕ := sourceAuxiliaryTrueSharedDilation434 E s
    sourceEndpointSign434 Ptw choice (dR*w)*
      sourceEndpointSign434 Ptw choice (dR*wp) =
    sourceEndpointSign434 Ptw choice w*
      sourceEndpointSign434 Ptw choice wp := by
  dsimp only
  exact source_original_true_shared_common_parity434 Ptw _ w wp
    (source_auxiliary_true_shared_dilation_pos434 groups M E s hP hs).ne'
    hw hwp choice
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueSharedCore -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- Literal original outside-P factor is invariant under a finite
LABELLED PRIME PRODUCT. The index function need NOT be injective:
repeated prime labels are correctly erased with their full
multiplicities. This extends the previous set-product lemma. -/
theorem source_auxiliary_original_labelled_outside_invariant434
    {ι : Type} [DecidableEq ι]
    (R : Finset ι) (prime : ι → ℕ) (P : Finset ℕ) (w : ℕ)
    (hPrime : ∀ i ∈ R,(prime i).Prime)
    (hP : ∀ i ∈ R,prime i ∈ P) (hw : 0 < w) :
    sourceOutsidePart P ((∏ i ∈ R,prime i)*w) =
      sourceOutsidePart P w := by
  classical
  induction R using Finset.induction_on with
  | empty => simp
  | @insert i R hi ih =>
    have hip := hPrime i (Finset.mem_insert_self _ _)
    have hiP := hP i (Finset.mem_insert_self _ _)
    have hpR : ∀ j ∈ R,(prime j).Prime :=
      fun j hj => hPrime j (Finset.mem_insert_of_mem hj)
    have hPR : ∀ j ∈ R,prime j ∈ P :=
      fun j hj => hP j (Finset.mem_insert_of_mem hj)
    have hPos : 0 < ∏ j ∈ R, prime j :=
      Finset.prod_pos (fun j hj => (hpR j hj).pos)
    have hw' : 0 < (∏ j ∈ R,prime j)*w := mul_pos hPos hw
    rw [Finset.prod_insert hi]
    have hInv := source_outside_part_shared_invariant434
      P {prime i} ((∏ j ∈ R,prime j)*w)
      (by intro z hz
          have he : z=prime i := Finset.mem_singleton.mp hz
          subst z
          exact hip)
      (Finset.singleton_subset_iff.mpr hiP) hw'.ne'
    simpa only [Finset.prod_singleton,mul_assoc] using
      hInv.trans (ih hpR hPR)

/-- Original full prime-slot arithmetic F(n), not a surrogate
divisor bound, is invariant under every labelled shared prime,
including duplicate values. -/
theorem source_auxiliary_original_labelled_core_invariant434
    {ι : Type} [DecidableEq ι]
    (R : Finset ι) (prime : ι → ℕ)
    (P primeSlot : Finset ℕ) (w q : ℕ)
    (alpha c : ℕ → ℂ) (chi : DirichletCharacter ℂ q)
    (s0 s1 : ℝ)
    (hPrime : ∀ i ∈ R,(prime i).Prime)
    (hP : ∀ i ∈ R,prime i ∈ P) (hw : 0 < w) :
    sourceCore (sourceOutsidePart P ((∏ i ∈ R,prime i)*w))
      primeSlot alpha c q chi s0 s1 =
    sourceCore (sourceOutsidePart P w)
      primeSlot alpha c q chi s0 s1 := by
  rw [source_auxiliary_original_labelled_outside_invariant434
    R prime P w hPrime hP hw]

/-- Instantiate at ACTUAL shared labelled slots, using the
multiset product D_R = prod_g prod_{i∈E_g} shared(g,i).
No set deduplication or injectivity assumption occurs. -/
theorem source_auxiliary_true_shared_full_core_invariant434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M)) (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p∈P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (primeSlot : Finset ℕ) (w q : ℕ)
    (alpha c : ℕ → ℂ) (chi : DirichletCharacter ℂ q)
    (s0 s1 : ℝ) (hw : 0 < w) :
    sourceCore
      (sourceOutsidePart (Finset.univ.biUnion P)
        (sourceAuxiliaryTrueSharedDilation434 E s*w))
      primeSlot alpha c q chi s0 s1 =
    sourceCore
      (sourceOutsidePart (Finset.univ.biUnion P) w)
      primeSlot alpha c q chi s0 s1 := by
  classical
  let slots : Type := Σ g : G,E g
  let label : slots → ℕ := fun z => s z.1 z.2
  have hp : ∀ z ∈ (Finset.univ : Finset slots),(label z).Prime := by
    intro z hz
    exact hP z.1 (s z.1 z.2) (hs z.1 z.2)
  have hmem : ∀ z ∈ (Finset.univ : Finset slots),
      label z ∈ Finset.univ.biUnion P := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨z.1,Finset.mem_univ _,hs z.1 z.2⟩
  have hprod :
      sourceAuxiliaryTrueSharedDilation434 E s =
      ∏ z : slots,label z := by
    change (∏ g : G,∏ i : E g,s g i) =
      (∏ z : Σ g : G,E g,s z.1 z.2)
    rw [Fintype.prod_sigma]
  rw [hprod]
  exact source_auxiliary_original_labelled_core_invariant434
    (Finset.univ : Finset slots) label
    (Finset.univ.biUnion P) primeSlot w q
    alpha c chi s0 s1 hp hmem hw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSharedIndependentSigns -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Valuation parity of the ACTUAL source03 shared dilation, with
all repeated prime labels counted, is determined by the exact
number of labelled shared slots. Requires that EVERY shared
prime is among the primes twisted by parity Ptw.
No injectivity or coprimality of labelled primes is assumed. -/
theorem source_original_true_shared_parity_labelled434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (Ptw : Finset ℕ)
    (hPrime : ∀ g i,(s g i).Prime)
    (hTw : ∀ g i,s g i ∈ Ptw) :
    literalSourceParity Ptw
      (sourceAuxiliaryTrueSharedDilation434 E s) =
    (-1:ℂ)^(∑ g : G, (E g).card) := by
  classical
  have hh := source_shared_product_parity434
    Ptw
    (Finset.univ : Finset ((g : G) × E g))
    (fun gi => s gi.1 gi.2)
    (fun gi _ => hPrime gi.1 gi.2)
    (fun gi _ => hTw gi.1 gi.2)
  simpa only [sourceAuxiliaryTrueSharedDilation434,
    Fintype.prod_sigma,Finset.card_univ,
    Fintype.card_sigma,Fintype.card_coe] using hh

/-- FOUR independent source/target endpoint parity signs can be
stripped from the TRUE multiset shared dilation with a known
pattern CONSTANT sign, not an approximation. For different
signs, this constant need NOT equal one; hence this algebraic
lemma does NOT prove the four-signed residual operator has
the SAME ideal norm bound as the original common-twist operator.
The missing uniform signed ideal/physical transference is explicit. -/
theorem source_original_true_shared_independent_signs434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (Ptw : Finset ℕ) (hTw : ∀ g i,s g i ∈ Ptw)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (epsSrc epsTgt : Bool) :
    let DR := sourceAuxiliaryTrueSharedDilation434 E s
    let r := ∑ g : G,(E g).card
    sourceEndpointSign434 Ptw epsSrc (DR*w) *
      sourceEndpointSign434 Ptw epsTgt (DR*wp) =
    ((if epsSrc then (-1:ℂ)^r else 1)*
     (if epsTgt then (-1:ℂ)^r else 1)) *
      sourceEndpointSign434 Ptw epsSrc w *
      sourceEndpointSign434 Ptw epsTgt wp := by
  classical
  dsimp only
  have hPrime : ∀ g i,(s g i).Prime :=
    fun g i => hP g (s g i) (hs g i)
  have hSign := source_original_true_shared_parity_labelled434
    M E s Ptw hPrime hTw
  have hD := source_auxiliary_true_shared_dilation_pos434
    P M E s hP hs
  exact source_shared_dilation_independent_signs434
    Ptw (sourceAuxiliaryTrueSharedDilation434 E s) w wp
    (∑ g : G,(E g).card) epsSrc epsTgt
    hD.ne' hw.ne' hwp.ne' hSign

/-- In the ORIGINAL common-parity source03 channel, the above
pattern factor equals one even when the shared labels repeat. -/
theorem source_original_true_shared_common_sign_factor434
    (r : ℕ) (eps : Bool) :
    (if eps then (-1:ℂ)^r else 1)*
    (if eps then (-1:ℂ)^r else 1) = 1 := by
  cases eps with
  | false => norm_num
  | true =>
    simp only [if_true,←pow_add]
    rw [show r+r=2*r by omega,pow_mul]
    norm_num
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueActualSharedParity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- Real SOURCE03 designated A/B probe blocks being disjoint
makes each actual ν pair of freed probe subsets disjoint.
No disjointness of sampled PRIME VALUES is assumed. -/
theorem source_original_true_pattern_freed_pair_disjoint434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m) :
    Disjoint ν.1 ν.2 := by
  classical
  obtain ⟨_,hAsub,_,hBsub⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  have hzBlockA : z.1 ∈ blockA :=
    (Finset.mem_product.mp (hAsub hzA)).1
  have hzBlockB : z.1 ∈ blockB :=
    (Finset.mem_product.mp (hBsub hzB)).1
  exact (Finset.disjoint_left.mp hBlocks) hzBlockA hzBlockB

/-- For the TRUE original comparison pattern ν, the
literal first-J SHARED slot count in the source03
multiplicity-preserving physical dilation is
  |G| J - (|νA|+|νB|).
The freed prime tuples depend on ν but the count is
determined by its ORIGINAL probe sets. -/
theorem source_original_true_pattern_shared_count434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m) :
    (∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card)
      + (ν.1.card+ν.2.card) =
      (Fintype.card G)*J :=
  source_original_true_actual_shared_slot_count434
    J ell m hmJ ν
      (source_original_true_pattern_freed_pair_disjoint434
        blockA blockB hBlocks m ν hν)

/-- Exact parity identity for the actual shared PRIME SLOT
multiplicities in one SOURCE03 comparison pattern. This
connects the mixed-endpoint shared-dilation sign with
the freed-probe parity whose two-block sum does not cancel.
Only arithmetic of -1, not signed ideal transference. -/
theorem source_original_true_pattern_shared_parity434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m) :
    let R := ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    ((-1:ℂ)^R) =
      ((-1:ℂ)^((Fintype.card G)*J)) *
      ((-1:ℂ)^(ν.1.card+ν.2.card)) := by
  classical
  let R := ∑ g : G,
    (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let n := ν.1.card+ν.2.card
  have hCount : R+n=Fintype.card G*J :=
    source_original_true_pattern_shared_count434
      blockA blockB hBlocks J ell m hmJ ν hν
  have hSquare : ((-1:ℂ)^n)*((-1:ℂ)^n)=1 := by
    calc
      _ = ((-1:ℂ)*(-1))^n :=
        (mul_pow (-1:ℂ) (-1:ℂ) n).symm
      _ = 1 := by norm_num
  calc
    (-1:ℂ)^R = (-1:ℂ)^R*1 := by ring
    _ = (-1:ℂ)^R*((-1:ℂ)^n *(-1:ℂ)^n) := by rw [hSquare]
    _ = ((-1:ℂ)^(R+n))*((-1:ℂ)^n) := by rw [pow_add];ring
    _ = ((-1:ℂ)^((Fintype.card G)*J))*((-1:ℂ)^n) := by rw [hCount]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFourEndpointParityTotals -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- ACTUAL original SOURCE03 MIXED ENDPOINT PARITY sign sum.
The literal shared label multiplicities depend on each ν,
and the signed family total is NOT the usual -1:
it is -(±1) times the exact actual pattern count.
This proves rigorously why a common-twist-only
transference estimate is insufficient for all FOUR
independently signed endpoint channels. -/
theorem source_original_true_mixed_shared_sign_sum434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J) :
    let R := fun ν : SourceOriginalProbePattern434 G m =>
      ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    (∑ ν ∈ family,
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (-1:ℂ)^(R ν)) =
      -((-1:ℂ)^((Fintype.card G)*J)) * (family.card:ℂ) := by
  classical
  let R := fun ν : SourceOriginalProbePattern434 G m =>
    ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let R0 := (Fintype.card G)*J
  have hTerm (ν : SourceOriginalProbePattern434 G m)
      (hν : ν ∈ family) :
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
        (-1:ℂ)^(R ν) =
      (-1:ℂ)^R0 *
        ((-((-1:ℂ)^(ν.1.card+ν.2.card))) *
          (-1:ℂ)^(ν.1.card+ν.2.card)) := by
    have hh := source_original_true_pattern_shared_parity434
      blockA blockB hBlocks J ell m hmJ ν hν
    change (-1:ℂ)^(R ν) =
      (-1:ℂ)^R0 * (-1:ℂ)^(ν.1.card+ν.2.card) at hh
    rw [hh]
    ring
  have hCombi :
      (∑ ν ∈ family,
        (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
          (-1:ℂ)^(ν.1.card+ν.2.card)) =
      -(family.card:ℂ) := by
    have hh := source_original_true_mixed_endpoint_freed_parity_sum434
      blockA blockB m
    exact_mod_cast hh
  calc
    _ = ∑ ν ∈ family, (-1:ℂ)^R0 *
        ((-((-1:ℂ)^(ν.1.card+ν.2.card))) *
          (-1:ℂ)^(ν.1.card+ν.2.card)) := by
          apply Finset.sum_congr rfl
          intro ν hν
          exact hTerm ν hν
    _ = (-1:ℂ)^R0 *
        (∑ ν ∈ family,
          (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
            (-1:ℂ)^(ν.1.card+ν.2.card)) := by
          rw [Finset.mul_sum]
    _ = -((-1:ℂ)^R0) * (family.card:ℂ) := by
          rw [hCombi]
          ring

/-- The FOUR independent SOURCE03 endpoint parity choices
have TWO algebraically distinct channel totals. Common
choices 00/11 retain the exact alternating -1; mixed
01/10 have the actual shared-slot pattern count instead.
This is a pure arithmetic obstruction to treating
independent signs as the SAME ideal residual theorem.
The distinct signed C6 physical estimates are unaffected
in norm, but B signed transference still needs its OWN proof. -/
theorem source_original_true_four_shared_endpoint_sign_totals434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (hA : (sourceOriginalProbeBlock434 blockA m).Nonempty)
    (hB : (sourceOriginalProbeBlock434 blockB m).Nonempty)
    (epsSrc epsTgt : Bool) :
    let R := fun ν : SourceOriginalProbePattern434 G m =>
      ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    (∑ ν ∈ family,
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
        (if epsSrc then (-1:ℂ)^(R ν) else 1) *
        (if epsTgt then (-1:ℂ)^(R ν) else 1)) =
      if epsSrc = epsTgt then -1
      else -((-1:ℂ)^((Fintype.card G)*J)) *
        (family.card:ℂ) := by
  classical
  let R := fun ν : SourceOriginalProbePattern434 G m =>
    ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  have hCommon :
      (∑ ν ∈ family,
        -((-1:ℂ)^(ν.1.card+ν.2.card))) = -1 := by
    have hh := source_original_true_two_block_signed_pattern_total434
      blockA blockB m hA hB
    exact_mod_cast hh
  have hMixed := source_original_true_mixed_shared_sign_sum434
    blockA blockB hBlocks J ell m hmJ
  cases epsSrc <;> cases epsTgt
  · simpa [R,family] using hCommon
  · simpa [R,family] using hMixed
  · simpa [R,family,mul_comm,mul_left_comm,mul_assoc] using hMixed
  · have hNorm (ν : SourceOriginalProbePattern434 G m) :
        (-1:ℂ)^(R ν) * (-1:ℂ)^(R ν) = 1 := by
      calc
        _ = ((-1:ℂ)*(-1))^(R ν) :=
          (mul_pow (-1:ℂ) (-1:ℂ) (R ν)).symm
        _ = 1 := by norm_num
    calc
      (∑ ν ∈ family,
        -((-1:ℂ)^(ν.1.card+ν.2.card)) *
          (-1:ℂ)^(R ν) * (-1:ℂ)^(R ν)) =
      ∑ ν ∈ family,
        -((-1:ℂ)^(ν.1.card+ν.2.card)) := by
          apply Finset.sum_congr rfl
          intro ν hν
          rw [mul_assoc,hNorm ν,mul_one]
      _ = -1 := hCommon
end Green64Analytic.CorrelationSquare

end

/-! ## code.characterExpansion -/

section

open scoped BigOperators
open MeasureTheory

namespace Green64CorrelationFinite

/-- Exact finite statement; see SOURCE_INTERFACE_AUDIT.md for its partial scope. -/
def Expected_characterExpansion : Prop :=
∀ (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ),
 (∀ u, ‖F u‖ ≤ 1) →
 (∀ v : (ZMod q)ˣ, F v = ∑ χ : DirichletCharacter ℂ q,
   ((q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u * star (χ (u : ZMod q))) * χ (v : ZMod q)) ∧
 (∀ χ : DirichletCharacter ℂ q,
   ‖(q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u * star (χ (u : ZMod q))‖ ≤ 1)

 theorem characterExpansion : Expected_characterExpansion :=
by
  have characterExpansionInv : ∀ (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ) (v : (ZMod q)ˣ),
 F v = ∑ χ : DirichletCharacter ℂ q,
   ((q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u * χ ((u : ZMod q)⁻¹)) * χ (v : ZMod q) := by
   intro q _ F v
   classical
   have hφ : (q.totient : ℂ) ≠ 0 := by
     exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
   have horth (u : (ZMod q)ˣ) :
       (∑ χ : DirichletCharacter ℂ q, χ ((u : ZMod q)⁻¹)*χ (v : ZMod q)) =
         if u=v then (q.totient : ℂ) else 0 := by
     simpa only [Units.val_inj] using
       DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit (v : ZMod q)
   symm
   calc
     _ = (q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u *
         (∑ χ : DirichletCharacter ℂ q, χ ((u : ZMod q)⁻¹)*χ (v : ZMod q)) := by
       simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
       rw [Finset.sum_comm]
     _ = F v := by
       simp only [horth]
       simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
       field_simp
  have characterInvConj : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ),
 χ ((u : ZMod q)⁻¹) = star (χ (u : ZMod q)) := by
   intro q χ u
   have hn : ‖χ (u : ZMod q)‖ = 1 := χ.unit_norm_eq_one u
   have hz : χ (u : ZMod q) ≠ 0 := by
     intro h
     rw [h,norm_zero] at hn
     norm_num at hn
   apply mul_left_cancel₀ hz
   have hm : χ (u : ZMod q)*χ ((u : ZMod q)⁻¹) = 1 := by
     rw [← map_mul]
     simp
   rw [hm]
   have hh := (RCLike.mul_conj (χ (u : ZMod q))).symm
   rw [hn] at hh
   norm_num at hh
   exact hh
  intro q _ F hF
  constructor
  · intro v
    simpa only [characterInvConj] using characterExpansionInv q F v
  · intro χ
    have hφ : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    have hs : ‖∑ u : (ZMod q)ˣ, F u*star (χ (u : ZMod q))‖ ≤ (q.totient : ℝ) := by
      calc
        _ ≤ ∑ u : (ZMod q)ˣ, ‖F u*star (χ (u : ZMod q))‖ := norm_sum_le _ _
        _ ≤ ∑ u : (ZMod q)ˣ, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          simpa only [norm_mul,norm_star,χ.unit_norm_eq_one u,mul_one] using hF u
        _ = q.totient := by simp [ZMod.card_units_eq_totient]
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (q.totient : ℝ)⁻¹*(q.totient : ℝ) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (le_of_lt hφ))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hφ)

example : (∀ (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ),
 (∀ u, ‖F u‖ ≤ 1) →
 (∀ v : (ZMod q)ˣ, F v = ∑ χ : DirichletCharacter ℂ q,
   ((q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u * star (χ (u : ZMod q))) * χ (v : ZMod q)) ∧
 (∀ χ : DirichletCharacter ℂ q,
   ‖(q.totient : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, F u * star (χ (u : ZMod q))‖ ≤ 1)) := characterExpansion
end Green64CorrelationFinite

end

