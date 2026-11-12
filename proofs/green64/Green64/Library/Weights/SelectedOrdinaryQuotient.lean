module

public import Green64.Library.Weights.Part099
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part042

@[expose] public section

/-!
# Weights / SelectedOrdinaryQuotient

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSelectedOrdinaryQuotient -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Internal finite support argument: an actual selected embedding of
original distinct marked lists is an injective list of P-prime divisors.
Its product divides the physical endpoint and disappears completely
from that endpoint's ordinary part. No squarefree assumption on w. -/
private theorem selected_mark_product_ordinary_quotient
    {G ι : Type} [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι]
    (P : G → Finset ℕ) (t : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (w : ℕ) (hw : 0 < w) (a : ∀ g, Fin (t g) → ℕ)
    (ha : a ∈ bigMarkLists P t w)
    (e : ι ↪ (Σ g : G, Fin (t g))) :
    let X := ∏ z : ι, a (e z).1 (e z).2
    X ∣ w ∧ 0 < w/X ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (w/X) := by
  classical
  dsimp only
  let label : ι → ℕ := fun z => a (e z).1 (e z).2
  have hmem : ∀ g i, a g i ∈ P g := by
    intro g i
    have hg := Fintype.mem_piFinset.mp ha g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).1
  have hdvd : ∀ g i, a g i ∣ w := by
    intro g i
    have hg := Fintype.mem_piFinset.mp ha g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).2
  have hinj : Function.Injective (fun z : Σ g : G, Fin (t g) => a z.1 z.2) := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    dsimp only at he
    have hgh : g=h := hDisj g h (a g i) (hmem g i) (he.symm ▸ hmem h j)
    subst h
    have hg := Fintype.mem_piFinset.mp ha g
    have hi : Function.Injective (a g) := (Finset.mem_filter.mp hg).2
    have hij : i=j := hi he
    subst j
    rfl
  have hlabel : Function.Injective label := hinj.comp e.injective
  have hp : ∀ z, (label z).Prime := by
    intro z
    exact hPrime (e z).1 (label z) (hmem _ _)
  have hP : ∀ z, label z ∈ Finset.univ.biUnion P := by
    intro z
    exact Finset.mem_biUnion.mpr ⟨(e z).1,Finset.mem_univ _,hmem _ _⟩
  have hpos : 0 < ∏ z, label z := Finset.prod_pos (fun z hz => (hp z).pos)
  have hsub : Finset.univ.image label ⊆ w.primeFactors := by
    intro p hp'
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp'
    exact Nat.mem_primeFactors.mpr ⟨hp z,hdvd _ _,hw.ne'⟩
  have hprod : (∏ p ∈ Finset.univ.image label, p) = ∏ z, label z := by
    rw [Finset.prod_image]
    intro z hz v hv he
    exact hlabel he
  have hX : (∏ z, label z) ∣ w := by
    rw [← hprod]
    exact (Finset.prod_dvd_prod_of_subset (Finset.univ.image label)
      w.primeFactors (fun p => p) hsub).trans (Nat.prod_primeFactors_dvd w)
  have hu : 0 < w/(∏ z, label z) := Nat.div_pos (Nat.le_of_dvd hw hX) hpos
  have hmul : (∏ z, label z)*(w/(∏ z, label z)) = w := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hX
  have ho := source_auxiliary_original_labelled_outside_invariant434
    (Finset.univ : Finset ι) label (Finset.univ.biUnion P) (w/(∏ z,label z))
    (fun z hz => hp z) (fun z hz => hP z) hu
  rw [hmul,source_native_B521_fock_outside_eq_T_original_ordinary434,
    source_native_B521_fock_outside_eq_T_original_ordinary434] at ho
  exact ⟨hX,hu,ho⟩

/-- Both ORIGINAL physical selected products divide their own endpoint.
Both ordinary-part identities use the literal free-slot embeddings and
all original marks. These discharge the arithmetic premises of B587. -/
theorem b589_actual_original_probe_both_ordinary_quotients434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
    (XB ∣ w ∧ 0 < w/XB ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (w/XB)) ∧
    (XA ∣ wp ∧ 0 < wp/XA ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) wp =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (wp/XA)) := by
  constructor
  · exact selected_mark_product_ordinary_quotient
      P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) hPrime hDisj
      w hw a ha (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ nu)
  · exact selected_mark_product_ordinary_quotient
      P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) hPrime hDisj
      wp hwp b hb (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ nu)

/-- The actual source endpoint Q core is bounded at the stripped
quotient w/X_B. X_B is the original selected product, extracted from
bigMarkLists; full Delta and exact QSkip factorials are built in.
In particular, NO tau(X_B) factor or core-smallness premise occurs. -/
theorem b589_actual_original_source_Qcore_stripped434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (w : ℕ) (hw : 0 < w)
    (a : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ‖primeSlotCoreValue P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁) w‖ ≤
      ((w/sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a).divisors.card : ℝ)^2 := by
  obtain ⟨hX,hu,ho⟩ := selected_mark_product_ordinary_quotient
    P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) hPrime hDisj
    w hw a ha (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ nu)
  change sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
    sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (w/sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a) at ho
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁
  have he : primeSlotCoreValue P F w = primeSlotCoreValue P F
      (w/sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a) := by
    unfold primeSlotCoreValue
    rw [ho]
  change ‖primeSlotCoreValue P F w‖ ≤ _
  rw [he]
  exact b589_actual_full_D20_sorted_Q_core_norm434
    P r d L hr hL b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ _ hu

/-- The independently selected target endpoint retains its own original
A-block product and its own full Q core. No source/target symmetry or
substitution of the physical slots is assumed. -/
theorem b589_actual_original_target_Qcore_stripped434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (wp : ℕ) (hwp : 0 < wp)
    (a : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ‖primeSlotCoreValue P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁) wp‖ ≤
      ((wp/sourceOriginalProbeFreeTargetX434 J ell m hmJ nu a).divisors.card : ℝ)^2 := by
  obtain ⟨hX,hu,ho⟩ := selected_mark_product_ordinary_quotient
    P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) hPrime hDisj
    wp hwp a ha (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ nu)
  change sourceOriginalOrdinaryPart (Finset.univ.biUnion P) wp =
    sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (wp/sourceOriginalProbeFreeTargetX434 J ell m hmJ nu a) at ho
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁
  have he : primeSlotCoreValue P F wp = primeSlotCoreValue P F
      (wp/sourceOriginalProbeFreeTargetX434 J ell m hmJ nu a) := by
    unfold primeSlotCoreValue
    rw [ho]
  change ‖primeSlotCoreValue P F wp‖ ≤ _
  rw [he]
  exact b589_actual_full_D20_sorted_Q_core_norm434
    P r d L hr hL b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ _ hu
end Green64Analytic.ShiftTwoTerminal

end

end

