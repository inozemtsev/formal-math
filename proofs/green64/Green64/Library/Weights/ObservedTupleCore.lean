module

public import Green64.Library.Weights.SelectedOrdinaryQuotient
public import Green64.Library.Weights.LiteralD61StrippedCore

@[expose] public section

/-!
# Weights / ObservedTupleCore

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ObservedTupleCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

-- The private finite stripping proof below is retained from B589.
-- New public consumers apply it to the entire observed sigma carrier.
private theorem b602_selected_mark_product_ordinary_quotient
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

/-- Every observed marked prime is stripped simultaneously. The full
observed product divides the physical endpoint, and its removal leaves
the original ordinary P-free part unchanged. No hidden completion is
chosen, and the observed counts may vary by group. -/
theorem b602_observed_tuple_ordinary_quotient434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (c : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (w : ℕ) (hw : 0 < w)
    (a : ∀ g, Fin (c g) → ℕ) (ha : a ∈ bigMarkLists P c w) :
    let X := ∏ g, ∏ i : Fin (c g), a g i
    X ∣ w ∧ 0 < w/X ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (w/X) := by
  have h := b602_selected_mark_product_ordinary_quotient
    P c hPrime hDisj w hw a ha
    (Function.Embedding.refl (Σ g : G, Fin (c g)))
  change (∏ z : Σ g : G, Fin (c g), a z.1 z.2) ∣ w ∧
    0 < w/(∏ z : Σ g : G, Fin (c g), a z.1 z.2) ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (w/(∏ z : Σ g : G, Fin (c g), a z.1 z.2)) at h
  simpa only [Fintype.prod_sigma] using h

/-- The original full-Delta Q core on an observed marked carrier is
bounded by the stripped quotient divisor square. The observed product
does not introduce a divisor-count factor of its own. -/
theorem b602_original_full_D20_observed_core_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (c : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (w : ℕ) (hw : 0 < w)
    (marks : ∀ g, Fin (c g) → ℕ) (hmarks : marks ∈ bigMarkLists P c w)
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ‖primeSlotCoreValue P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁) w‖ ≤
      ((w/(∏ g, ∏ i : Fin (c g), marks g i)).divisors.card : ℝ)^2 := by
  obtain ⟨_hX,hu,ho⟩ := b602_observed_tuple_ordinary_quotient434
    P c hPrime hDisj w hw marks hmarks
  let X := ∏ g, ∏ i : Fin (c g), marks g i
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁
  have he : primeSlotCoreValue P F w = primeSlotCoreValue P F (w/X) := by
    unfold primeSlotCoreValue
    rw [ho]
  change ‖primeSlotCoreValue P F w‖ ≤ _
  rw [he]
  exact b589_actual_full_D20_sorted_Q_core_norm434
    P r d L hr hL b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ _ hu

/-- The literal sigma=1 D61 alpha, with both original power masks and
terminal clip, on an arbitrary original observed marked tuple. -/
theorem b602_literal_sigma_one_D61_observed_core_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (c : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (w : ℕ) (hw : 0 < w)
    (marks : ∀ g, Fin (c g) → ℕ) (hmarks : marks ∈ bigMarkLists P c w)
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (a eta b0 : ℝ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ‖primeSlotCoreValue P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q χ σ₀ σ₁) w‖ ≤
      ((w/(∏ g, ∏ i : Fin (c g), marks g i)).divisors.card : ℝ)^2 := by
  rw [b589_original_sigma_one_D61_core_identity434]
  exact b602_original_full_D20_observed_core_bound434
    P c hPrime hDisj w hw marks hmarks r d L hr hL b slot δ ξ
    (b589OriginalD61MaskedK a eta b0 L K)
    (L^(-(1:ℝ))) (Real.exp (Real.sqrt L)) ((Real.exp L)^a) hWy q χ σ₀ σ₁

/-- Both actual original P-band D61 cores, with independent observed
counts and lists. This directly supplies the observed physical carrier
used after hidden-slot summation, without selecting w-dependent full
mark completions or asserting a moment for their union. -/
theorem b602_literal_P_sigma_one_D61_two_observed_core_bound434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (c c' : sourceOriginalPAllGroupType r L → ℕ)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (marks : ∀ g, Fin (c g) → ℕ)
    (marks' : ∀ g, Fin (c' g) → ℕ)
    (hmarks : marks ∈ bigMarkLists (sourceOriginalPAllActualBands r L) c w)
    (hmarks' : marks' ∈ bigMarkLists (sourceOriginalPAllActualBands r L) c' wp)
    (b b' : Fin (d+1)) (slot slot' : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
    (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
    (K K' : Finset ℕ) (a eta b0 : ℝ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (q q' : ℕ) (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (σ₀ σ₁ σ₀' σ₁' : ℝ) :
    let P := sourceOriginalPAllActualBands r L
    let F := sourceNativePrimeCore r d L b slot δ ξ K
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q χ σ₀ σ₁
    let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q' χ' σ₀' σ₁'
    ‖primeSlotCoreValue P F w * star (primeSlotCoreValue P F' wp)‖ ≤
      ((w/(∏ g, ∏ i : Fin (c g), marks g i)).divisors.card : ℝ)^2 *
      ((wp/(∏ g, ∏ i : Fin (c' g), marks' g i)).divisors.card : ℝ)^2 := by
  dsimp only
  have hs := b602_literal_sigma_one_D61_observed_core_bound434
    (sourceOriginalPAllActualBands r L) c
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    w hw marks hmarks r d L hr hL b slot δ ξ K a eta b0 hWy q χ σ₀ σ₁
  have ht := b602_literal_sigma_one_D61_observed_core_bound434
    (sourceOriginalPAllActualBands r L) c'
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    wp hwp marks' hmarks' r d L hr hL b' slot' δ' ξ' K' a eta b0 hWy q' χ' σ₀' σ₁'
  rw [norm_mul,norm_star]
  exact mul_le_mul hs ht (norm_nonneg _) (sq_nonneg _)
end Green64Analytic.ShiftTwoTerminal

end

end

