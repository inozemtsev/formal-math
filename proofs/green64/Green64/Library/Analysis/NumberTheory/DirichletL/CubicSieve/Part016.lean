module

public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.Initial
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Norm -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I hI.2).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J hJ.2).1

theorem idealSymbol_eq_idealSexticRow_sq
    (F : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hI : I ∈ F) (hsq : Squarefree I) (z : O) :
    eisEmbedding (CubicJacobiGlobal.idealSymbol I z) =
      (idealSexticRow F hFp hFg I z) ^ 2 := by
  rw [← CanonicalRowCompletion.idealRowHom_square]
  congr 1
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFp
  conv_lhs => rw [← idealSupport_product_eq F hI hsq, map_prod]
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact CanonicalRowCompletion.idealRowHom_prime z i.val (primePool_good F hFg i)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I ((mem_idealRange.mp hI).1.2)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_cubic_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (idealMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      (idealSexticRow F hFp hFg J.val z) ^ 2 * a J
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val (primaryGenerator I.val)) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dite_eq_left J.property]
    rfl
  rw [heR, hea] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Extraction -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primary_extracted_parts (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryGenerator (firstPart I) ≠ 0 ∧ primaryGenerator (secondPart I) ≠ 0 ∧
      primaryGenerator (cubePart I) ≠ 0 := by
  have he := congrArg primaryGeneratorHom
    (cubic_factorization I (primaryGenerator_ne_zero_ideal I hI))
  simp only [map_mul, map_pow] at he
  change primaryGenerator I = primaryGenerator (firstPart I) *
    primaryGenerator (secondPart I) ^ 2 * primaryGenerator (cubePart I) ^ 3 at he
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem firstPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (firstPart I) := ⟨firstPart_squarefree I, (primary_extracted_parts I hI).1⟩

theorem secondPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (secondPart I) := ⟨secondPart_squarefree I, (primary_extracted_parts I hI).2.1⟩

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Elements -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (I : Ideal O) (hI : primaryGenerator I ≠ 0) : O →* ℂ where
  toFun x := eisEmbedding (CubicJacobiGlobal.idealSymbol I x)
  map_one' := by rw [CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' x y := by rw [CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal O) (B : b → Ideal O) (D : c → O)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

def goodPart (I : Ideal O) : Ideal O := CanonicalQuadraticSieve.goodSquarefreePart I

def badPart (I : Ideal O) : Ideal O :=
  ∏ P ∈ CanonicalQuadraticSieve.badPrimeSupport I, P

theorem goodPart_admissible (I : Ideal O) : Admissible (goodPart I) := by
  have h := CanonicalQuadraticSieve.goodSquarefreePart_admissible I
  exact ⟨h.2.1, CanonicalQuadraticSieve.primaryGenerator_admissible _ h⟩

theorem badPart_mul_goodPart (I : Ideal O) (hI : Squarefree I) :
    badPart I * goodPart I = I := CanonicalQuadraticSieve.squarefree_bad_good_product I hI

def extractedGenerator (I : Ideal O) : O :=
  primaryGenerator (goodPart (firstPart I)) *
    primaryGenerator (goodPart (secondPart I)) ^ 2 *
    idealGenerator (cubePart I) ^ 3 *
    (idealGenerator (badPart (firstPart I)) * idealGenerator (badPart (secondPart I)) ^ 2)

theorem span_extractedGenerator (I : Ideal O) (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {idealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {idealGenerator (badPart (firstPart I))} *
      Ideal.span {idealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_idealGenerator, span_idealGenerator, span_idealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction (z : O) (hz : z ≠ 0) :
    ∃ u : Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector (I : Ideal O) :
    ∃ E : CanonicalQuadraticSieve.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := by
  exact ⟨⟨CanonicalQuadraticSieve.badPrimeSupport I,
    Finset.mem_powerset.mpr (CanonicalQuadraticSieve.badPrimeSupport_subset I)⟩, rfl⟩

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FullExtraction -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
      CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * idealGenerator d.2.2.2.val ^ 3 *
    (idealGenerator (∏ P ∈ d.2.1.val, P) * idealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
    CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryGenerator p.2.2.val *
    primaryGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryGenerator (goodPart (firstPart I)) *
      primaryGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * idealGenerator (cubePart I) ^ 3 *
          (idealGenerator (∏ P ∈ e.val, P) * idealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D = 96 * (cubeImage R).card := by
    have hu : Fintype.card Oˣ = 6 := by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp only [D, Fintype.card_prod, Fintype.card_coe, hu,
      CanonicalQuadraticSieve.fixedBadPrimes_powerset_card]
    omega
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryGenerator i.val * primaryGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  dsimp only [D] at hcard
  convert hb using 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_coe]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ExtractionBounds -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast CanonicalQuadraticSieve.goodSquarefreePart_norm_le I hI

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    DescentFiberCost.finite_ideal_count_real _ X hX
      (fun I hI => primaryGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    DescentFiberCost.finite_ideal_count_real _ Y hY
      (fun I hI => primaryGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Dyadic -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

def extractionLabel (M : ℝ) (z : O) :
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.DescentProfiles -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
          paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hk⟩ := paperRadialFourier_log_separation_envelope W V ak M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b, ?_, hi, hb, hp⟩
  exact descent_profile_identity g₁ g₂ W V a₁ a₂ ak R b he

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

theorem source_descent_profile_separation {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) * paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  obtain ⟨C, hC, hsep⟩ := descent_profile_separation g₁ g₂ Φ V a₁ a₂ ak M hM hV A J
  let I₁ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₁) t‖
  let I₂ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₂) t‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun t => by positivity)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun t => by positivity)
  refine ⟨𝓕 g₁, 𝓕 g₂, I₁ * I₂ * C, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, heq, hi, hb, hp⟩ := hsep R hR
  refine ⟨b₃, ?_, tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  · simpa only [g₁, g₂, CubicReflectionKernel.logSchwartz_apply] using heq
  · rw [tripleCoefficient_weighted_integral]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hI₁ hI₂)
    convert hh using 1 ; dsimp only [I₁, I₂] ; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualProfiles -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def inverseNormWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.exp y : ℂ)
def inverseRootWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.sqrt (Real.exp y) : ℂ)

def firstRootWindows (V : Fin 9 → ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![V 0, V 1, V 2, inverseNormWindow (V 3), inverseRootWindow (V 4),
    inverseNormWindow (V 5), V 6, inverseRootWindow (V 7), inverseRootWindow (V 8)]

def firstLeftSlope : Fin 9 → ℝ := ![1, 0, 1, 0, 0, 1, 0, 1, 0]
def firstRightSlope : Fin 9 → ℝ := ![0, 1, 1, 0, 0, 1, 0, 0, 1]
def firstKernelSlope : Fin 9 → ℝ := ![0, 0, 0, -1, -1, -2, 1, -1, -1]

def secondRootWindows (V : Fin 6 → ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![V 0, inverseNormWindow (V 1), inverseNormWindow (V 2), V 3,
    inverseRootWindow (V 4), inverseRootWindow (V 5)]

def secondLeftSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 1, 0]
def secondRightSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 0, 1]
def secondKernelSlope : Fin 6 → ℝ := ![0, -1, -2, 1, -1, -1]

def firstPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (∏ i, firstRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, firstLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, firstRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, firstKernelSlope i * y i))

def secondPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (∏ i, secondRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, secondLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, secondRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, secondKernelSlope i * y i))

def profileMode {ι : Type*} [Fintype ι] (V : ι → ℝ → ℂ)
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) : ℂ :=
  ∏ i, V i (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem first_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M hM hU A J

theorem second_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M hM hU A J

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.DescentHeight -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := paperRadialFourier_log_separation_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.IdealMasks -/

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem prime_mem_support_iff_dvd (P A : Ideal ActualEisensteinCubic.O)
    (hP : Prime P) (hA : A ≠ 0) :
    P ∈ IdealMobiusDivisorSum.primeSupport A ↔ P ∣ A := by
  simp only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hA, hP, true_and]

theorem ideal_primeMark_eq_divisibility {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P)
    (A : Ideal ActualEisensteinCubic.O) (hA : A ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport A) =
      ∏ i ∈ I, ∑ P ∈ L i, if P ∣ A then a i P else 0 := by
  unfold primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro P hP
  simp only [prime_mem_support_iff_dvd P A (hL i hi P hP) hA]

theorem ideal_primeSupport_mul_cube (n b : Ideal ActualEisensteinCubic.O)
    (hn : n ≠ 0) (hb : b ≠ 0) :
    IdealMobiusDivisorSum.primeSupport (n * b ^ 3) =
      IdealMobiusDivisorSum.primeSupport n ∪ IdealMobiusDivisorSum.primeSupport b := by
  simp only [IdealMobiusDivisorSum.primeSupport,
    normalizedFactors_mul hn (pow_ne_zero 3 hb), normalizedFactors_pow,
    Multiset.toFinset_add]
  congr 1
  ext P
  simp

theorem ideal_whole_mark_priority {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (n b : Ideal ActualEisensteinCubic.O) (hn : n ≠ 0) (hb : b ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport (n * b ^ 3)) =
      ∑ J ∈ I.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport n) *
        primeMark (I \ J) L a
          (IdealMobiusDivisorSum.primeSupport b \ IdealMobiusDivisorSum.primeSupport n) := by
  rw [ideal_primeSupport_mul_cube n b hn hb]
  exact primeMark_priority _ _ _ _ _

theorem ideal_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
      (a : σ → Ideal ActualEisensteinCubic.O → ℂ),
      (I : Set σ).PairwiseDisjoint L →
      (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) →
      ∀ A : Ideal ActualEisensteinCubic.O, A ≠ 0 →
        ‖primeMark I L a (IdealMobiusDivisorSum.primeSupport A)‖ ≤
          C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro σ _ I L a hL ha A hA
  exact (primeMark_norm_le_divisor_count I L a _ hL ha).trans (hb A hA)

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

theorem idealZeroMask_primary_indicator
    (D B : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0)
    (hB : CompletedGauss.primaryGenerator B ≠ 0) :
    CanonicalQuadraticSieve.idealZeroMask D (CompletedGauss.primaryGenerator B) =
      if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {CompletedGauss.primaryGenerator B} =
      Ideal.span {ConcretePrimeRowBridge.idealGenerator B} := by
    rw [(CompletedGauss.primaryGenerator_spec B hB).1,
      ConcretePrimeRowBridge.span_idealGenerator]
  rw [CanonicalQuadraticSieve.idealZeroMask_span_eq D _ _ he,
    CanonicalQuadraticSieve.idealZeroMask_generator_eq_indicator D B hD]

theorem hybrid_quadratic_square_mask
    (k n b c m h t : Ideal ActualEisensteinCubic.O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) := by
  have he : n * b = (c * t) ^ 2 * (m * h) := by rw [hn, hb]; ring
  rw [he, CanonicalQuadraticSieve.canonical_quadraticRow_primary_squarefree k hk,
    idealZeroMask_primary_indicator k (c * t) hk.1 hct]
  rw [isCoprime_comm]

theorem hybrid_double_mask_mobius
    (k P c : Ideal ActualEisensteinCubic.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal ActualEisensteinCubic.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal ActualEisensteinCubic.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := QuadraticSquarefreeKernel.squarefreePart b
  let t := QuadraticSquarefreeKernel.squarePart b
  let c := gcd n g
  let m := CanonicalQuadraticSieve.idealQuotient c n
  let h := CanonicalQuadraticSieve.idealQuotient c g
  have hg : Squarefree g := QuadraticSquarefreeKernel.squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (CanonicalQuadraticSieve.idealQuotient_mul hcn).symm
  have hgh : g = c * h := (CanonicalQuadraticSieve.idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (QuadraticSquarefreeKernel.squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    QuadraticSquarefreeKernel.squarePart_ne_zero hb⟩

theorem ideal_product_fiber_card
    (s t : Finset (Ideal ActualEisensteinCubic.O))
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    (((s ×ˢ t).filter (fun p => p.1 * p.2 = J)).card) ≤ (idealDivisors J).card :=
  CanonicalQuadraticSieve.product_fiber_card (s ×ˢ t) J hJ

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O))
    (B J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Gcd -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I z)

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact SevenEighths.InverseMoment.ideal_coprime_mobius D _ (primaryGenerator_ne_zero_ideal D hD)

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

lemma cubic_admissible_quotient {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) :=
  cubic_admissible_of_dvd hI (CanonicalQuadraticSieve.idealQuotient_dvd hD)

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact cubicRow_mul _ _ _

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      rw [← CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [cubicGcdTerm, ite_eq_right hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [cubicGcdTerm, ite_eq_right hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [cubicGcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (CanonicalQuadraticSieve.mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => cubicRow (cols j) z * a j)

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FullNorm -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementRange (M : ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌊M⌋₊).filter
    (fun z => z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)

lemma mem_elementRange (M : ℝ) (z : O) :
    z ∈ elementRange M ↔ z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_qNat_le
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Nat.le_floor h.2

def elementMatrix (M N : ℝ) : Matrix (elementRange M) (idealRange N) ℂ :=
  fun z J => cubicRow J.val z.val

def elementSieveNorm (M N : ℝ) : ℝ := squaredNorm (elementMatrix M N)

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    exact Subtype.ext (primaryGenerator_inj_on_cubic_admissible
      (mem_idealRange.mp I.property).1 (mem_idealRange.mp J.property).1 he)
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

lemma elementSieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    elementSieveNorm M N ≤ elementSieveNorm M' N' := by
  apply element_family_squared_norm_le (fun z : elementRange M => z.val)
    (fun I : idealRange N => I.val) Subtype.val_injective Subtype.val_injective
  · intro z
    exact ⟨((mem_elementRange M z.val).mp z.property).1,
      ((mem_elementRange M z.val).mp z.property).2.trans hM⟩
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hN⟩

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N hN hN (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

theorem elementSieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    elementSieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ elementRange M, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact ((mem_elementRange M z).mp hz).2
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, cubicRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    change aext J.val * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM (elementRange M) hR
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [aext, dite_eq_left J.property]
    rfl
  simp_rw [hinner] at he
  rw [hea, ← Finset.sum_coe_sort] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ExtractionOptimization -/

section

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
      _ ≤ _ := cube_scale_power M T ξ hT hTM (by linarith)
  have hn : (M/T)^(1/3 : ℝ)*W*N ≤ M^(1/3 : ℝ)*N := by
    apply mul_le_mul_of_nonneg_right _ hN
    calc
      _ ≤ (M/T)^(1/3 : ℝ)*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_left
        (extracted_linear_le W T (by linarith) hWcube) hH
      _ ≤ _ := cube_scale_power M T (1/3) hT hTM le_rfl
  have hc : (M/T)^(1/3 : ℝ)*W*(U*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
    rw [Real.mul_rpow hU hN, Real.mul_rpow (hT.le.trans hTM) hN]
    calc
      _ = ((M/T)^(1/3 : ℝ)*(W*U^(2/3 : ℝ)))*N^(2/3 : ℝ) := by ring
      _ ≤ ((M/T)^(1/3 : ℝ)*T^(2/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (extracted_monomial_le W U T (2/3) hW hU hWT (by norm_num)) hH)
          (Real.rpow_nonneg hN _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (cube_scale_power M T (2/3) hT hTM (by norm_num))
        (Real.rpow_nonneg hN _)
  nlinarith

theorem extraction_min_shape (M N X Y ξ : ℝ) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : 1 ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < X*Y^2 := by positivity
  have hM0 : 0 < M := hT.trans_le hXY
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hyx : Y ≤ X
  · apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N Y X (X*Y^2) ξ hN hY hX0.le hT hXY
      (by nlinarith) (by nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sq_nonneg Y)]) hξ
  · have hxy : X ≤ Y := (lt_of_not_ge hyx).le
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N X Y (X*Y^2) ξ hN hX hY0.le hT hXY
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hX0.le hY0.le)])
      (by nlinarith [sq_le_sq₀ hX0.le hY0.le |>.mpr hxy]) hξ

lemma cubic_cross_shape_absorb (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    (M*N)^(2/3 : ℝ) ≤ M^(1/3 : ℝ)*N + M^ξ := by
  have hM0 : 0 < M := by linarith
  have hfirst : 0 ≤ M^(1/3 : ℝ)*N := mul_nonneg (Real.rpow_nonneg hM0.le _) hN
  have hsecond : 0 ≤ M^ξ := Real.rpow_nonneg hM0.le _
  by_cases hMN : M ≤ N
  · have hN0 : 0 < N := hM0.trans_le hMN
    have hh := Real.rpow_le_rpow hM0.le hMN (by norm_num : (0 : ℝ) ≤ 1/3)
    have hm : M^(2/3 : ℝ) = M^(1/3 : ℝ)*M^(1/3 : ℝ) := by
      rw [← Real.rpow_add hM0]
      congr 1
      ring
    have hn : N^(1/3 : ℝ)*N^(2/3 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    apply le_trans _ (le_add_of_nonneg_right hsecond)
    rw [Real.mul_rpow hM0.le hN, hm]
    calc
      _ ≤ (M^(1/3 : ℝ)*N^(1/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hM0.le _))
          (Real.rpow_nonneg hN _)
      _ = _ := by rw [mul_assoc, hn]
  · have hNM : N ≤ M := (lt_of_not_ge hMN).le
    apply le_trans _ (le_add_of_nonneg_left hfirst)
    calc
      _ ≤ (M*M)^(2/3 : ℝ) := Real.rpow_le_rpow (mul_nonneg hM0.le hN)
        (mul_le_mul_of_nonneg_left hNM hM0.le) (by norm_num)
      _ = M^(4/3 : ℝ) := by
        rw [Real.mul_rpow hM0.le hM0.le, ← Real.rpow_add hM0]
        congr 1
        ring
      _ ≤ M^ξ := Real.rpow_le_rpow_of_exponent_le hM hξ

theorem extraction_min_two_power (M N X Y ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : (4/3 : ℝ) ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      2*(M^(1/3 : ℝ)*N + M^ξ) := by
  have hh := extraction_min_shape M N X Y ξ hN hX hY hXY (by linarith)
  have hc := cubic_cross_shape_absorb M N ξ hM hN hξ
  linarith

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Gauss -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicQuotientCharacter (I : Ideal O) (hI : Admissible I) : MulChar (O ⧸ I) ℂ where
  toFun := CompletedGauss.cubicRow I hI.2
  map_one' := by simp [CompletedGauss.cubicRow]
  map_mul' x y := by simp only [CompletedGauss.cubicRow, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1]
    have hcop : ¬ IsCoprime I (Ideal.span {z}) := by
      simpa only [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq] using hx
    have hc := idealSymbol_cube_mask I z hI.2
    rw [ite_eq_right hcop] at hc
    exact (eq_zero_of_pow_eq_zero hc)

@[simp] lemma cubicQuotientCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    cubicQuotientCharacter I hI (Ideal.Quotient.mk I z) = cubicRow I z :=
  CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z

lemma cubicQuotientCharacter_cube (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicQuotientCharacter_mk, cubicRow,
    idealSymbol_cube_mask I z hI.2]
  have hu : IsUnit (Ideal.Quotient.mk I z) ↔ IsCoprime I (Ideal.span {z}) := by
    rw [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq]
  by_cases h : IsUnit (Ideal.Quotient.mk I z)
  · rw [ite_eq_left (hu.mp h), MulChar.one_apply h]
  · rw [ite_eq_right (fun hcop => h (hu.mpr hcop)), MulChar.map_nonunit _ h]

lemma cubicQuotientCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI (-1) = 1 := by
  have h3 := congrArg (fun χ : MulChar (O ⧸ I) ℂ => χ (-1)) (cubicQuotientCharacter_cube I hI)
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply (isUnit_neg_one)] at h3
  have h2 : cubicQuotientCharacter I hI (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  calc
    _ = cubicQuotientCharacter I hI (-1) ^ 2 * cubicQuotientCharacter I hI (-1) := by rw [h2, one_mul]
    _ = cubicQuotientCharacter I hI (-1) ^ 3 := by ring
    _ = 1 := h3

def quotientCharacterTransport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := MulChar.map_nonunit χ (fun h => hx (by simpa using h.map e.symm.toMonoidHom))

def principalCubicCharacter (I : Ideal O) (hI : Admissible I) :
    MulChar (O ⧸ Ideal.span {primaryGenerator I}) ℂ :=
  quotientCharacterTransport (Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1)
    (cubicQuotientCharacter I hI)

@[simp] lemma principalCubicCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    principalCubicCharacter I hI (Ideal.Quotient.mk _ z) = cubicRow I z := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (Ideal.Quotient.mk _ z)) = _
  rw [Ideal.quotEquivOfEq_mk, cubicQuotientCharacter_mk]

lemma principalCubicCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    principalCubicCharacter I hI (-1) = 1 := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (-1)) = 1
  rw [map_neg, map_one, cubicQuotientCharacter_neg_one]

lemma gaussTwo_eq_gaussSum (I : Ideal O) (hI : Admissible I) :
    let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
    let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
    gaussTwo I hI.2 = gaussSum (principalCubicCharacter I hI)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (primaryGenerator I) hI.2) / (‖eisEmbedding (primaryGenerator I)‖ : ℂ) := by
  dsimp only [gaussTwo, gaussSum, principalCubicCharacter, quotientCharacterTransport, cubicQuotientCharacter]
  congr 1

lemma gaussSum_inverse_of_even {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (heven : χ (-1) = 1) :
    gaussSum χ⁻¹ ψ = star (gaussSum χ ψ) := by
  rw [star_gaussSum_eq]
  have hh : χ⁻¹ (-1) = 1 := by rw [← MulChar.star_apply', heven, star_one]
  have h := gaussSum_mulShift χ⁻¹ ψ (-1 : Rˣ)
  rw [Units.coe_neg_one, ← ψ.inv_mulShift, hh, one_mul] at h
  exact h.symm

lemma cubic_pair_cross_phase (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.mk _ (primaryGenerator J)) *
      principalCubicCharacter J hJ (Ideal.Quotient.mk _ (primaryGenerator I)) = 1 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  rw [← MulChar.star_apply', principalCubicCharacter_mk, principalCubicCharacter_mk]
  change star (idealKernel I J) * idealKernel J I = 1
  rw [← idealKernel_reciprocity I J hI.2 hJ.2]
  change star (cubicRow I (primaryGenerator J)) * cubicRow I (primaryGenerator J) = 1
  rw [cubicRow_common_mask I hI.2, (primaryGenerator_spec J hJ.2).1, ite_eq_left hcop]

def cubicPairGauss (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) : ℂ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.factor Ideal.mul_le_left x) *
      principalCubicCharacter J hJ (Ideal.Quotient.factor Ideal.mul_le_right x) *
      eisTraceProdChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates a b hI.2 hJ.2 x) /
      ((‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ))

theorem cubicPairGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    cubicPairGauss I J hI hJ = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator J}) := finite_quotient_span hJ.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator J}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) :=
    finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) := Fintype.ofFinite _
  have hc : IsCoprime (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) := by
    rwa [(primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]
  dsimp only [cubicPairGauss]
  rw [gauss_sum_actual_O ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
    (primaryGenerator I) (primaryGenerator J) hI.2 hJ.2 hc,
    cubic_pair_cross_phase I J hI hJ hcop, one_mul,
    gaussSum_inverse_of_even _ _ (principalCubicCharacter_neg_one I hI),
    gaussTwo_eq_gaussSum I hI, gaussTwo_eq_gaussSum J hJ]
  have halg (a b : ℂ) (x y : ℝ) :
      star a * b / ((x : ℂ) * (y : ℂ)) = star (a / (x : ℂ)) * (b / (y : ℂ)) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    ring
  exact halg _ _ _ _

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma primeIndex_product (I : Ideal O) (hI : Admissible I) :
    (∏ P : PrimeIndex I, P.val) = I := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI.2
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hI.1
  have hv : (CompletedGauss.primeSupport I).val = UniqueFactorizationMonoid.normalizedFactors I := by
    simpa only [CompletedGauss.primeSupport, Multiset.toFinset_val] using hnodup.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport I, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport I).val.prod := (Finset.prod_val _).symm
    _ = I := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hI0

theorem gaussTwo_norm_one (I : Ideal O) (hI : Admissible I) : ‖gaussTwo I hI.2‖ = 1 := by
  let c := primaryGenerator I
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Fintype (O ⧸ P.val) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
  have hc : Ideal.span {c} = ∏ P : PrimeIndex I, P.val :=
    (primaryGenerator_spec I hI.2).1.trans (primeIndex_product I hI).symm
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ P : PrimeIndex I, O ⧸ P.val :=
    (Ideal.quotEquivOfEq hc).trans
      (IdealGaussCRT.quotientProdEquivPi (fun P : PrimeIndex I => P.val)
        (CanonicalRowCompletion.primeIndex_pairwise_coprime I))
  let χ : ∀ P : PrimeIndex I, MulChar (O ⧸ P.val) ℂ :=
    fun P => actualSextic P.val (primeIndex_good I hI.2 P) ^ 2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hI.2
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hI.2
  have hχ : ∀ P : PrimeIndex I, χ P ≠ 1 := fun P =>
    cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) false
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun P : PrimeIndex I => O ⧸ P.val)
    e χ ψ hχ (fun P => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun P : PrimeIndex I => O ⧸ P.val) e ψ hψ P)
  have hrow (x : O ⧸ Ideal.span {c}) : (∏ P : PrimeIndex I, χ P (e x P)) =
      CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    dsimp only [c] at z ⊢
    simp only [e, c, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      IdealGaussCRT.quotientProdEquivPi_mk, CompletedGauss.cubicRow_mk, χ]
  simp_rw [hrow] at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c},
    CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI.2))

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Growth -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def HasCubicExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M + N^ξ + (M*N)^(2/3 : ℝ))

theorem hasCubicExponent_initial : HasCubicExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4*C, by positivity, ?_⟩
  intro M N hM hN
  have hN0 : 0 ≤ N := by linarith
  have hceil : (⌈N⌉₊ : ℝ) ≤ 2*N := by
    have hh := Nat.ceil_lt_add_one hN0
    linarith
  have hn : (⌈N⌉₊ : ℝ)^2 ≤ 4*N^2 := by nlinarith [sq_nonneg ((⌈N⌉₊ : ℝ) - 2*N)]
  have hp : 1 ≤ (M*N)^ε := Real.one_le_rpow (by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hN)]) hε.le
  have hx : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ C*(M+(⌈N⌉₊ : ℝ)^2) := sieveNorm_initial M N hM hN
    _ ≤ 4*C*(M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ)) := by
      rw [Real.rpow_two]
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hn), mul_nonneg hC.le hx]
    _ ≤ _ := by
      have hs : 0 ≤ M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ) := by positivity
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4*C) hs) (sub_nonneg.mpr hp)]

lemma HasCubicExponent.swapped {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        sieveNorm M N ≤ C*(M*N)^ε*(M^ξ + N + (M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  rw [sieveNorm_reciprocity]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

lemma HasCubicExponent.doubled {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
        sieveNorm (2*X) N ≤ C*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h.swapped ε hε
  let A : ℝ := 1 + (2:ℝ)^ξ + (2:ℝ)^(2/3 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*(2:ℝ)^ε*A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2/3 : ℝ)
  have hshape : (2*X)^ξ + N + ((2*X)*N)^(2/3 : ℝ) ≤
      A*(X^ξ+N+(X*N)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hxξ]
  calc
    _ ≤ C*((2*X)*N)^ε*((2*X)^ξ+N+((2*X)*N)^(2/3 : ℝ)) := hb (2*X) N (by linarith) hN
    _ ≤ C*((2*X)*N)^ε*(A*(X^ξ+N+(X*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.B2Growth -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementSieveNorm_two_power_log (ξ ε A M N : ℝ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hB1 : ∀ X : ℝ, 1 ≤ X → sieveNorm (2*X) N ≤
      A*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ))) :
    elementSieveNorm M N ≤ (384*128^2 : ℝ) * A *
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
      (M*N)^ε * (M^(1/3 : ℝ)*N + M^ξ) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let R := elementRange M
  have hRne : R.Nonempty := by
    refine ⟨1, ?_⟩
    rw [mem_elementRange]
    refine ⟨one_ne_zero, ?_⟩
    simpa using hM
  have hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    fun z hz => (mem_elementRange M z).mp hz
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  obtain ⟨X,Y,hX,hY,hXY,he⟩ := full_element_dyadic_extraction R hRne M N hR
    (fun j : idealRange N => j.val) Subtype.val_injective
    (fun j => mem_idealRange.mp j.property) a
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hXM : X ≤ M := by nlinarith [sq_nonneg (Y-1)]
  have hYM : Y ≤ M := by nlinarith [sq_nonneg (Y-1)]
  let B := A*(M*N)^ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (U : ℝ) (hU : 1 ≤ U) (hUM : U ≤ M) :
      sieveNorm (2*U) N ≤ B*(U^ξ+N+(U*N)^(2/3 : ℝ)) := by
    apply (hB1 U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hUM hN0.le) hε) hA
  have hmin : min (Y*sieveNorm (2*X) N) (X*sieveNorm (2*Y) N) ≤
      B*min (Y*(X^ξ+N+(X*N)^(2/3 : ℝ))) (X*(Y^ξ+N+(Y*N)^(2/3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB]
    apply min_le_min
    · convert mul_le_mul_of_nonneg_left (hb X hX hXM) hY0.le using 1; ring
    · convert mul_le_mul_of_nonneg_left (hb Y hY hYM) hX0.le using 1; ring
  have hopt := extraction_min_two_power M N X Y ξ hM hN0.le hX hY hXY hξ
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hi (z : O) : (∑ j : idealRange N, a j * elementCharacter j.val (mem_idealRange.mp j.property).1.2 z) =
      ∑ j : idealRange N, cubicRow j.val z * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hi] at he
  have hE : 0 ≤ ∑ j : idealRange N, ‖a j‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M/(X*Y^2))^(1/3 : ℝ) by positivity)) hE
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*B by positivity)) hE
  have he' := he.trans hh
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val * a j‖^2) ≤ _
  apply he'.trans
  convert hbnd using 1 <;> dsimp only [B] <;> ring

theorem HasCubicExponent.full_element_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*(M*N)^ε*(M^(1/3 : ℝ)*N + M^ξ) := by
  obtain ⟨A,hA,hb⟩ := h.doubled (ε/2) (by positivity)
  let D : ℝ := 2 + 1/((ε/4)*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨(384*128^2 : ℝ)*A*D^2, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power (ε/4) (by positivity) M hM
  have hLP : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 ≤ D^2*M^(ε/2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε/4)*(2:ℕ) = ε/2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M^(ε/2) ≤ (M*N)^(ε/2) := Real.rpow_le_rpow hM0.le
    (by nlinarith) (by positivity)
  have hprod : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 * (M*N)^(ε/2) ≤
      D^2*(M*N)^ε := by
    calc
      _ ≤ (D^2*M^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right hLP (Real.rpow_nonneg (by positivity) _)
      _ ≤ (D^2*(M*N)^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]
        congr 2
        ring
  have he := elementSieveNorm_two_power_log ξ (ε/2) A M N hξ (by positivity) hA.le hM hN
    (fun X hX => hb X N hX hN)
  calc
    _ ≤ (384*128^2 : ℝ)*A*
        (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
        (M*N)^(ε/2)*(M^(1/3 : ℝ)*N+M^ξ) := he
    _ = ((384*128^2 : ℝ)*A)*
        ((CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M*N)^(ε/2))*
        (M^(1/3 : ℝ)*N+M^ξ) := by ring
    _ ≤ ((384*128^2 : ℝ)*A)*(D^2*(M*N)^ε)*(M^(1/3 : ℝ)*N+M^ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.Mobius -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementQuotient (d z : O) : O := if h : d ∣ z then h.choose else 0

lemma elementQuotient_mul (d z : O) (h : d ∣ z) : d * elementQuotient d z = z := by
  rw [elementQuotient, dite_eq_left h]
  exact h.choose_spec.symm

lemma elementQuotient_injective (d : O) : Set.InjOn (elementQuotient d) {z | d ∣ z} := by
  intro x hx y hy he
  rw [← elementQuotient_mul d x hx, ← elementQuotient_mul d y hy, he]

def dividedRows (R : Finset O) (d : O) : Finset O :=
  (R.filter (fun z => d ∣ z)).image (elementQuotient d)

lemma sum_divisible_rows (R : Finset O) (d : O) (f : O → ℂ) :
    (∑ z ∈ R, if d ∣ z then f z else 0) =
      ∑ w ∈ dividedRows R d, f (d * w) := by
  rw [← Finset.sum_filter]
  unfold dividedRows
  have hinj : Set.InjOn (elementQuotient d) (↑(R.filter (fun z => d ∣ z)) : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective d (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro z hz
  rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]

lemma dividedRows_ne_zero (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0) (d : O)
    (w : O) (hw : w ∈ dividedRows R d) : w ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  intro he
  have h := elementQuotient_mul d z (Finset.mem_filter.mp hz).2
  rw [he, mul_zero] at h
  exact hR z (Finset.mem_filter.mp hz).1 h.symm

lemma dividedRows_norm_le (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (d : O) (hd : d ≠ 0) (w : O) (hw : w ∈ dividedRows R d) :
    (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ M / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  have hdN : 0 < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hd))
  apply (le_div_iff₀ hdN).mpr
  calc
    _ = (Ideal.absNorm (Ideal.span {d * elementQuotient d z}) : ℝ) := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm (Ideal.span {z}) : ℝ) := by
      rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]
    _ ≤ M := hR z (Finset.mem_filter.mp hz).1

lemma cubicRow_mul_argument (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    cubicRow I (x * y) = cubicRow I x * cubicRow I y := by
  exact (elementCharacter I hI).map_mul x y

lemma totalQuotient_cubic_admissible (D I : Ideal O) (hI : Admissible I) :
    Admissible (totalQuotient D I) := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    exact cubic_admissible_quotient hI h
  · rw [totalQuotient, ite_eq_right h]
    exact ⟨squarefree_one, by rw [primaryGenerator_one]; exact one_ne_zero⟩

def descendedCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) : ℂ :=
  cubicRow (totalQuotient D (cols j)) d * (if D ∣ cols j then a j else 0)

def residualGram {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
    star (cubicRow (totalQuotient D (cols j)) z * a j) *
      (cubicRow (totalQuotient D (cols k)) z * a k) else 0

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols j)).2,
      cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols k)).2]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl

lemma ideal_dvd_span_iff_generator (E : Ideal O) (z : O) :
    E ∣ Ideal.span {z} ↔ idealGenerator E ∣ z := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have he : (z ∈ Ideal.span {idealGenerator E}) ↔ idealGenerator E ∣ z :=
    Ideal.mem_span_singleton
  rwa [span_idealGenerator] at he

lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols hcols a]

theorem cubic_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (idealGenerator E),
            w (idealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (idealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      (star (cubicRow D z) * cubicRow D z) * residualGram D cols b z := by
    simp only [cubicGcdTerm_eq_quotient D (primaryGenerator_ne_zero_ideal D hD),
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if idealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, cubicRow_common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if idealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols hcols a R w (idealGenerator E))

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.DescentEnergy -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum DivisorBlockCauchy
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma descendedCoefficient_norm_le {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖ ≤ ‖if D ∣ cols j then a j else 0‖ := by
  unfold descendedCoefficient
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (elementCharacter_norm_le_one _ (totalQuotient_cubic_admissible D _ (hc j)).2 d)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem descended_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
      ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
        (divisorConstant ε hε * N^ε)^2 * ∑ j, ‖a j‖^2 := by
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  let B := divisorConstant ε hε * N^ε
  have hB : 0 ≤ B := mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hcard (D : Ideal O) (hD : D ∈ columnDivisorPool cols) :
      ((idealDivisors D).card : ℝ) ≤ B := by
    have hd := columnDivisorPool_norm_bounds cols hc0 N hN D hD
    have hd0 : D ≠ 0 := by
      intro he
      have hh := hd.1
      norm_num [he] at hh
    exact ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 D hd0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hd.2 hε.le)
        (divisorConstant_pos ε hε).le)
  calc
    _ ≤ ∑ D ∈ columnDivisorPool cols, B * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ ∑ E ∈ idealDivisors D, ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          apply Finset.sum_le_sum
          intro E hE
          exact Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            (descendedCoefficient_norm_le D cols hc a (idealGenerator E) j) 2)
        _ = ((idealDivisors D).card : ℝ) * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD) (by positivity)
    _ = B * (∑ D ∈ columnDivisorPool cols, ∑ j, ‖if D ∣ cols j then a j else 0‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ B * (B * ∑ j, ‖a j‖^2) := mul_le_mul_of_nonneg_left
      (divisor_mask_energy_small_power ε hε _ cols hc0 N hN a) hB
    _ = _ := by dsimp [B]; ring

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.PairPrimes -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrime (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → Ideal O :=
  Sum.elim Subtype.val Subtype.val

instance pairPrime_maximal (I J : Ideal O) (P : PrimeIndex I ⊕ PrimeIndex J) :
    (pairPrime I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

lemma pairPrime_good (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : goodLambda ∉ pairPrime I J P := by
  cases P with
  | inl P => exact primeIndex_good I hI.2 P
  | inr P => exact primeIndex_good J hJ.2 P

lemma pairPrime_coprime (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (pairPrime I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
      (primeIndex_le J (primaryGenerator_ne_zero_ideal J hJ.2) Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

lemma pairPrime_product (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    (∏ P, pairPrime I J P) = I * J := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (primeIndex_product I hI) (primeIndex_product J hJ)

def pairExponent (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (fun _ => 4) (fun _ => 2)

lemma pairExponent_nonprincipal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) :
    actualSextic (pairPrime I J P) (pairPrime_good I J hI hJ P) ^ pairExponent I J P ≠ 1 := by
  cases P with
  | inl P => exact cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) true
  | inr P => exact cubicExponent_nonprincipal P.val (primeIndex_good J hJ.2 P) false

lemma primeIndex_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z =
      cubicRow I z := by
  exact (CompletedGauss.cubicRow_mk I hI.2 z).symm.trans
    (CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z)

lemma primeIndex_conjugate_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      star (cubicRow I z) := by
  have he : finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      (finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z) ^ 2 := by
    simp only [finiteSexticRow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro P hP
    rw [MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0),
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ← pow_mul]
  rw [he, primeIndex_cubic_row I hI, cubicRow_square_eq_star]

lemma pairPrime_row (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (z : O) :
    finiteSexticRow (pairPrime I J) (pairPrime_good I J hI hJ) (pairExponent I J) z =
      star (cubicRow I z) * cubicRow J z := by
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (primeIndex_good J hJ.2) (fun _ => 2) z = _
  rw [primeIndex_conjugate_cubic_row I hI, primeIndex_cubic_row J hJ]

lemma pairPrime_modulus (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    Ideal.span {primaryGenerator I * primaryGenerator J} = ∏ P, pairPrime I J P := by
  rw [pairPrime_product I J hI hJ, ← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.PairPoisson -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrincipalRow (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : O ⧸ Ideal.span {primaryGenerator I * primaryGenerator J} → ℂ :=
  principalSexticRow (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) (primaryGenerator I * primaryGenerator J)
    (pairPrime_modulus I J hI hJ)

lemma pairPrincipalRow_mk (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (z : O) :
    pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) =
      star (cubicRow I z) * cubicRow J z := by
  unfold pairPrincipalRow
  rw [principalSexticRow_mk (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) _ (pairPrime_modulus I J hI hJ) z,
    pairPrime_row I J hI hJ]

lemma pairPrincipalGauss_eq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = cubicPairGauss I J hI hJ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ Ideal.span {a * b}) := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (O ⧸ Ideal.span {a * b}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span hI.2
  let e : (O ⧸ Ideal.span {a * b}) ≃+* (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) = (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul, Complex.ofReal_mul]
  dsimp only [principalNormalizedGauss, cubicPairGauss]
  rw [hnorm]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  change pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) * _ = _
  rw [pairPrincipalRow_mk]
  simp only [e, a, b, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]
  rw [← MulChar.star_apply', principalCubicCharacter_mk I hI, principalCubicCharacter_mk J hJ]
  congr 1

lemma pairPrincipalGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  rw [pairPrincipalGauss_eq I J hI hJ hcop, cubicPairGauss_separation I J hI hJ hcop]

theorem cubic_pair_poisson (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, (star (cubicRow I z) * cubicRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        (‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ : ℂ)) *
      ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2) := by
  let c := primaryGenerator I * primaryGenerator J
  have hc0 : c ≠ 0 := mul_ne_zero hI.2 hJ.2
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (pairPrime_modulus I J hI hJ)
  let : Fintype (O ⧸ ∏ P, pairPrime I J P) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (P : PrimeIndex I ⊕ PrimeIndex J) : Fintype (O ⧸ pairPrime I J P) := Fintype.ofFinite _
  let row := pairPrincipalRow I J hI hJ hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  let G := ∑ r : O ⧸ Ideal.span {c}, row r * ψ r
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        (cubicRow I h * star (cubicRow J h)) * G := by
    have hh := canonical_principal_gauss_transform_of_nontrivial (pairPrime I J)
      (pairPrime_coprime I J hI hJ hcop) (pairPrime_good I J hI hJ) (pairExponent I J)
      (pairExponent_nonprincipal I J hI hJ) c (pairPrime_modulus I J hI hJ) ψ
      (Ideal.Quotient.mk (Ideal.span {c}) h)
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (row (Ideal.Quotient.mk (Ideal.span {c}) h)) * G at hh
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ h)) * G at hh
    rw [pairPrincipalRow_mk I J hI hJ hcop h, star_mul, star_star,
      mul_comm (star (cubicRow J h)) (cubicRow I h)] at hh
    exact hh
  have hp := actual_radial_paper_poisson_trace W M hM c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      (M / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  have hsum : (∑' h : O, ((cubicRow I h * star (cubicRow J h)) * G) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hsum] at hp
  have hrow (z : O) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      star (cubicRow I z) * cubicRow J z :=
    pairPrincipalRow_mk I J hI hJ hcop z
  simp_rw [hrow] at hp
  rw [hp]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc0))
  have hGauss := pairPrincipalGauss_separation I J hI hJ hcop
  change G / (‖eisEmbedding c‖ : ℂ) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * _) = _
  rw [← mul_assoc]
  congr 1
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * G =
    (M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (‖eisEmbedding c‖ : ℂ)
  rw [hG]
  push_cast
  field_simp [hn]

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.KernelTransfer -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_radial_kernel_transfer (W : 𝓢(ℝ, ℂ)) (Lr Lc : ℝ)
    (hLr : 0 ≤ Lr) (hLc : 0 ≤ Lc) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hN : 0 ≤ N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
        (_hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E)
        (x : m → ℝ) (y : n → ℝ) (_hx : ∀ i, |x i| ≤ Lr) (_hy : ∀ j, |y j| ≤ Lc),
        (1 + R) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (R * Real.exp (x i + (y j + y k)))‖) ≤
          C * (elementSieveNorm M N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, htransfer⟩ := QuadraticKernelTransfer.radial_matrix_kernel_transfer
    W Lr (2 * Lc) hLr (by positivity) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ _ _ ε hε M N hN rows cols hr hc hrows hcols a b E hE ha hb x y hx hy
  let c : m → n × n → ℂ := fun i p => if IsCoprime (cols p.1) (cols p.2) then
    star (cubicRow (cols p.1) (rows i) * a p.1) *
      (cubicRow (cols p.2) (rows i) * b p.2) else 0
  let H := elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E
  have hfac : 0 ≤ elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) :=
    mul_nonneg (elementSieveNorm_nonneg _ _)
      (mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _))
  have hH : 0 ≤ H := mul_nonneg hfac hE
  have hyy (p : n × n) : |y p.1 + y p.2| ≤ 2 * Lc :=
    (abs_add_le _ _).trans (by linarith [hy p.1, hy p.2])
  have hphase (t : ℝ) : (∑ i, ‖∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)‖) ≤ H := by
    let aTwist : n → ℂ := fun j => a j * star (logPhase t (y j))
    let bTwist : n → ℂ := fun j => b j * logPhase t (y j)
    have ha' : (∑ j, ‖aTwist j‖ ^ 2) ≤ E := by simpa only [aTwist, norm_mul, norm_star, logPhase_norm, mul_one] using ha
    have hb' : (∑ j, ‖bTwist j‖ ^ 2) ≤ E := by simpa only [bTwist, norm_mul, logPhase_norm, mul_one] using hb
    have he (i : m) : (∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)) =
        ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
          star (cubicRow (cols j) (rows i) * aTwist j) *
            (cubicRow (cols k) (rows i) * bTwist k) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c, aTwist, bTwist]
      split_ifs
      · rw [logPhase_add]
        simp only [star_mul, star_star]
        ring
      · simp only [zero_mul]
    simp_rw [he]
    have hbil := element_coprime_bilinear_bound ε hε M N hN rows cols hr hc hrows hcols aTwist bTwist
    apply (sq_le_sq₀ (by positivity) hH).mp
    apply hbil.trans
    calc
      _ ≤ (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) *
          (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hfac) (mul_le_mul_of_nonneg_left hb' hfac)
          (by positivity) hH
      _ = H ^ 2 := by ring
  have ht := htransfer R hR c x (fun p : n × n => y p.1 + y p.2) H hH hx hyy hphase
  simpa only [Fintype.sum_prod_type, c, H] using ht

end
end SevenEighths.CubicSieve

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FrequencyShell -/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma log_shell_ratio (K q : ℝ) (hK : 0 < K) (hq : K / 2 ≤ q ∧ q ≤ K) :
    |Real.log (q / K)| ≤ 4 := by
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hK).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hK).mpr
    linarith [hq.2]

lemma log_inverse_shell_ratio (N q : ℝ) (hN : 0 < N) (hq : N / 2 ≤ q ∧ q ≤ N) :
    |Real.log (N / q)| ≤ 4 := by
  have hq0 : 0 < q := by linarith [hq.1]
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hq0).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hq0).mpr
    linarith [hq.1]

lemma radial_product_log_identity (M K N q u v : ℝ)
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (M * K / N ^ 2) * Real.exp (Real.log (q / K) + (Real.log (N / u) + Real.log (N / v))) =
      M * q / (u * v) := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hq hK),
    Real.exp_log (div_pos hN hu), Real.exp_log (div_pos hN hv)]
  field_simp

theorem cubic_frequency_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {rows i}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, ht⟩ := cubic_radial_kernel_transfer W 4 4 (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a b E hE ha hb
  have hq (i : m) : 0 < (Ideal.absNorm (Ideal.span {rows i}) : ℝ) := by linarith [(hrows i).1]
  have hn (j : n) : 0 < (Ideal.absNorm (cols j) : ℝ) := by linarith [(hcols j).2.1]
  have hr0 (i : m) : rows i ≠ 0 := by
    intro hz
    simpa [hz] using hq i
  have hp := ht (M * K / N ^ 2) (by positivity) ε hε K N hN.le rows cols hr hc
    (fun i => ⟨hr0 i, (hrows i).2⟩) (fun j => ⟨(hcols j).1, (hcols j).2.2⟩)
    a b E hE ha hb
    (fun i => Real.log ((Ideal.absNorm (Ideal.span {rows i}) : ℝ) / K))
    (fun j => Real.log (N / (Ideal.absNorm (cols j) : ℝ)))
    (fun i => log_shell_ratio K _ hK (hrows i))
    (fun j => log_inverse_shell_ratio N _ hN (hcols j).2)
  simp_rw [radial_product_log_identity M K N _ _ _ hK hN (hq _) (hn _) (hn _)] at hp
  exact hp

end
end SevenEighths.CubicSieve

end OAI

end

