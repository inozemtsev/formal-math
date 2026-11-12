module

public import Green64.Library.Correlation.Part002
public import Mathlib
public import Green64.Library.Correlation.Part001
public import Green64.Library.Analysis.Estimates.SourceLowFrequencyFourFactorIntegral
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Analysis.Estimates.Part001

@[expose] public section

/-!
# Weights / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceActualAlphaDyadicCut -/

section

namespace Green64Analytic.CorrelationMellin

/-! Original universal source discrepancy is stable under exact
intersection with a source m-dyad. This is essential for keeping
the original alpha while grouping all rational characters and gcd
classes; it introduces no new discrepancy hypothesis. -/

noncomputable def sourceAlphaDyadicCut
    (alpha : ℕ → ℂ) (lo hi m : ℕ) : ℂ :=
  if m ∈ Finset.Icc lo hi then alpha m else 0

theorem source_alpha_dyadic_cut_sum_exact
    (alpha : ℕ → ℂ) (lo hi a b : ℕ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (freq : ℝ) :
    (∑ m ∈ Finset.Icc a b, sourceAlphaDyadicCut alpha lo hi m *
       chi m * (m:ℂ)⁻¹ * sourcePhase m freq) =
    ∑ m ∈ Finset.Icc (max a lo) (min b hi),
       alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m freq := by
  classical
  have hTerm (m : ℕ) :
      sourceAlphaDyadicCut alpha lo hi m *
          chi m * (m:ℂ)⁻¹ * sourcePhase m freq =
      if m ∈ Finset.Icc lo hi then
        alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m freq else 0 := by
    by_cases hm : m ∈ Finset.Icc lo hi
    · simp [sourceAlphaDyadicCut, hm]
    · simp [sourceAlphaDyadicCut, hm]
  have hFilter :
      (Finset.Icc a b).filter (fun m => m ∈ Finset.Icc lo hi) =
        Finset.Icc (max a lo) (min b hi) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  simp_rw [hTerm]
  rw [←Finset.sum_filter, hFilter]

theorem source_alpha_dyadic_cut_preserves_discrepancy
    (L B x : ℝ) (alpha : ℕ → ℂ) (lo hi : ℕ)
    (hDisc : SourceAlphaDiscrepancy L B x alpha) :
    SourceAlphaDiscrepancy L B x
      (sourceAlphaDyadicCut alpha lo hi) := by
  intro q chi a b freq hq ha hb hf
  rw [source_alpha_dyadic_cut_sum_exact]
  exact hDisc q chi (max a lo) (min b hi) freq
    hq (ha.trans (le_max_left _ _)) (by
      have hm : (min b hi) ≤ b := min_le_left _ _
      exact (Nat.cast_le.mpr hm).trans hb) hf

theorem source_alpha_dyadic_cut_support
    (alpha : ℕ → ℂ) (lo hi m : ℕ)
    (hm : m ∉ Finset.Icc lo hi) :
    sourceAlphaDyadicCut alpha lo hi m = 0 := by
  simp [sourceAlphaDyadicCut, hm]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadWindowSplit -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Exact finite fourfold source box, prior to Fourier separation
of the smooth logarithmic cutoff. Coordinates are (m,p_s,p_l,r).
No independence, squarefree restriction, or distinctness is used. -/
def sourceActualFourDyadTuples
    (small long R : Finset ℕ) (a b : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.Icc a b).product small).product (long.product R)

def sourceActualFourDyadProduct
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  z.1.1*z.1.2*z.2.1*z.2.2

noncomputable def sourceActualFourDyadLiteralTerm
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  (alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹ *
      sourcePhase z.1.1 (sigma0+t)) *
  (bs z.1.2 * (z.1.2:ℂ)⁻¹ * sourcePhase z.1.2 t) *
  (bp z.2.1 * (z.2.1:ℂ)⁻¹ *
      sourcePhase z.2.1 (sigma1+t)) *
  (d z.2.2 * (z.2.2:ℂ)⁻¹ * sourcePhase z.2.2 t)
noncomputable def sourceActualSmoothFourDyadAt
    (small long R : Finset ℕ) (a b : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ) : ℂ :=
  ∑ z ∈ sourceActualFourDyadTuples small long R a b,
    cutoff (sourceActualFourDyadProduct z) *
      sourceActualFourDyadLiteralTerm alpha bs bp d chi sigma0 sigma1 t z

/-! If the original source smooth cutoff kills all fourfold tuples
then the whole physical box vanishes. Otherwise one true
nonzero-cutoff tuple provides BOTH dyadic comparisons. This is a
disjunction, not a new witness/estimate hypothesis. -/
theorem source_actual_smooth_fourdyad_zero_or_comparable
    (small long R : Finset ℕ) (a b M0 P P0 R0 : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 Y A : ℝ)
    (hY : 0 ≤ Y) (hA : 1 ≤ A)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hCutoff : ∀ w : ℕ, cutoff w ≠ 0 →
      Y ≤ A*(w:ℝ) ∧ (w:ℝ) ≤ A*Y) :
    (∀ t : ℝ,
      sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t = 0) ∨
    (Y ≤ (16*A)*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) ∧
     ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) ≤ (16*A)*Y) := by
  classical
  let tuples := sourceActualFourDyadTuples small long R a b
  let live := tuples.filter
    (fun z => cutoff (sourceActualFourDyadProduct z) ≠ 0)
  by_cases hEmpty : live = ∅
  · left
    intro t
    unfold sourceActualSmoothFourDyadAt
    apply Finset.sum_eq_zero
    intro z hz
    have hZero : cutoff (sourceActualFourDyadProduct z) = 0 := by
      by_contra hNonzero
      have hLive : z ∈ live := by
        apply Finset.mem_filter.mpr
        exact ⟨by simpa only [tuples] using hz, hNonzero⟩
      simpa [hEmpty] using hLive
    simp only [hZero, zero_mul]
  · right
    obtain ⟨z, hz⟩ : live.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨hzTuple,hzCut⟩ := Finset.mem_filter.mp hz
    have hzBase : z ∈
        ((Finset.Icc a b).product small).product (long.product R) := by
      simpa only [tuples, sourceActualFourDyadTuples] using hzTuple
    obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hzBase
    obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
    obtain ⟨hp,hr⟩ := Finset.mem_product.mp hzPR
    have hWindow := hCutoff (sourceActualFourDyadProduct z) hzCut
    exact source_actual_four_dyadic_box_comparison Y A M0 P P0 R0
      z.1.1 z.1.2 z.2.1 z.2.2 hY hA
      (hM hm) (hSmall hps) (hLong hp) (hR hr)
      (by simpa only [sourceActualFourDyadProduct] using hWindow.1)
      (by simpa only [sourceActualFourDyadProduct] using hWindow.2)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadUncutExact -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-- Exact finite pair factorization. -/
theorem source_actual_pair_finite_product_exact
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → ℂ) (g : β → ℂ) :
    (∑ z ∈ A.product B, f z.1 * g z.2) =
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  have hProd : (∑ z ∈ A.product B, f z.1 * g z.2) =
      ∑ a ∈ A, ∑ b ∈ B, f a * g b :=
    Finset.sum_product' A B (fun a b => f a * g b)
  rw [hProd]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Exact fourfold finite distributivity with literal ordered
(m,short,long,residual) tuples, without any new coefficient. -/
theorem source_actual_fourfold_finite_product_exact
    (M S P R : Finset ℕ) (f g h k : ℕ → ℂ) :
    (∑ z ∈ (M.product S).product (P.product R),
      f z.1.1 * g z.1.2 * h z.2.1 * k z.2.2) =
    ((∑ m ∈ M, f m) * (∑ s ∈ S, g s)) *
      ((∑ p ∈ P, h p) * (∑ r ∈ R, k r)) := by
  let F : ℕ × ℕ → ℂ := fun mp => f mp.1 * g mp.2
  let G : ℕ × ℕ → ℂ := fun pr => h pr.1 * k pr.2
  have hOuter := source_actual_pair_finite_product_exact
    (M.product S) (P.product R) F G
  have hLeft := source_actual_pair_finite_product_exact M S f g
  have hRight := source_actual_pair_finite_product_exact P R h k
  calc
    _ = (∑ mp ∈ M.product S, F mp) *
        (∑ pr ∈ P.product R, G pr) := by
      simpa only [F, G, mul_assoc] using hOuter
    _ = ((∑ m ∈ M, f m) * (∑ s ∈ S, g s)) *
          ((∑ p ∈ P, h p) * (∑ r ∈ R, k r)) := by
      rw [hLeft, hRight]

/-- The same literal source four-factor polynomial is recovered
from the actual fourfold tuples when the smooth size cutoff is 1.
This is the normalization required for Fourier separation. -/
theorem source_actual_uncut_fourdyad_exact_fourfactor
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ) :
    sourceActualSmoothFourDyadAt small long R a b
      (fun _ => 1) alpha bs bp d chi sigma0 sigma1 t =
    sourceFourFactorAt small long R a b alpha bs bp d chi
      sigma0 sigma1 t := by
  classical
  let fm : ℕ → ℂ := fun m =>
    alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t)
  let fs : ℕ → ℂ := fun p =>
    bs p * (p:ℂ)⁻¹ * sourcePhase p t
  let fp : ℕ → ℂ := fun p =>
    bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)
  let fr : ℕ → ℂ := fun r =>
    d r * (r:ℂ)⁻¹ * sourcePhase r t
  have hProd := source_actual_fourfold_finite_product_exact
    (Finset.Icc a b) small long R fm fs fp fr
  unfold sourceActualSmoothFourDyadAt
    sourceActualFourDyadTuples sourceFourFactorAt
    sourceActualFourDyadLiteralTerm
  simp only [one_mul]
  convert hProd using 1
  · dsimp [fm,fs,fp,fr] <;> ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFiniteFourierSeparation -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Exact finite-frequency Fourier separation for the original
four-source-factor polynomial. No truncation or smoothing tail is
claimed: the source Fourier measure must later be approximated by
finite frequencies with a proved small tail. -/
theorem source_actual_fourdyad_term_frequency_shift
    (m ps p r : ℕ)
    (hm : 0 < m) (hps : 0 < ps)
    (hp : 0 < p) (hr : 0 < r)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t nu : ℝ) :
    sourcePhase (m*ps*p*r) nu *
      (((alpha m * chi m * (m:ℂ)⁻¹ *
            sourcePhase m (sigma0+t)) *
        (bs ps * (ps:ℂ)⁻¹ * sourcePhase ps t)) *
       (bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)) *
       (d r * (r:ℂ)⁻¹ * sourcePhase r t)) =
      (((alpha m * chi m * (m:ℂ)⁻¹ *
            sourcePhase m (sigma0+(t+nu))) *
        (bs ps * (ps:ℂ)⁻¹ * sourcePhase ps (t+nu))) *
       (bp p * (p:ℂ)⁻¹ *
         sourcePhase p (sigma1+(t+nu))) *
       (d r * (r:ℂ)⁻¹ * sourcePhase r (t+nu))) := by
  have hW : sourcePhase (m*ps*p*r) nu =
      sourcePhase m nu * sourcePhase ps nu *
        sourcePhase p nu * sourcePhase r nu := by
    rw [sourcePhase_mul (m*ps*p) r
        (by positivity : 0 < m*ps*p) hr,
      sourcePhase_mul (m*ps) p
        (by positivity : 0 < m*ps) hp,
      sourcePhase_mul m ps hm hps]
  have hmAdd : sourcePhase m (sigma0+(t+nu)) =
      sourcePhase m (sigma0+t)*sourcePhase m nu := by
    rw [show sigma0+(t+nu) = (sigma0+t)+nu by ring,
      sourcePhase_add]
  have hpAdd : sourcePhase p (sigma1+(t+nu)) =
      sourcePhase p (sigma1+t)*sourcePhase p nu := by
    rw [show sigma1+(t+nu) = (sigma1+t)+nu by ring,
      sourcePhase_add]
  rw [hW, hmAdd, hpAdd, sourcePhase_add ps t nu,
    sourcePhase_add r t nu]
  ring

/-- An actual source fourfold sum with one logarithmic Fourier
monomial equals the SAME original sourceFourFactorAt at shifted t. -/
theorem source_actual_fourdyad_single_frequency_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t nu : ℝ)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    sourceActualSmoothFourDyadAt small long R a b
        (fun w => sourcePhase w nu)
        alpha bs bp d chi sigma0 sigma1 t =
    sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 (t+nu) := by
  calc
    _ = sourceActualSmoothFourDyadAt small long R a b
        (fun _ => 1) alpha bs bp d chi sigma0 sigma1 (t+nu) := by
      unfold sourceActualSmoothFourDyadAt
      apply Finset.sum_congr rfl
      intro z hz
      have hzBase : z ∈
          ((Finset.Icc a b).product small).product
            (long.product R) := by
        simpa only [sourceActualFourDyadTuples] using hz
      obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hzBase
      obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
      obtain ⟨hpl,hrl⟩ := Finset.mem_product.mp hzPR
      have hmPos : 0 < z.1.1 :=
        lt_of_lt_of_le (by omega : 0 < a)
          (Finset.mem_Icc.mp hm).1
      have hpsPos := hs z.1.2 hps
      have hpPos := hp z.2.1 hpl
      have hrPos := hr z.2.2 hrl
      simp only [one_mul]
      dsimp [sourceActualFourDyadProduct,
        sourceActualFourDyadLiteralTerm]
      exact source_actual_fourdyad_term_frequency_shift
        z.1.1 z.1.2 z.2.1 z.2.2
        hmPos hpsPos hpPos hrPos
        alpha bs bp d chi sigma0 sigma1 t nu
    _ = _ := source_actual_uncut_fourdyad_exact_fourfactor
      small long R a b alpha bs bp d chi sigma0 sigma1 (t+nu)
/-- Every finite Fourier separation of the exact normalized
source cutoff has the same sourceFourFactorAt, with only
frequency shifts. Does not yet control the infinite Fourier tail. -/
theorem source_actual_fourdyad_finite_fourier_separation
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (freqs : Finset ℝ) (weights : ℝ → ℂ)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    sourceActualSmoothFourDyadAt small long R a b
      (fun w => ∑ nu ∈ freqs, weights nu * sourcePhase w nu)
      alpha bs bp d chi sigma0 sigma1 t =
    ∑ nu ∈ freqs, weights nu *
      sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 (t+nu) := by
  classical
  unfold sourceActualSmoothFourDyadAt
  calc
    (∑ z ∈ sourceActualFourDyadTuples small long R a b,
      (∑ nu ∈ freqs,
        weights nu * sourcePhase (sourceActualFourDyadProduct z) nu) *
        sourceActualFourDyadLiteralTerm alpha bs bp d chi
          sigma0 sigma1 t z) =
      ∑ z ∈ sourceActualFourDyadTuples small long R a b,
        ∑ nu ∈ freqs,
          weights nu *
            (sourcePhase (sourceActualFourDyadProduct z) nu *
              sourceActualFourDyadLiteralTerm alpha bs bp d chi
                sigma0 sigma1 t z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro nu hnu
      ring
    _ = ∑ nu ∈ freqs,
        ∑ z ∈ sourceActualFourDyadTuples small long R a b,
          weights nu *
            (sourcePhase (sourceActualFourDyadProduct z) nu *
              sourceActualFourDyadLiteralTerm alpha bs bp d chi
                sigma0 sigma1 t z) := by
      exact Finset.sum_comm
    _ = ∑ nu ∈ freqs,
        weights nu *
          (∑ z ∈ sourceActualFourDyadTuples small long R a b,
            sourcePhase (sourceActualFourDyadProduct z) nu *
              sourceActualFourDyadLiteralTerm alpha bs bp d chi
                sigma0 sigma1 t z) := by
      apply Finset.sum_congr rfl
      intro nu hnu
      rw [Finset.mul_sum]
    _ = ∑ nu ∈ freqs, weights nu *
      sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 (t+nu) := by
      apply Finset.sum_congr rfl
      intro nu hnu
      congr 1
      simpa only [sourceActualSmoothFourDyadAt] using
        source_actual_fourdyad_single_frequency_exact
          small long R a b alpha bs bp d chi
          sigma0 sigma1 t nu ha hs hp hr
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadAbsoluteL1 -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! True absolute ℓ¹ budget of the original four-dyad tuples,
using the previously kernel-checked dyadic reciprocal bounds. -/
theorem source_actual_pair_real_sum_product
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → ℝ) (g : β → ℝ) :
    (∑ z ∈ A.product B, f z.1 * g z.2) =
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  have hProd : (∑ z ∈ A.product B, f z.1 * g z.2) =
      ∑ a ∈ A, ∑ b ∈ B, f a * g b :=
    Finset.sum_product' A B (fun a b => f a * g b)
  rw [hProd]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem source_actual_fourfold_real_sum_product
    (M S P R : Finset ℕ) (f g h k : ℕ → ℝ) :
    (∑ z ∈ (M.product S).product (P.product R),
      f z.1.1 * g z.1.2 * h z.2.1 * k z.2.2) =
    ((∑ m ∈ M, f m) * (∑ s ∈ S, g s)) *
      ((∑ p ∈ P, h p) * (∑ r ∈ R, k r)) := by
  let F : ℕ × ℕ → ℝ := fun mp => f mp.1 * g mp.2
  let G : ℕ × ℕ → ℝ := fun pr => h pr.1 * k pr.2
  have hOuter := source_actual_pair_real_sum_product
    (M.product S) (P.product R) F G
  have hLeft := source_actual_pair_real_sum_product M S f g
  have hRight := source_actual_pair_real_sum_product P R h k
  calc
    _ = (∑ mp ∈ M.product S, F mp) *
        (∑ pr ∈ P.product R, G pr) := by
      simpa only [F, G, mul_assoc] using hOuter
    _ = ((∑ m ∈ M, f m) * (∑ s ∈ S, g s)) *
          ((∑ p ∈ P, h p) * (∑ r ∈ R, k r)) := by
      rw [hLeft, hRight]
theorem source_actual_fourdyad_term_norm_product
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    ‖sourceActualFourDyadLiteralTerm alpha bs bp d
        chi sigma0 sigma1 t z‖ =
      (‖alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹‖ *
       ‖bs z.1.2 * (z.1.2:ℂ)⁻¹‖) *
      (‖bp z.2.1 * (z.2.1:ℂ)⁻¹‖ *
       ‖d z.2.2 * (z.2.2:ℂ)⁻¹‖) := by
  simp [sourceActualFourDyadLiteralTerm, norm_mul, sourcePhase_norm]
  ring

/-- The exact sum of norms factorizes, with no assumed
collapsed convolution majorant and no character simplification. -/
theorem source_actual_fourdyad_absolute_sum_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ) :
    (∑ z ∈ sourceActualFourDyadTuples small long R a b,
      ‖sourceActualFourDyadLiteralTerm alpha bs bp d
        chi sigma0 sigma1 t z‖) =
      ((∑ m ∈ Finset.Icc a b,
          ‖alpha m * chi m * (m:ℂ)⁻¹‖) *
       (∑ ps ∈ small, ‖bs ps * (ps:ℂ)⁻¹‖)) *
      ((∑ p ∈ long, ‖bp p * (p:ℂ)⁻¹‖) *
       (∑ r ∈ R, ‖d r * (r:ℂ)⁻¹‖)) := by
  classical
  have hExact := source_actual_fourfold_real_sum_product
    (Finset.Icc a b) small long R
    (fun m => ‖alpha m * chi m * (m:ℂ)⁻¹‖)
    (fun ps => ‖bs ps * (ps:ℂ)⁻¹‖)
    (fun p => ‖bp p * (p:ℂ)⁻¹‖)
    (fun r => ‖d r * (r:ℂ)⁻¹‖)
  rw [sourceActualFourDyadTuples]
  calc
    _ = ∑ z ∈ ((Finset.Icc a b).product small).product (long.product R),
      (‖alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹‖ *
       ‖bs z.1.2 * (z.1.2:ℂ)⁻¹‖) *
      (‖bp z.2.1 * (z.2.1:ℂ)⁻¹‖ *
       ‖d z.2.2 * (z.2.2:ℂ)⁻¹‖) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact source_actual_fourdyad_term_norm_product
          alpha bs bp d chi sigma0 sigma1 t z
    _ = _ := by
      convert hExact using 1
      · apply Finset.sum_congr rfl
        intro z hz
        ring
theorem source_actual_fourdyad_absolute_l1_budget
    (small long R : Finset ℕ) (a b M0 P P0 R0 : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t Am Cs Ap Ar : ℝ)
    (hM0 : 1 ≤ M0) (hP : 1 ≤ P)
    (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (hAm : 0 ≤ Am) (hCs : 0 ≤ Cs)
    (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBs : ∀ ps ∈ small, ‖bs ps‖ ≤ Cs)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ Ar) :
    (∑ z ∈ sourceActualFourDyadTuples small long R a b,
      ‖sourceActualFourDyadLiteralTerm alpha bs bp d chi
        sigma0 sigma1 t z‖) ≤ 16*Am*Cs*Ap*Ar := by
  have hMcoeff : ∀ m ∈ Finset.Icc a b,
      ‖alpha m * chi m‖ ≤ Am := by
    intro m hm
    have hc : ‖chi m‖ ≤ 1 :=
      DirichletCharacter.norm_le_one chi (m : ZMod q)
    calc
      ‖alpha m * chi m‖ = ‖alpha m‖ * ‖chi m‖ := norm_mul _ _
      _ ≤ ‖alpha m‖ * 1 :=
        mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ ≤ Am := by simpa using hAlpha m hm
  have hmL1 := source_dyadic_reciprocal_l1
    (Finset.Icc a b) M0 Am
    (fun m => alpha m * chi m)
    hM0 hAm hM hMcoeff
  have hsL1 := source_dyadic_reciprocal_l1
    small P Cs bs hP hCs hSmall hBs
  have hpL1 := source_dyadic_reciprocal_l1
    long P0 Ap bp hP0 hAp hLong hBp
  have hrL1 := source_dyadic_reciprocal_l1
    R R0 Ar d hR0 hAr hR hd
  rw [source_actual_fourdyad_absolute_sum_exact]
  calc
    _ ≤ (2*Am)*(2*Cs)*((2*Ap)*(2*Ar)) := by
      gcongr
    _ = 16*Am*Cs*Ap*Ar := by ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadFourierTail -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Quantitative tail transfer for the ORIGINAL four-dyad product:
a uniform Fourier approximation of the actual cutoff costs only
the kernel-checked absolute source reciprocal ℓ¹ budget. -/
theorem source_actual_fourdyad_uniform_cutoff_error
    (small long R : Finset ℕ)
    (a b M0 P P0 R0 : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (freqs : Finset ℝ) (weights : ℝ → ℂ)
    (Am Cs Ap Ar epsilon : ℝ)
    (hM0 : 1 ≤ M0) (hP : 1 ≤ P)
    (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (hAm : 0 ≤ Am) (hCs : 0 ≤ Cs)
    (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar)
    (hEps : 0 ≤ epsilon)
    (ha : 1 ≤ a)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBs : ∀ ps ∈ small, ‖bs ps‖ ≤ Cs)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ Ar)
    (hApprox : ∀ w : ℕ,
      ‖cutoff w -
        ∑ nu ∈ freqs, weights nu * sourcePhase w nu‖ ≤ epsilon) :
    ‖sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t -
      ∑ nu ∈ freqs, weights nu *
        sourceFourFactorAt small long R a b
          alpha bs bp d chi sigma0 sigma1 (t+nu)‖ ≤
      epsilon * (16*Am*Cs*Ap*Ar) := by
  classical
  have hsPos : ∀ ps ∈ small, 0 < ps := by
    intro ps hps
    have hh := (Finset.mem_Icc.mp (hSmall hps)).1
    omega
  have hpPos : ∀ p ∈ long, 0 < p := by
    intro p hp
    have hh := (Finset.mem_Icc.mp (hLong hp)).1
    omega
  have hrPos : ∀ r ∈ R, 0 < r := by
    intro r hr
    have hh := (Finset.mem_Icc.mp (hR hr)).1
    omega
  let F := sourceActualFourDyadTuples small long R a b
  let term := sourceActualFourDyadLiteralTerm
    alpha bs bp d chi sigma0 sigma1 t
  let approx : ℕ → ℂ :=
    fun w => ∑ nu ∈ freqs, weights nu * sourcePhase w nu
  have hFourier := source_actual_fourdyad_finite_fourier_separation
    small long R a b alpha bs bp d chi sigma0 sigma1 t
    freqs weights ha hsPos hpPos hrPos
  have hError :
      sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t -
      (∑ nu ∈ freqs, weights nu *
        sourceFourFactorAt small long R a b
          alpha bs bp d chi sigma0 sigma1 (t+nu)) =
      ∑ z ∈ F,
        (cutoff (sourceActualFourDyadProduct z) -
          approx (sourceActualFourDyadProduct z)) * term z := by
    rw [← hFourier]
    simp only [sourceActualSmoothFourDyadAt]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hError]
  calc
    ‖∑ z ∈ F,
        (cutoff (sourceActualFourDyadProduct z) -
          approx (sourceActualFourDyadProduct z)) * term z‖
      ≤ ∑ z ∈ F,
        ‖(cutoff (sourceActualFourDyadProduct z) -
          approx (sourceActualFourDyadProduct z)) * term z‖ :=
      norm_sum_le _ _
    _ = ∑ z ∈ F,
        ‖cutoff (sourceActualFourDyadProduct z) -
          approx (sourceActualFourDyadProduct z)‖ * ‖term z‖ := by
      simp only [norm_mul]
    _ ≤ ∑ z ∈ F, epsilon * ‖term z‖ := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right
        (hApprox (sourceActualFourDyadProduct z)) (norm_nonneg _)
    _ = epsilon * (∑ z ∈ F, ‖term z‖) := by
      rw [Finset.mul_sum]
    _ ≤ epsilon * (16*Am*Cs*Ap*Ar) := by
      exact mul_le_mul_of_nonneg_left
        (source_actual_fourdyad_absolute_l1_budget
          small long R a b M0 P P0 R0
          alpha bs bp d chi sigma0 sigma1 t Am Cs Ap Ar
          hM0 hP hP0 hR0 hAm hCs hAp hAr
          hM hSmall hLong hR hAlpha hBs hBp hd) hEps
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourFactorFrequencyTwist -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Real Mellin frequency shifts are EXACT unit-modulus twists
of the four original source coefficient sequences. This preserves
original joint characters, gcd classes, marked residual and dyads. -/
noncomputable def sourceActualCoefficientTwist
    (coeff : ℕ → ℂ) (nu : ℝ) (n : ℕ) : ℂ :=
  coeff n * sourcePhase n nu

theorem source_actual_coefficient_twist_norm
    (coeff : ℕ → ℂ) (nu : ℝ) (n : ℕ) :
    ‖sourceActualCoefficientTwist coeff nu n‖ = ‖coeff n‖ := by
  simp [sourceActualCoefficientTwist, norm_mul, sourcePhase_norm]

theorem source_actual_fourfactor_frequency_shift_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t nu : ℝ) :
    sourceFourFactorAt small long R a b alpha bs bp d
      chi sigma0 sigma1 (t+nu) =
    sourceFourFactorAt small long R a b
      (sourceActualCoefficientTwist alpha nu)
      (sourceActualCoefficientTwist bs nu)
      (sourceActualCoefficientTwist bp nu)
      (sourceActualCoefficientTwist d nu)
      chi sigma0 sigma1 t := by
  have hs :
      (∑ p ∈ small, bs p * (p:ℂ)⁻¹ * sourcePhase p (t+nu)) =
      ∑ p ∈ small, sourceActualCoefficientTwist bs nu p *
        (p:ℂ)⁻¹ * sourcePhase p t := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [sourcePhase_add p t nu]
    dsimp [sourceActualCoefficientTwist]
    ring
  have hp :
      (∑ p ∈ long, bp p * (p:ℂ)⁻¹ *
         sourcePhase p (sigma1+(t+nu))) =
      ∑ p ∈ long, sourceActualCoefficientTwist bp nu p *
        (p:ℂ)⁻¹ * sourcePhase p (sigma1+t) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [show sigma1+(t+nu)=(sigma1+t)+nu by ring,
      sourcePhase_add]
    dsimp [sourceActualCoefficientTwist]
    ring
  have hm :
      (∑ m ∈ Finset.Icc a b,
        alpha m * chi m * (m:ℂ)⁻¹ *
          sourcePhase m (sigma0+(t+nu))) =
      ∑ m ∈ Finset.Icc a b,
        sourceActualCoefficientTwist alpha nu m *
          chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [show sigma0+(t+nu)=(sigma0+t)+nu by ring,
      sourcePhase_add]
    dsimp [sourceActualCoefficientTwist]
    ring
  have hr :
      (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r (t+nu)) =
      ∑ r ∈ R, sourceActualCoefficientTwist d nu r *
        (r:ℂ)⁻¹ * sourcePhase r t := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [sourcePhase_add r t nu]
    dsimp [sourceActualCoefficientTwist]
    ring
  unfold sourceFourFactorAt
  rw [hs, hp, hm, hr]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadCutoffStability -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Stable original four-dyad sum under ANY pointwise cutoff
approximation. This is true absolute coefficient summation, not a
free residual majorant, Fourier estimate or cancellation input. -/
theorem source_actual_fourdyad_cutoff_uniform_stability
    (small long R : Finset ℕ)
    (a b M0 P P0 R0 : ℕ)
    (cutoff cutoff2 alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (Am Cs Ap Ar epsilon : ℝ)
    (hM0 : 1 ≤ M0) (hP : 1 ≤ P)
    (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (hAm : 0 ≤ Am) (hCs : 0 ≤ Cs)
    (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar)
    (hEps : 0 ≤ epsilon)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBs : ∀ ps ∈ small, ‖bs ps‖ ≤ Cs)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ Ar)
    (hApprox : ∀ w : ℕ, ‖cutoff w - cutoff2 w‖ ≤ epsilon) :
    ‖sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t -
      sourceActualSmoothFourDyadAt small long R a b
        cutoff2 alpha bs bp d chi sigma0 sigma1 t‖ ≤
        epsilon * (16*Am*Cs*Ap*Ar) := by
  let F := sourceActualFourDyadTuples small long R a b
  let term := sourceActualFourDyadLiteralTerm
    alpha bs bp d chi sigma0 sigma1 t
  have hDiff :
      sourceActualSmoothFourDyadAt small long R a b
          cutoff alpha bs bp d chi sigma0 sigma1 t -
        sourceActualSmoothFourDyadAt small long R a b
          cutoff2 alpha bs bp d chi sigma0 sigma1 t =
      ∑ z ∈ F, (cutoff (sourceActualFourDyadProduct z) -
          cutoff2 (sourceActualFourDyadProduct z)) * term z := by
    unfold sourceActualSmoothFourDyadAt
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hDiff]
  calc
    ‖∑ z ∈ F, (cutoff (sourceActualFourDyadProduct z) -
          cutoff2 (sourceActualFourDyadProduct z)) * term z‖ ≤
      ∑ z ∈ F, ‖(cutoff (sourceActualFourDyadProduct z) -
          cutoff2 (sourceActualFourDyadProduct z)) * term z‖ :=
        norm_sum_le _ _
    _ = ∑ z ∈ F,
          ‖cutoff (sourceActualFourDyadProduct z) -
            cutoff2 (sourceActualFourDyadProduct z)‖ * ‖term z‖ := by
      simp only [norm_mul]
    _ ≤ ∑ z ∈ F, epsilon * ‖term z‖ := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right
        (hApprox (sourceActualFourDyadProduct z)) (norm_nonneg _)
    _ = epsilon * (∑ z ∈ F, ‖term z‖) := by
      rw [Finset.mul_sum]
    _ ≤ epsilon * (16*Am*Cs*Ap*Ar) := by
      exact mul_le_mul_of_nonneg_left
        (source_actual_fourdyad_absolute_l1_budget
          small long R a b M0 P P0 R0
          alpha bs bp d chi sigma0 sigma1 t Am Cs Ap Ar
          hM0 hP hP0 hR0 hAm hCs hAp hAr
          hM hSmall hLong hR hAlpha hBs hBp hd) hEps
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalWindowSupport -/

section

namespace Green64Analytic.CorrelationMellin

/-! The literal Fourier-separation amplitude in 03-shifted.tex is
 (w/Y)*psi1(w/Y)*w^(i*v1). This is the actual normalized
 size-cutoff weight, not a new freely chosen support function. -/
noncomputable def sourceActualOriginalWindowWeight
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (w : ℕ) : ℂ :=
  (((w:ℝ)/Y:ℂ) * psi1 ((w:ℝ)/Y)) *
    sourcePhase w v1

theorem source_actual_original_window_weight_support
    (Y A : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hY : 0 < Y) (hA : 1 ≤ A)
    (hPsi : ∀ u : ℝ, psi1 u ≠ 0 →
      (1/A ≤ u ∧ u ≤ A)) :
    ∀ w : ℕ, sourceActualOriginalWindowWeight Y psi1 v1 w ≠ 0 →
      Y ≤ A*(w:ℝ) ∧ (w:ℝ) ≤ A*Y := by
  intro w hnz
  have hPsiNZ : psi1 ((w:ℝ)/Y) ≠ 0 := by
    intro hz
    apply hnz
    simp only [sourceActualOriginalWindowWeight, hz, mul_zero, zero_mul]
  obtain ⟨hLo,hHi⟩ := hPsi _ hPsiNZ
  have hApos : 0 < A := by linarith
  have hLoCross : 1*Y ≤ (w:ℝ)*A :=
    (div_le_div_iff₀ hApos hY).mp hLo
  have hHiCross : (w:ℝ) ≤ A*Y :=
    (div_le_iff₀ hY).mp hHi
  exact ⟨by nlinarith, hHiCross⟩

/-- Exact zero-box or true four-dyad comparisons for the source's
original cutoff amplitude, including the Fourier phase twist. -/
theorem source_actual_original_window_zero_or_comparable
    (small long R : Finset ℕ)
    (a b M0 P P0 R0 : ℕ) (Y A : ℝ)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (hY : 0 < Y) (hA : 1 ≤ A)
    (hPsi : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0)) :
    (∀ t : ℝ,
      sourceActualSmoothFourDyadAt small long R a b
        (sourceActualOriginalWindowWeight Y psi1 v1)
        alpha bs bp d chi sigma0 sigma1 t = 0) ∨
    (Y ≤ (16*A)*(P:ℝ)*((M0*P0*R0:ℕ):ℝ) ∧
     ((M0*P0*R0:ℕ):ℝ)*(P:ℝ) ≤ (16*A)*Y) := by
  apply source_actual_smooth_fourdyad_zero_or_comparable
    small long R a b M0 P P0 R0
    (sourceActualOriginalWindowWeight Y psi1 v1)
    alpha bs bp d chi sigma0 sigma1 Y A
    hY.le hA hM hSmall hLong hR
  exact source_actual_original_window_weight_support
    Y A psi1 v1 hY hA hPsi
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalWindowFourier -/

section

open scoped FourierTransform SchwartzMap ContDiff
namespace Green64Analytic.CorrelationMellin

/-! Exact original window (w/Y) psi1(w/Y) w^(i v1)
is an evaluation of the Fourier-inverted genuine Schwartz
logarithmic window, with NO replacement cutoff or coefficient. -/
theorem source_actual_original_window_schwartz_fourier_exact
    (A Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (w : ℕ)
    (hA : 1 ≤ A) (hY : 0 < Y) (hw : 0 < w)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    sourceActualOriginalWindowWeight Y psi1 v1 w =
    (𝓕⁻ (𝓕 (sourceActualLogWindowSchwartz
        A psi1 hA hSmooth hSupport)))
      (Real.log ((w:ℝ)/Y)) * sourcePhase w v1 := by
  let f : 𝓢(ℝ,ℂ) :=
    sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  have hInv : 𝓕⁻ (𝓕 f) = f :=
    source_actual_log_window_fourier_inversion
      A psi1 hA hSmooth hSupport
  have hVal := congrArg
    (fun (g : 𝓢(ℝ,ℂ)) => g (Real.log ((w:ℝ)/Y))) hInv
  have hWpos : (0:ℝ) < w := by exact_mod_cast hw
  have hRatio : 0 < ((w:ℝ)/Y) := div_pos hWpos hY
  have hRaw : (f : ℝ → ℂ) (Real.log ((w:ℝ)/Y)) =
      sourceActualLogWindow psi1 (Real.log ((w:ℝ)/Y)) := rfl
  rw [hRaw] at hVal
  unfold sourceActualOriginalWindowWeight
  rw [hVal]
  simp only [sourceActualLogWindow, Real.exp_log hRatio, Complex.ofReal_div]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalWindowIntegral -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! The actual original source weight has an EXPLICIT exact
Fourier inversion integral, not only an abstract transform
identity. The Fourier convention has a 2*pi factor. -/
theorem source_actual_original_window_fourier_integral_exact
    (A Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (w : ℕ)
    (hA : 1 ≤ A) (hY : 0 < Y) (hw : 0 < w)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    sourceActualOriginalWindowWeight Y psi1 v1 w =
      (∫ ξ : ℝ,
        Complex.exp
          (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ) *
            Complex.I) •
        (𝓕 (sourceActualLogWindowSchwartz
          A psi1 hA hSmooth hSupport) : 𝓢(ℝ,ℂ)) ξ) *
      sourcePhase w v1 := by
  let f : 𝓢(ℝ,ℂ) :=
    sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  have hRoot := source_actual_original_window_schwartz_fourier_exact
    A Y psi1 v1 w hA hY hw hSmooth hSupport
  rw [hRoot]
  have hInv := SchwartzMap.fourierInv_coe (𝓕 f : 𝓢(ℝ,ℂ))
  have hFourier := Real.fourierInv_eq'
    ((𝓕 f : 𝓢(ℝ,ℂ)) : ℝ → ℂ) (Real.log ((w:ℝ)/Y))
  rw [hInv]
  simpa only [f] using congrArg
    (fun z : ℂ => z * sourcePhase w v1) hFourier
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSchwartzFourierTrunc -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! The genuine original Fourier transform integral can be truncated
at a real frequency radius R with error bounded by the ACTUAL L1
tail of the Fourier transform, using no Fourier approximant premise. -/
theorem source_actual_schwartz_fourier_truncation_error
    (f : 𝓢(ℝ,ℂ)) (R u : ℝ) :
    ‖(𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) u -
      (∫ ξ in {ξ : ℝ | |ξ| < R},
        Complex.exp
          (((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)*Complex.I) •
           (𝓕 f : 𝓢(ℝ,ℂ)) ξ)‖ ≤
      (∫ ξ in {ξ : ℝ | R ≤ |ξ|},
        ‖(𝓕 f : 𝓢(ℝ,ℂ)) ξ‖) := by
  let F : 𝓢(ℝ,ℂ) := 𝓕 f
  let S : Set ℝ := {ξ : ℝ | |ξ| < R}
  let g : ℝ → ℂ := fun ξ =>
    Complex.exp (((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)*Complex.I) • F ξ
  have hS : MeasurableSet S := by
    exact (isOpen_lt continuous_abs continuous_const).measurableSet
  have hGN (ξ : ℝ) : ‖g ξ‖ = ‖F ξ‖ := by
    dsimp [g]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hInner : Continuous (fun ξ : ℝ => ⟪ξ,u⟫) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hReal : Continuous (fun ξ : ℝ => 2*Real.pi*⟪ξ,u⟫) :=
    continuous_const.mul hInner
  have hComplex : Continuous (fun ξ : ℝ =>
      ((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)) :=
    Complex.ofRealCLM.continuous.comp hReal
  have hArg : Continuous (fun ξ : ℝ =>
      (((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)*Complex.I)) :=
    hComplex.mul continuous_const
  have hCG : Continuous g :=
    (Complex.continuous_exp.comp hArg).mul F.continuous
  have hIG : Integrable g volume :=
    F.integrable.mono hCG.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (hGN ξ).le))
  have hInverse : (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) u = ∫ ξ, g ξ := by
    rw [SchwartzMap.fourierInv_coe]
    exact Real.fourierInv_eq' (F : ℝ → ℂ) u
  have hSplit : (∫ ξ, g ξ) - (∫ ξ in S, g ξ) =
      (∫ ξ in Sᶜ, g ξ) :=
    (setIntegral_compl hS hIG).symm
  have hBound :
      ‖∫ ξ in Sᶜ, g ξ‖ ≤
        ∫ ξ in Sᶜ, ‖F ξ‖ := by
    calc
      _ ≤ ∫ ξ in Sᶜ, ‖g ξ‖ := norm_integral_le_integral_norm _
      _ = ∫ ξ in Sᶜ, ‖F ξ‖ := by
        simp_rw [hGN]
  calc
    _ = ‖∫ ξ in Sᶜ, g ξ‖ := by
      simpa only [hInverse, S, g] using
        congrArg norm hSplit
    _ ≤ ∫ ξ in Sᶜ, ‖F ξ‖ := hBound
    _ = ∫ ξ in {ξ : ℝ | R ≤ |ξ|}, ‖F ξ‖ := by
      have hSet : Sᶜ = {ξ : ℝ | R ≤ |ξ|} := by
        ext ξ
        simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      rw [hSet]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualWindowFourierPhase -/

section

open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! The true inverse-Fourier kernel at log(w/Y) separates as
Y^(-2 pi i xi) times the exact source phase w^(i(v1+2pi xi)).
Both the frequency and the original w, Y are kept literal. -/
theorem source_actual_window_fourier_phase_exact
    (Y : ℝ) (w : ℕ) (v1 ξ : ℝ)
    (hY : 0 < Y) (hw : 0 < w) :
    Complex.exp
      (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ)*Complex.I) *
        sourcePhase w v1 =
    Complex.exp
      (((-2*Real.pi*ξ*Real.log Y:ℝ):ℂ)*Complex.I) *
        sourcePhase w (v1+2*Real.pi*ξ) := by
  have hwR : (w:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hYne : Y ≠ 0 := hY.ne'
  unfold sourcePhase
  rw [Real.inner_apply, Real.log_div hwR hYne]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalWindowTruncSaving -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! Uniform truncated Fourier representation of the ACTUAL
(w/Y) psi1(w/Y) w^(i v1) source cutoff. No free hApprox:
arbitrary log saving follows from the fixed smooth compact bump. -/
theorem eventually_source_actual_original_window_truncation_saving
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (D : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (Y v1 : ℝ) (w : ℕ), 0 < Y → 0 < w →
      ‖sourceActualOriginalWindowWeight Y psi1 v1 w -
        (∫ ξ in {ξ : ℝ | |ξ| < L},
          Complex.exp
            (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ) *
              Complex.I) •
          (𝓕 (sourceActualLogWindowSchwartz
            A psi1 hA hSmooth hSupport) : 𝓢(ℝ,ℂ)) ξ) *
          sourcePhase w v1‖ ≤ (L^D)⁻¹ := by
  let f : 𝓢(ℝ,ℂ) :=
    sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  have hTail :=
    eventually_source_actual_fixed_log_window_fourier_tail_saving
      A psi1 hA hSmooth hSupport D
  filter_upwards [hTail] with L hTailL
  intro Y v1 w hY hw
  let u : ℝ := Real.log ((w:ℝ)/Y)
  let M : ℂ :=
    ∫ ξ in {ξ : ℝ | |ξ| < L},
      Complex.exp (((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)*Complex.I) •
        (𝓕 f : 𝓢(ℝ,ℂ)) ξ
  have hIdentity :
      sourceActualOriginalWindowWeight Y psi1 v1 w =
      (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) u * sourcePhase w v1 :=
    source_actual_original_window_schwartz_fourier_exact
      A Y psi1 v1 w hA hY hw hSmooth hSupport
  have hTrunc :
      ‖(𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) u - M‖ ≤
      (∫ ξ in {ξ : ℝ | L ≤ |ξ|},
        ‖(𝓕 f : 𝓢(ℝ,ℂ)) ξ‖) :=
    source_actual_schwartz_fourier_truncation_error f L u
  have hPhase : ‖sourcePhase w v1‖ = 1 :=
    sourcePhase_norm w v1
  change ‖sourceActualOriginalWindowWeight Y psi1 v1 w -
    M * sourcePhase w v1‖ ≤ (L^D)⁻¹
  rw [hIdentity, ← sub_mul, norm_mul, hPhase, mul_one]
  exact hTrunc.trans (by simpa only [f] using hTailL)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalTruncatedWeight -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! The original source cutoff with the actual truncated
Schwartz Fourier integral, defined also at w=0 to preserve
the exact zero of (w/Y)*psi1(w/Y). -/
noncomputable def sourceActualOriginalTruncatedWindowWeight
    (A Y : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (v1 L : ℝ) (w : ℕ) : ℂ :=
  if w = 0 then 0 else
    (∫ ξ in {ξ : ℝ | |ξ| < L},
      Complex.exp
        (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ) *
          Complex.I) •
      (𝓕 (sourceActualLogWindowSchwartz
        A psi1 hA hSmooth hSupport) : 𝓢(ℝ,ℂ)) ξ) *
    sourcePhase w v1
theorem eventually_source_actual_original_weight_truncation_all_nat
    (A : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (D : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (Y v1 : ℝ) (w : ℕ), 0 < Y →
      ‖sourceActualOriginalWindowWeight Y psi1 v1 w -
        sourceActualOriginalTruncatedWindowWeight
          A Y psi1 hA hSmooth hSupport v1 L w‖ ≤ (L^D)⁻¹ := by
  have hTail :=
    eventually_source_actual_original_window_truncation_saving
      A psi1 hA hSmooth hSupport D
  filter_upwards [hTail, eventually_ge_atTop (3:ℝ)] with L hTailL hL3
  intro Y v1 w hY
  by_cases hw : w = 0
  · subst w
    have hLpos : 0 < L := by linarith
    have hBound : (0:ℝ) ≤ (L^D)⁻¹ := by positivity
    simpa [sourceActualOriginalWindowWeight,
      sourceActualOriginalTruncatedWindowWeight] using hBound
  · have hwPos : 0 < w := Nat.pos_of_ne_zero hw
    simpa only [sourceActualOriginalTruncatedWindowWeight,
      if_neg hw] using hTailL Y v1 w hY hwPos
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualRoughRationalAlpha -/

section

namespace Green64Analytic.CorrelationMellin

/-! The original SourceAlphaDiscrepancy applied simultaneously to
every reduced rational gcd class d|den and the exact product
chi0*xi, after an arbitrary original dyadic alpha cut. Source
W-roughness supplies the required units: it is NOT a new
discrepancy or exceptional-set hypothesis. -/

theorem source_actual_rough_rational_alpha_discrepancy
    (L B x C : ℝ) (hL : 1 ≤ L)
    (alpha : ℕ → ℂ) (lo hi : ℕ)
    (hDisc : SourceAlphaDiscrepancy L B x alpha)
    (qBase den d : ℕ)
    (hBasePos : 0 < qBase) (hDenPos : 0 < den) (hd : d ∣ den)
    (chi0 : DirichletCharacter ℂ qBase)
    (xi : DirichletCharacter ℂ (den/d))
    (hBase : (qBase:ℝ) ≤ L^C)
    (hDen : (den:ℝ) ≤ L^C)
    (hBC : 2*C ≤ B)
    (hW : L^B ≤ Real.exp (Real.sqrt L))
    (hRough : ∀ m : ℕ, alpha m ≠ 0 →
       ∀ p : ℕ, p.Prime → p ∣ m →
         Real.exp (Real.sqrt L) < (p:ℝ))
    (a b : ℕ) (ha : 1 ≤ a) (hb : (b:ℝ) ≤ x^2)
    (sigma0 t : ℝ) (hFreq : |sigma0+t| ≤ L^B) :
    ‖∑ m ∈ Finset.Icc a b,
        sourceAlphaDyadicCut alpha lo hi m *
          chi0 m * xi m * (m:ℂ)⁻¹ *
          sourcePhase m (sigma0+t)‖ ≤ L^(-B) := by
  classical
  let q : ℕ := den/d
  let joint : DirichletCharacter ℂ (qBase*q) :=
    sourceJointCharacter qBase q chi0 xi
  have hMod : ((qBase*q:ℕ):ℝ) ≤ L^B := by
    simpa only [q] using
      source_actual_joint_reduced_modulus_budget
        qBase den d L C B hL hBase hDen hBC
  have hCut := source_alpha_dyadic_cut_preserves_discrepancy
    L B x alpha lo hi hDisc
  have hBound := hCut (qBase*q) joint a b (sigma0+t)
    hMod ha hb hFreq
  have hTerm (m : ℕ) (hm : m ∈ Finset.Icc a b) :
      sourceAlphaDyadicCut alpha lo hi m *
        chi0 m * xi m * (m:ℂ)⁻¹ *
        sourcePhase m (sigma0+t) =
      sourceAlphaDyadicCut alpha lo hi m *
        joint m * (m:ℂ)⁻¹ *
        sourcePhase m (sigma0+t) := by
    by_cases hz : sourceAlphaDyadicCut alpha lo hi m = 0
    · simp [hz]
    · have hAlpha : alpha m ≠ 0 := by
        intro hZero
        exact hz (by simp [sourceAlphaDyadicCut, hZero])
      have hChar := source_actual_joint_character_rough_alpha
        qBase den d m chi0 xi L C B
        hBasePos hDenPos hd hL hBase hDen hBC hW
        (hRough m hAlpha)
      have hChar' : joint m = chi0 m * xi m := by
        simpa only [joint,q] using hChar
      rw [hChar']
      ring
  calc
    _ = ‖∑ m ∈ Finset.Icc a b,
       sourceAlphaDyadicCut alpha lo hi m *
         joint m * (m:ℂ)⁻¹ *
         sourcePhase m (sigma0+t)‖ := by
      congr 1
      exact Finset.sum_congr rfl hTerm
    _ ≤ L^(-B) := hBound
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualTruncatedWeightSeparation -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-! Exact Fourier separation of the ACTUAL truncated window.
The entire dependence on the original product w is through
sourcePhase w (v1+2*pi*xi), so the source fourfactor shifts as proven. -/
theorem source_actual_truncated_window_phase_separation
    (A Y : ℝ) (psi1 : ℝ → ℂ) (v1 L : ℝ) (w : ℕ)
    (hA : 1 ≤ A) (hY : 0 < Y) (hw : 0 < w)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    sourceActualOriginalTruncatedWindowWeight
        A Y psi1 hA hSmooth hSupport v1 L w =
      ∫ ξ in {ξ : ℝ | |ξ| < L},
        (Complex.exp
          (((-2*Real.pi*ξ*Real.log Y:ℝ):ℂ)*Complex.I) *
          ((𝓕 (sourceActualLogWindowSchwartz
            A psi1 hA hSmooth hSupport) : 𝓢(ℝ,ℂ)) ξ)) *
          sourcePhase w (v1+2*Real.pi*ξ) := by
  let f : 𝓢(ℝ,ℂ) :=
    sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw
  simp only [sourceActualOriginalTruncatedWindowWeight, if_neg hw0]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with ξ
  have hPhase := source_actual_window_fourier_phase_exact
    Y w v1 ξ hY hw
  simp only [smul_eq_mul]
  calc
    (Complex.exp
        (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ)*Complex.I) *
        (𝓕 f : 𝓢(ℝ,ℂ)) ξ) * sourcePhase w v1 =
      (Complex.exp
        (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫:ℝ):ℂ)*Complex.I) *
          sourcePhase w v1) * (𝓕 f : 𝓢(ℝ,ℂ)) ξ := by ring
    _ = (Complex.exp
        (((-2*Real.pi*ξ*Real.log Y:ℝ):ℂ)*Complex.I) *
          sourcePhase w (v1+2*Real.pi*ξ)) *
          (𝓕 f : 𝓢(ℝ,ℂ)) ξ := by rw [hPhase]
    _ = _ := by ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalFourierKernel -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationMellin

/-- The actual source inverse-Fourier kernel after separating log(w/Y). -/
noncomputable def sourceActualLogWindowFourierKernel
    (f : 𝓢(ℝ, ℂ)) (Y : ℝ) (ξ : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*ξ*Real.log Y : ℝ) : ℂ)*Complex.I) * (𝓕 f) ξ

theorem source_actual_log_window_fourier_kernel_norm
    (f : 𝓢(ℝ, ℂ)) (Y ξ : ℝ) :
    ‖sourceActualLogWindowFourierKernel f Y ξ‖ = ‖(𝓕 f) ξ‖ := by
  simp only [sourceActualLogWindowFourierKernel, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem source_actual_log_window_fourier_kernel_continuous
    (f : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    Continuous (sourceActualLogWindowFourierKernel f Y) := by
  unfold sourceActualLogWindowFourierKernel
  have hExp : Continuous (fun ξ : ℝ =>
      Complex.exp (((-2*Real.pi*ξ*Real.log Y : ℝ) : ℂ)*Complex.I)) := by
    fun_prop
  exact hExp.mul (𝓕 f).continuous

theorem source_actual_log_window_fourier_kernel_integrable
    (f : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    Integrable (sourceActualLogWindowFourierKernel f Y) := by
  exact (𝓕 f).integrable.mono
    (source_actual_log_window_fourier_kernel_continuous f Y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ =>
      (source_actual_log_window_fourier_kernel_norm f Y ξ).le))

theorem source_actual_log_window_fourier_kernel_mass_le
    (f : 𝓢(ℝ, ℂ)) (Y : ℝ) (S : Set ℝ) :
    (∫ ξ in S, ‖sourceActualLogWindowFourierKernel f Y ξ‖) ≤
      ∫ ξ : ℝ, ‖(𝓕 f) ξ‖ := by
  simp_rw [source_actual_log_window_fourier_kernel_norm]
  have hUniv : IntegrableOn (fun ξ : ℝ => ‖(𝓕 f) ξ‖) Set.univ := by
    simpa using (𝓕 f).integrable.norm
  simpa only [setIntegral_univ] using
    (setIntegral_mono_set (s := S) (t := Set.univ)
      hUniv (Filter.Eventually.of_forall (fun ξ => norm_nonneg ((𝓕 f) ξ)))
      (Set.subset_univ S).eventuallySubset)

/-- Exact finite or infinite frequency representation of the genuine source
window after separation; the phase uses the required factor 2*pi. -/
theorem source_actual_log_window_fourier_kernel_separation
    (f : 𝓢(ℝ, ℂ)) (Y v1 : ℝ) (w : ℕ) (S : Set ℝ)
    (hY : 0 < Y) (hw : 0 < w) :
    (∫ ξ in S, Complex.exp
      (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫ : ℝ):ℂ)*Complex.I) *
        (𝓕 f) ξ) * sourcePhase w v1 =
    ∫ ξ in S, sourceActualLogWindowFourierKernel f Y ξ *
      sourcePhase w (v1+2*Real.pi*ξ) := by
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with ξ
  have hPhase := source_actual_window_fourier_phase_exact Y w v1 ξ hY hw
  unfold sourceActualLogWindowFourierKernel
  calc
    _ = (Complex.exp
          (((2*Real.pi*⟪ξ,Real.log ((w:ℝ)/Y)⟫ : ℝ):ℂ)*Complex.I) *
          sourcePhase w v1) * (𝓕 f) ξ := by ring
    _ = _ := by rw [hPhase]; ring

/-- Real source Fourier frequencies at a fixed log-power cutoff fit in an
explicit log-power budget, uniformly over the original phase v1. -/
theorem source_actual_original_fourier_frequency_budget
    (L v1 ξ : ℝ) (sv sf : ℕ) (hL : 3 ≤ L)
    (hv : |v1| ≤ L^sv) (hξ : |ξ| ≤ L^sf) :
    |v1+2*Real.pi*ξ| ≤ L^(max sv sf+2) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hPi : 0 ≤ 2*Real.pi := by positivity
  have hK : 1+2*Real.pi ≤ L^2 := by
    nlinarith [Real.pi_lt_four, sq_nonneg (L-3)]
  have hvPow := pow_le_pow_right₀ hL1 (Nat.le_max_left sv sf)
  have hξPow := pow_le_pow_right₀ hL1 (Nat.le_max_right sv sf)
  calc
    _ ≤ |v1|+|2*Real.pi*ξ| := abs_add_le _ _
    _ = |v1|+(2*Real.pi)*|ξ| := by
      rw [abs_mul, abs_of_nonneg hPi]
    _ ≤ L^sv+(2*Real.pi)*L^sf :=
      add_le_add hv (mul_le_mul_of_nonneg_left hξ hPi)
    _ ≤ (1+2*Real.pi)*L^(max sv sf) := by
      nlinarith
    _ ≤ L^2*L^(max sv sf) :=
      mul_le_mul_of_nonneg_right hK (pow_nonneg hL0 _)
    _ = L^(max sv sf+2) := by rw [pow_add]; ring

/-- The retained integral is exactly the source's genuine truncated original
window on the full literal four-dyad sum. Zero integers never enter this sum. -/
theorem source_actual_fourdyad_truncated_window_kernel_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t A Y v1 radius : ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hY : 0 < Y) (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps) (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    sourceActualSmoothFourDyadAt small long R a b
      (sourceActualOriginalTruncatedWindowWeight
        A Y psi1 hA hSmooth hSupport v1 radius)
      alpha bs bp d chi sigma0 sigma1 t =
    sourceActualSmoothFourDyadAt small long R a b
      (fun w => ∫ ξ in {ξ : ℝ | |ξ| < radius},
        sourceActualLogWindowFourierKernel
          (sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport) Y ξ *
            sourcePhase w (v1+2*Real.pi*ξ))
      alpha bs bp d chi sigma0 sigma1 t := by
  unfold sourceActualSmoothFourDyadAt
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ∈ ((Finset.Icc a b).product small).product (long.product R) := hz
  obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hz'
  obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
  obtain ⟨hpl,hrl⟩ := Finset.mem_product.mp hzPR
  have hmPos : 0 < z.1.1 := by have hh := (Finset.mem_Icc.mp hm).1; omega
  have hpsPos := hs z.1.2 hps
  have hpPos := hp z.2.1 hpl
  have hrPos := hr z.2.2 hrl
  have hw : 0 < sourceActualFourDyadProduct z := by
    unfold sourceActualFourDyadProduct
    positivity
  rw [source_actual_truncated_window_phase_separation
    A Y psi1 v1 radius (sourceActualFourDyadProduct z)
    hA hY hw hSmooth hSupport]
  rfl
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadIntegralSeparation -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Interchange the genuine Fourier integral with a FINITE source
four-dyad convolution. No free energy or residual estimate.
The only analytical input is integrability of the Fourier weight. -/
theorem source_actual_fourdyad_integral_separation
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t : ℝ)
    (S : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ)
    (cutoff : ℕ → ℂ)
    (hK : IntegrableOn K S) (hFreq : Continuous freq)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r)
    (hCut : ∀ w : ℕ, 0 < w →
      cutoff w = ∫ ξ in S, K ξ * sourcePhase w (freq ξ)) :
    sourceActualSmoothFourDyadAt small long R a b
       cutoff alpha bs bp d chi sigma0 sigma1 t =
    ∫ ξ in S, K ξ *
      sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 (t+freq ξ) := by
  classical
  let F := sourceActualFourDyadTuples small long R a b
  let term := sourceActualFourDyadLiteralTerm
    alpha bs bp d chi sigma0 sigma1 t
  have hPhaseCont (w : ℕ) :
      Continuous (fun ξ : ℝ => sourcePhase w (freq ξ)) := by
    have hBase : Continuous (fun v : ℝ => sourcePhase w v) := by
      simpa only [zero_add] using sourcePhase_continuous w 0
    exact hBase.comp hFreq
  have hTermInt (z : (ℕ × ℕ) × (ℕ × ℕ)) :
      IntegrableOn (fun ξ : ℝ =>
        K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z) S := by
    let phase : ℝ → ℂ :=
      fun ξ => sourcePhase (sourceActualFourDyadProduct z)
        (freq ξ) * term z
    have hPhase : Continuous phase :=
      (hPhaseCont (sourceActualFourDyadProduct z)).mul
        continuous_const
    have hBound : ∀ᵐ ξ : ℝ ∂(volume.restrict S),
        ‖phase ξ‖ ≤ ‖term z‖ := by
      filter_upwards with ξ
      simp only [phase, norm_mul, sourcePhase_norm, one_mul]
      exact le_refl _
    have hResult : IntegrableOn (fun ξ : ℝ => K ξ * phase ξ) S :=
      hK.mul_bdd hPhase.aestronglyMeasurable hBound
    simpa only [phase, mul_assoc] using hResult
  have hProductPos (z : (ℕ × ℕ) × (ℕ × ℕ)) (hz : z ∈ F) :
      0 < sourceActualFourDyadProduct z := by
    have hzBase : z ∈
        ((Finset.Icc a b).product small).product (long.product R) := by
      simpa only [F,sourceActualFourDyadTuples] using hz
    obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hzBase
    obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
    obtain ⟨hpl,hrl⟩ := Finset.mem_product.mp hzPR
    have hmPos : 0 < z.1.1 :=
      lt_of_lt_of_le (by omega : 0 < a) (Finset.mem_Icc.mp hm).1
    have hpsPos := hs z.1.2 hps
    have hpPos := hp z.2.1 hpl
    have hrPos := hr z.2.2 hrl
    simp only [sourceActualFourDyadProduct]
    positivity
  have hLeft :
      sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t =
      ∑ z ∈ F, ∫ ξ in S,
        K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z := by
    unfold sourceActualSmoothFourDyadAt
    apply Finset.sum_congr rfl
    intro z hz
    have hzF : z ∈ F := by simpa only [F] using hz
    rw [hCut (sourceActualFourDyadProduct z) (hProductPos z hzF)]
    rw [integral_mul_const]
  have hFubini :
      (∑ z ∈ F, ∫ ξ in S,
        K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z) =
      ∫ ξ in S,
        ∑ z ∈ F, K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z := by
    rw [integral_finsetSum F (fun z hz => hTermInt z)]
  calc
    sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t =
      (∑ z ∈ F, ∫ ξ in S,
        K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z) := hLeft
    _ = (∫ ξ in S,
        ∑ z ∈ F, K ξ * sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z) := hFubini
    _ = (∫ ξ in S, K ξ *
        (∑ z ∈ F, sourcePhase (sourceActualFourDyadProduct z)
          (freq ξ) * term z)) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = (∫ ξ in S, K ξ *
        sourceFourFactorAt small long R a b alpha bs bp d chi
          sigma0 sigma1 (t+freq ξ)) := by
      apply integral_congr_ae
      filter_upwards with ξ
      congr 1
      simpa only [sourceActualSmoothFourDyadAt,F,term] using
        source_actual_fourdyad_single_frequency_exact
          small long R a b alpha bs bp d chi sigma0 sigma1
          t (freq ξ) ha hs hp hr
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadL2Lift -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- The pullback of Lebesgue measure to a closed real interval is finite. -/
noncomputable instance sourceActualIccComapIsFinite (T : ℝ) :
    IsFiniteMeasure
      (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) where
  measure_univ_lt_top := by
    let hEmb : MeasurableEmbedding
        (Subtype.val : Set.Icc (-T) T → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Icc
    rw [Measure.comap_apply Subtype.val Subtype.val_injective
      (fun s hs => hEmb.measurableSet_image.mpr hs) volume MeasurableSet.univ]
    have himage :
        (Subtype.val : Set.Icc (-T) T → ℝ) '' Set.univ = Set.Icc (-T) T := by
      ext x
      simp
    rw [himage]
    exact (measure_Icc_lt_top :
      volume (Set.Icc (-T) T) < ⊤)


/-- The literal source four-dyad term, restricted to the compact
Mellin interval.  This is the actual source term, not a proxy. -/
noncomputable def sourceActualFourDyadTermOnIcc
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    C(Set.Icc (-T) T, ℂ) where
  toFun t :=
    sourceActualFourDyadLiteralTerm alpha bs bp d chi
      sigma0 sigma1 t.1 z
  continuous_toFun := by
    have hm : Continuous (fun t : ℝ =>
        alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹ *
          sourcePhase z.1.1 (sigma0+t)) :=
      continuous_const.mul (sourcePhase_continuous z.1.1 sigma0)
    have hsPhase : Continuous (fun t : ℝ => sourcePhase z.1.2 t) := by
      simpa only [zero_add] using sourcePhase_continuous z.1.2 0
    have hs : Continuous (fun t : ℝ =>
        bs z.1.2 * (z.1.2:ℂ)⁻¹ * sourcePhase z.1.2 t) :=
      continuous_const.mul hsPhase
    have hp : Continuous (fun t : ℝ =>
        bp z.2.1 * (z.2.1:ℂ)⁻¹ *
          sourcePhase z.2.1 (sigma1+t)) :=
      continuous_const.mul (sourcePhase_continuous z.2.1 sigma1)
    have hrPhase : Continuous (fun t : ℝ => sourcePhase z.2.2 t) := by
      simpa only [zero_add] using sourcePhase_continuous z.2.2 0
    have hr : Continuous (fun t : ℝ =>
        d z.2.2 * (z.2.2:ℂ)⁻¹ * sourcePhase z.2.2 t) :=
      continuous_const.mul hrPhase
    have hterm : Continuous (fun t : ℝ =>
        sourceActualFourDyadLiteralTerm alpha bs bp d chi
          sigma0 sigma1 t z) := by
      change Continuous (fun t : ℝ =>
        ((alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹ *
             sourcePhase z.1.1 (sigma0+t)) *
          (bs z.1.2 * (z.1.2:ℂ)⁻¹ * sourcePhase z.1.2 t)) *
         (bp z.2.1 * (z.2.1:ℂ)⁻¹ *
             sourcePhase z.2.1 (sigma1+t)) *
          (d z.2.2 * (z.2.2:ℂ)⁻¹ * sourcePhase z.2.2 t))
      exact ((hm.mul hs).mul hp).mul hr
    exact hterm.comp continuous_subtype_val

/-- The genuine L² vector represented by one literal four-dyad term
on the compact Mellin interval. -/
noncomputable def sourceActualFourDyadTermL2
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    Lp ℂ 2 (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) :=
  (ContinuousMap.toLp 2 (Measure.comap Subtype.val volume) ℂ)
    (sourceActualFourDyadTermOnIcc T alpha bs bp d chi sigma0 sigma1 z)

/-- The actual finite four-dyad family as an L²([-T,T])-valued
frequency map.  Each coefficient is the literal product phase. -/
noncomputable def sourceActualFourDyadL2Lift
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (ξ : ℝ) :
    Lp ℂ 2 (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) :=
  ∑ z ∈ sourceActualFourDyadTuples small long R a b,
    sourcePhase (sourceActualFourDyadProduct z) (freq ξ) •
      sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z

theorem source_actual_fourdyad_L2_lift_continuous
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (hFreq : Continuous freq) :
    Continuous (sourceActualFourDyadL2Lift small long R a b T
      alpha bs bp d chi sigma0 sigma1 freq) := by
  classical
  unfold sourceActualFourDyadL2Lift
  apply continuous_finset_sum
  intro z hz
  have hPhase : Continuous (fun ξ : ℝ =>
      sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) := by
    have hBase : Continuous (fun u : ℝ =>
        sourcePhase (sourceActualFourDyadProduct z) u) := by
      simpa only [zero_add] using
        sourcePhase_continuous (sourceActualFourDyadProduct z) 0
    exact hBase.comp hFreq
  exact hPhase.smul continuous_const

theorem source_actual_fourdyad_L2_lift_aestronglyMeasurable
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (hFreq : Continuous freq) :
    AEStronglyMeasurable
      (sourceActualFourDyadL2Lift small long R a b T
        alpha bs bp d chi sigma0 sigma1 freq) := by
  exact (source_actual_fourdyad_L2_lift_continuous
    small long R a b T alpha bs bp d chi sigma0 sigma1 freq hFreq).aestronglyMeasurable

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadL2Bochner -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- Bochner--Fubini expansion for the literal source four-dyad family.
This identifies the vector integral in the genuine L²([-T,T]) space
with the finite sum of the scalar Fourier coefficients times the
literal source L² vectors. -/
theorem source_actual_fourdyad_L2_bochner_finset
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (S : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ)
    (hK : IntegrableOn K S) (hFreq : Continuous freq) :
    (∫ ξ in S, K ξ •
      sourceActualFourDyadL2Lift small long R a b T
        alpha bs bp d chi sigma0 sigma1 freq ξ) =
    ∑ z ∈ sourceActualFourDyadTuples small long R a b,
      (∫ ξ in S, K ξ *
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) •
      sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z := by
  classical
  let F := sourceActualFourDyadTuples small long R a b
  have hPhase (z : (ℕ × ℕ) × (ℕ × ℕ)) :
      Continuous (fun ξ : ℝ =>
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) := by
    have hBase : Continuous (fun u : ℝ =>
        sourcePhase (sourceActualFourDyadProduct z) u) := by
      simpa only [zero_add] using
        sourcePhase_continuous (sourceActualFourDyadProduct z) 0
    exact hBase.comp hFreq
  have hScalar (z : (ℕ × ℕ) × (ℕ × ℕ)) :
      IntegrableOn (fun ξ : ℝ => K ξ *
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) S := by
    apply hK.mul_bdd (hPhase z).aestronglyMeasurable
    filter_upwards with ξ
    simp only [sourcePhase_norm]
    exact le_rfl
  unfold sourceActualFourDyadL2Lift
  change
    (∫ ξ in S, K ξ •
      (∑ z ∈ F,
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ) •
          sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z)) =
    ∑ z ∈ F,
      (∫ ξ in S, K ξ *
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) •
          sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z
  simp_rw [Finset.smul_sum, smul_smul]
  rw [integral_finsetSum F]
  · apply Finset.sum_congr rfl
    intro z hz
    exact integral_smul_const _ _
  · intro z hz
    exact (hScalar z).smul_const _

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadL2Identification -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- The genuine finite literal four-dyad sum as a continuous function
on the compact Mellin interval. -/
noncomputable def sourceActualFourDyadSumOnIcc
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    C(Set.Icc (-T) T, ℂ) :=
  ∑ z ∈ sourceActualFourDyadTuples small long R a b,
    cutoff (sourceActualFourDyadProduct z) •
      sourceActualFourDyadTermOnIcc T alpha bs bp d chi sigma0 sigma1 z

/-- The L²-valued frequency lift is exactly the continuous-function
image of the literal scalar four-dyad sum on the Mellin interval. -/
theorem source_actual_fourdyad_L2_lift_eq_toLp
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (ξ : ℝ) :
    sourceActualFourDyadL2Lift small long R a b T
      alpha bs bp d chi sigma0 sigma1 freq ξ =
    (ContinuousMap.toLp 2
      (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) ℂ)
      (sourceActualFourDyadSumOnIcc small long R a b T
        (fun w => sourcePhase w (freq ξ))
        alpha bs bp d chi sigma0 sigma1) := by
  classical
  unfold sourceActualFourDyadL2Lift sourceActualFourDyadTermL2
    sourceActualFourDyadSumOnIcc
  simp only [map_sum, map_smul]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadL2Norm -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- Exact norm formula for a compact-domain continuous complex function
viewed in L². -/
theorem source_continuous_toLp_norm_sq
    {α : Type} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : C(α, ℂ)) :
    ‖(ContinuousMap.toLp 2 μ ℂ) f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ContinuousMap.inner_toLp]
  simp_rw [Complex.mul_conj, ← Complex.sq_norm]
  change Complex.re (∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ) =
    ∫ x, ‖f x‖ ^ 2 ∂μ
  calc
    _ = Complex.re (((∫ x, ‖f x‖ ^ 2 ∂μ) : ℝ) : ℂ) :=
      congrArg Complex.re (integral_ofReal (𝕜 := ℂ) (μ := μ)
        (f := fun x => ‖f x‖ ^ 2))
    _ = _ := by simp

/-- Exact L² norm identification for the literal source frequency lift:
its Hilbert norm is the centered mean square of the same source
four-factor polynomial, with no proxy or approximation. -/
theorem source_actual_fourdyad_L2_lift_norm_sq
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (ξ : ℝ)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    ‖sourceActualFourDyadL2Lift small long R a b T
      alpha bs bp d chi sigma0 sigma1 freq ξ‖ ^ 2 =
    ∫ t : Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 (t.1 + freq ξ)‖ ^ 2
      ∂(Measure.comap Subtype.val volume :
        Measure (Set.Icc (-T) T)) := by
  rw [source_actual_fourdyad_L2_lift_eq_toLp,
    source_continuous_toLp_norm_sq]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  have hExact := source_actual_fourdyad_single_frequency_exact
    small long R a b alpha bs bp d chi sigma0 sigma1
    t.1 (freq ξ) ha hs hp hr
  rw [← hExact]
  simp [sourceActualFourDyadSumOnIcc,
    sourceActualSmoothFourDyadAt,
    sourceActualFourDyadTermOnIcc]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadL2SetNorm -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- Exact set-integral form of the literal source L² lift norm.
This is the normalization used by the source three-way physical
estimate, so no change-of-measure hypothesis remains. -/
theorem source_actual_fourdyad_L2_lift_norm_sq_setIntegral
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (freq : ℝ → ℝ) (ξ : ℝ)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    ‖sourceActualFourDyadL2Lift small long R a b T
      alpha bs bp d chi sigma0 sigma1 freq ξ‖ ^ 2 =
    ∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 (t + freq ξ)‖ ^ 2 := by
  rw [source_actual_fourdyad_L2_lift_norm_sq
    small long R a b T alpha bs bp d chi sigma0 sigma1
    freq ξ ha hs hp hr]
  exact integral_subtype_comap measurableSet_Icc
    (fun t : ℝ =>
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 (t + freq ξ)‖ ^ 2)

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadFourierL1MeanSquare -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- Continuous Fourier separation for the literal source four-dyad
polynomial. A uniform translated centered mean-square bound for the
same source polynomial passes through the actual Fourier kernel with
only the square of its L¹ mass. The hypothesis uses the source's
literal real set-integral normalization. Bochner integrability is
derived here, not assumed. -/
theorem source_actual_fourdyad_fourier_l1_mean_square
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (S : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ)
    (B mass : ℝ)
    (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hFreq : Continuous freq)
    (hK : IntegrableOn K S)
    (hGB : ∀ᵐ ξ ∂volume.restrict S,
      (∫ t in Set.Icc (-T) T,
        ‖sourceFourFactorAt small long R a b alpha bs bp d chi
          sigma0 sigma1 (t + freq ξ)‖ ^ 2) ≤ B)
    (hKmass : (∫ ξ in S, ‖K ξ‖) ≤ mass)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    ‖∫ ξ in S, K ξ •
      sourceActualFourDyadL2Lift small long R a b T
        alpha bs bp d chi sigma0 sigma1 freq ξ‖ ^ 2
      ≤ mass ^ 2 * B := by
  classical
  let G := sourceActualFourDyadL2Lift small long R a b T
    alpha bs bp d chi sigma0 sigma1 freq
  let C : ℝ := ∑ z ∈ sourceActualFourDyadTuples small long R a b,
    ‖sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z‖
  have hGcont : Continuous G :=
    source_actual_fourdyad_L2_lift_continuous
      small long R a b T alpha bs bp d chi sigma0 sigma1 freq hFreq
  have hGbound : ∀ ξ : ℝ, ‖G ξ‖ ≤ C := by
    intro ξ
    dsimp only [G, C]
    unfold sourceActualFourDyadL2Lift
    calc
      ‖∑ z ∈ sourceActualFourDyadTuples small long R a b,
        sourcePhase (sourceActualFourDyadProduct z) (freq ξ) •
          sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z‖
          ≤ ∑ z ∈ sourceActualFourDyadTuples small long R a b,
              ‖sourcePhase (sourceActualFourDyadProduct z) (freq ξ) •
                sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z‖ :=
            norm_sum_le _ _
      _ = ∑ z ∈ sourceActualFourDyadTuples small long R a b,
              ‖sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z‖ := by
            apply Finset.sum_congr rfl
            intro z hz
            simp only [norm_smul, sourcePhase_norm, one_mul]
  have hKG : IntegrableOn (fun ξ => K ξ • G ξ) S := by
    exact hK.smul_bdd C hGcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hGbound)
  have hNormGB : ∀ᵐ ξ ∂volume.restrict S, ‖G ξ‖ ^ 2 ≤ B := by
    filter_upwards [hGB] with ξ hξ
    rw [source_actual_fourdyad_L2_lift_norm_sq_setIntegral
      small long R a b T alpha bs bp d chi sigma0 sigma1
      freq ξ ha hs hp hr]
    exact hξ
  apply source_continuous_fourier_l1_mean_square
    K G S B mass hB hmass
  · exact hK.norm
  · exact hKG
  · exact hNormGB
  · exact hKmass

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadBochnerScalarSquare -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-- Every literal smooth four-dyad cutoff has its exact scalar mean square
as the Hilbert norm of the corresponding source vector. No coefficient,
window, character, or tuple support is changed. -/
theorem source_actual_fourdyad_cutoff_L2_norm_sq_setIntegral
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    ‖(ContinuousMap.toLp 2
      (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) ℂ)
      (sourceActualFourDyadSumOnIcc small long R a b T
        cutoff alpha bs bp d chi sigma0 sigma1)‖^2 =
    ∫ t in Set.Icc (-T) T,
      ‖sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t‖^2 := by
  rw [source_continuous_toLp_norm_sq]
  have hPoint (t : Set.Icc (-T) T) :
      sourceActualFourDyadSumOnIcc small long R a b T
        cutoff alpha bs bp d chi sigma0 sigma1 t =
      sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t.1 := by
    simp [sourceActualFourDyadSumOnIcc, sourceActualSmoothFourDyadAt,
      sourceActualFourDyadTermOnIcc]
  simp_rw [hPoint]
  exact integral_subtype_comap
    (measurableSet_Icc : MeasurableSet (Set.Icc (-T) T))
    (fun t : ℝ => ‖sourceActualSmoothFourDyadAt small long R a b
      cutoff alpha bs bp d chi sigma0 sigma1 t‖^2)

/-- Exact Bochner-Fubini identification at the scalar squared-energy level.
The cutoff is the genuine integral of K times the literal product phase;
this identity applies equally to bounded and unbounded frequency sets. -/
theorem source_actual_fourdyad_bochner_norm_sq_setIntegral
    (small long R : Finset ℕ) (a b : ℕ)
    (T : ℝ) (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (S : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ)
    (hK : IntegrableOn K S) (hFreq : Continuous freq) :
    ‖∫ ξ in S, K ξ • sourceActualFourDyadL2Lift
        small long R a b T alpha bs bp d chi sigma0 sigma1 freq ξ‖^2 =
    ∫ t in Set.Icc (-T) T,
      ‖sourceActualSmoothFourDyadAt small long R a b
        (fun w => ∫ ξ in S, K ξ * sourcePhase w (freq ξ))
        alpha bs bp d chi sigma0 sigma1 t‖^2 := by
  rw [source_actual_fourdyad_L2_bochner_finset
    small long R a b T alpha bs bp d chi sigma0 sigma1
    S K freq hK hFreq]
  have hToLp :
      (∑ z ∈ sourceActualFourDyadTuples small long R a b,
        (∫ ξ in S, K ξ * sourcePhase (sourceActualFourDyadProduct z) (freq ξ)) •
          sourceActualFourDyadTermL2 T alpha bs bp d chi sigma0 sigma1 z) =
      (ContinuousMap.toLp 2
        (Measure.comap Subtype.val volume : Measure (Set.Icc (-T) T)) ℂ)
        (sourceActualFourDyadSumOnIcc small long R a b T
          (fun w => ∫ ξ in S, K ξ * sourcePhase w (freq ξ))
          alpha bs bp d chi sigma0 sigma1) := by
    unfold sourceActualFourDyadTermL2 sourceActualFourDyadSumOnIcc
    simp only [map_sum, map_smul]
  rw [hToLp]
  exact source_actual_fourdyad_cutoff_L2_norm_sq_setIntegral
    small long R a b T _ alpha bs bp d chi sigma0 sigma1
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadEnergySplit -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- Exact scalar energy splitting for the literal four-dyad cutoff. -/
theorem source_actual_fourdyad_energy_split
    (small long R : Finset ℕ) (a b : ℕ) (T : ℝ)
    (cutoff cutoff2 alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    (∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
      small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t‖^2) ≤
    2*(∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
      small long R a b cutoff2 alpha bs bp d chi sigma0 sigma1 t‖^2) +
    2*(∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
      small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t -
      sourceActualSmoothFourDyadAt small long R a b cutoff2
        alpha bs bp d chi sigma0 sigma1 t‖^2) := by
  let mu : Measure (Set.Icc (-T) T) := Measure.comap Subtype.val volume
  let F := sourceActualFourDyadSumOnIcc small long R a b T cutoff alpha bs bp d chi sigma0 sigma1
  let G := sourceActualFourDyadSumOnIcc small long R a b T cutoff2 alpha bs bp d chi sigma0 sigma1
  let V := (ContinuousMap.toLp 2 mu ℂ) F
  let W := (ContinuousMap.toLp 2 mu ℂ) G
  have hF : ‖V‖^2 = ∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
      small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t‖^2 :=
    source_actual_fourdyad_cutoff_L2_norm_sq_setIntegral small long R a b T
      cutoff alpha bs bp d chi sigma0 sigma1
  have hG : ‖W‖^2 = ∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
      small long R a b cutoff2 alpha bs bp d chi sigma0 sigma1 t‖^2 :=
    source_actual_fourdyad_cutoff_L2_norm_sq_setIntegral small long R a b T
      cutoff2 alpha bs bp d chi sigma0 sigma1
  have hVec : V-W = (ContinuousMap.toLp 2 mu ℂ) (F-G) := by rw [map_sub]
  have hDiff : ‖V-W‖^2 = ∫ t in Set.Icc (-T) T,
      ‖sourceActualSmoothFourDyadAt small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t -
        sourceActualSmoothFourDyadAt small long R a b cutoff2 alpha bs bp d chi sigma0 sigma1 t‖^2 := by
    rw [hVec,source_continuous_toLp_norm_sq]
    have hPoint (t : Set.Icc (-T) T) : (F-G) t =
        sourceActualSmoothFourDyadAt small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t.1 -
        sourceActualSmoothFourDyadAt small long R a b cutoff2 alpha bs bp d chi sigma0 sigma1 t.1 := by
      simp [F,G,sourceActualFourDyadSumOnIcc,sourceActualSmoothFourDyadAt,sourceActualFourDyadTermOnIcc]
    simp_rw [hPoint]
    exact integral_subtype_comap
      (measurableSet_Icc : MeasurableSet (Set.Icc (-T) T))
      (fun t : ℝ => ‖sourceActualSmoothFourDyadAt small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t -
        sourceActualSmoothFourDyadAt small long R a b cutoff2 alpha bs bp d chi sigma0 sigma1 t‖^2)
  rw [←hF,←hG,←hDiff]
  have ht : ‖V‖ ≤ ‖W‖+‖V-W‖ := by simpa using norm_add_le W (V-W)
  nlinarith [norm_nonneg V,norm_nonneg W,norm_nonneg (V-W),sq_nonneg (‖W‖-‖V-W‖)]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceElementaryEulerLower -/

section

open scoped BigOperators
namespace Green64Analytic.SourceBlockSieve
/-- Exactly the source finite natural-prime Euler product, including 2. -/
noncomputable def sourceNaturalEuler (W : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (W+1)).filter Nat.Prime, (1-(p:ℝ)⁻¹)

theorem source_natural_euler_succ (W : ℕ) :
    sourceNaturalEuler (W+1) = sourceNaturalEuler W *
      (if Nat.Prime (W+1) then 1-((W+1:ℕ):ℝ)⁻¹ else 1) := by
  classical
  unfold sourceNaturalEuler
  simp only [Finset.prod_filter]
  rw [Finset.prod_range_succ]

theorem source_natural_euler_mul_floor (n : ℕ) :
    1 ≤ ((n+1:ℕ):ℝ)*sourceNaturalEuler (n+1) := by
  induction n with
  | zero =>
    have he : (Finset.range 2).filter Nat.Prime = ∅ := by
      ext p
      constructor
      · intro hp
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        have hge := (Finset.mem_filter.mp hp).2.two_le
        omega
      · intro hp
        simp at hp
    norm_num [sourceNaturalEuler, he]
  | succ n ih =>
    rw [source_natural_euler_succ (n+1)]
    by_cases hp : Nat.Prime (n+1+1)
    · rw [ite_eq_left hp]
      have hn : ((n+1+1:ℕ):ℝ) ≠ 0 := by positivity
      have heq : ((n+1+1:ℕ):ℝ) *
          (sourceNaturalEuler (n+1)*(1-((n+1+1:ℕ):ℝ)⁻¹)) =
          ((n+1:ℕ):ℝ)*sourceNaturalEuler (n+1) := by
        push_cast
        field_simp
        ring
      rw [heq]
      exact ih
    · rw [ite_eq_right hp, mul_one]
      have hn : 0 < ((n+1:ℕ):ℝ) := by positivity
      have hv : 0 ≤ sourceNaturalEuler (n+1) := by nlinarith
      push_cast at ih ⊢
      nlinarith

theorem source_natural_euler_lower (W : ℕ) (hW : 1 ≤ W) :
    (W:ℝ)⁻¹ ≤ sourceNaturalEuler W := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : W ≠ 0)
  have h := source_natural_euler_mul_floor n
  have hn : 0 < ((n+1:ℕ):ℝ) := by positivity
  rw [← one_div]
  exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using h)
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceFactorialFiberEnergy -/

section

/-!
Source `sh:factorial-norm`: first, a fully kernel-proved energy bound for
collapsing a finite ordered tuple polynomial along a bounded-to-one product map.
The prime unique-factorization and factorial-fiber specialization is separate.
-/

namespace Green64Analytic.CorrelationMellin

variable {α β : Type*} [DecidableEq β]

theorem collapsed_fiber_square_bound
    (s : Finset α) (index : α → β) (a : α → ℂ) (B : ℝ)
    (hfiber : ∀ y ∈ s.image index,
      ((s.filter (fun x => index x = y)).card : ℝ) ≤ B) :
    ∑ y ∈ s.image index,
        ‖∑ x ∈ s.filter (fun x => index x = y), a x‖ ^ 2
      ≤ B * ∑ x ∈ s, ‖a x‖ ^ 2 := by
  classical
  have hpoint (y : β) (hy : y ∈ s.image index) :
      ‖∑ x ∈ s.filter (fun x => index x = y), a x‖ ^ 2 ≤
        B * ∑ x ∈ s.filter (fun x => index x = y), ‖a x‖ ^ 2 := by
    calc
      _ ≤ (∑ x ∈ s.filter (fun x => index x = y), ‖a x‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ ((s.filter (fun x => index x = y)).card : ℝ) *
            ∑ x ∈ s.filter (fun x => index x = y), ‖a x‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ B * ∑ x ∈ s.filter (fun x => index x = y), ‖a x‖ ^ 2 := by
        gcongr
        exact hfiber y hy
  have hfiber_partition :
      (∑ y ∈ s.image index, ∑ x ∈ s.filter (fun x => index x = y), ‖a x‖ ^ 2) =
        ∑ x ∈ s, ‖a x‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : index x ∈ s.image index := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    simp [Finset.sum_ite_eq, hxi]
  calc
    _ ≤ ∑ y ∈ s.image index,
        B * ∑ x ∈ s.filter (fun x => index x = y), ‖a x‖ ^ 2 := by
          exact Finset.sum_le_sum (fun y hy => hpoint y hy)
    _ = B * ∑ x ∈ s, ‖a x‖ ^ 2 := by
      rw [← Finset.mul_sum, hfiber_partition]

/-- Exact grouping of finite complex coefficients by their product index. -/
theorem collapsed_fiber_sum_eq
    (s : Finset α) (index : α → β) (a : α → ℂ) :
    (∑ y ∈ s.image index,
      ∑ x ∈ s.filter (fun x => index x = y), a x) = ∑ x ∈ s, a x := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hxi : index x ∈ s.image index :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  simp [Finset.sum_ite_eq, hxi]

end Green64Analytic.CorrelationMellin

end

