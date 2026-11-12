module

public import Green64.Library.Weights.B26RawCommonHistory

@[expose] public section

/-!
# Weights / B26RawCoherentKernel

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26RawCoherentKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Perm" => BigGroupPerm (BG := G) (J+ell)
local notation "Nu" => SourceOriginalProbePattern434 G m

/-- Actual fresh-copy law with both physical birth gates. -/
def sourceOriginalB26RawPatternWeight434 (nu : Nu)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm) (S : Finset ℕ) : ℂ :=
  if Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t) ∧
      sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val) J ell m hmJ nu tau t
  then sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau else 0

/-- All four actual endpoint signs, followed by the original RAW sign. -/
def sourceOriginalB26RawPatternSign434 (nsmall : ℕ) (nu : Nu) (epsSrc epsTgt : Bool) : ℂ :=
  sourceOriginalB26NumericSharedSign434 nsmall J ell m hmJ nu epsSrc epsTgt *
    (-((-1:ℂ)^(nu.1.card+nu.2.card)))

/-- Coherent coefficient of the one common RAW continuation.
There is no absolute value, pattern resampling, or history resampling. -/
def sourceOriginalB26RawCoherentCoefficient434
    (blockA blockB : Finset G) (nsmall : ℕ) (epsSrc epsTgt : Bool)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm) (S : Finset ℕ) : ℂ :=
  ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
    sourceOriginalB26RawPatternSign434 J ell m hmJ nsmall nu epsSrc epsTgt *
      sourceOriginalB26RawPatternWeight434 P J ell m hmJ nu mu s t sigma tau S

theorem source_original_B26_RAW_pattern_sign_unit434
    (nsmall : ℕ) (nu : Nu) (epsSrc epsTgt : Bool) :
    ‖sourceOriginalB26RawPatternSign434 J ell m hmJ nsmall nu epsSrc epsTgt‖=1 := by
  unfold sourceOriginalB26RawPatternSign434 sourceOriginalB26NumericSharedSign434
  split_ifs <;> simp [norm_mul]

/-- The scalar RAW sign is real, so both original orientations extract
the same sign. This does not assert an endpoint transpose identity. -/
theorem source_original_B26_RAW_scalar_sign434
    (n : ℕ) (zeta theta : ℝ) (D : ℕ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    originalEdgeScalar (-((-1:ℂ)^n)) zeta theta D o k =
      (-((-1:ℂ)^n))*originalEdgeScalar 1 zeta theta D o k := by
  rcases ho with rfl | rfl
  · simp only [source_original_edge_scalar_positive_fourier434,one_mul]
  · rw [source_original_edge_scalar_negative_conjugate434,
      source_original_edge_scalar_negative_conjugate434]
    simp only [source_original_edge_scalar_positive_fourier434,one_mul,
      star_mul,star_neg,star_pow,star_one]
    ring

private theorem weight_live
    (nu : Nu) (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm) (S : Finset ℕ)
    (h : sourceOriginalB26RawPatternWeight434 P J ell m hmJ nu mu s t sigma tau S ≠ 0) :
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0 ∧
      Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t) := by
  unfold sourceOriginalB26RawPatternWeight434 at h
  split_ifs at h with hg
  · exact ⟨h,hg.1⟩
  · exact False.elim (h rfl)

/-- Exact uniqueness on the actual gated kernel, including numerical Nodup. -/
theorem source_original_B26_RAW_weight_support_unique434
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm) (S : Finset ℕ)
    (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (nu eta : Nu) (hn : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (he : eta ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hwn : sourceOriginalB26RawPatternWeight434 P J ell m hmJ nu mu s t sigma tau S ≠ 0)
    (hwe : sourceOriginalB26RawPatternWeight434 P J ell m hmJ eta mu s t sigma tau S ≠ 0) :
    nu=eta := by
  have hn' := weight_live P J ell m hmJ nu mu s t sigma tau S hwn
  have he' := weight_live P J ell m hmJ eta mu s t sigma tau S hwe
  exact source_original_B26_RAW_live_pattern_unique434 P J ell m hmJ
    blockA blockB hBlocks nu eta hn he mu s t sigma tau S hS hn'.1 he'.1 hn'.2 he'.2

/-- Exact diagonal-in-pattern kernel square, for any joint complex
continuation value Z. No pattern-cardinality factor or bound on Z occurs.
The sum over different target endpoints has NOT been squared here. -/
theorem source_original_B26_RAW_coherent_kernel_square434
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (nsmall : ℕ) (epsSrc epsTgt : Bool)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm) (S : Finset ℕ)
    (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S) (Z : ℂ) :
    ‖sourceOriginalB26RawCoherentCoefficient434 P J ell m hmJ blockA blockB
      nsmall epsSrc epsTgt mu s t sigma tau S * Z‖^2 =
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalB26RawPatternWeight434 P J ell m hmJ nu mu s t sigma tau S * Z‖^2 := by
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let w := fun nu : Nu => sourceOriginalB26RawPatternWeight434 P J ell m hmJ nu mu s t sigma tau S
  let sign := fun nu : Nu => sourceOriginalB26RawPatternSign434 J ell m hmJ nsmall nu epsSrc epsTgt
  change ‖(∑ nu ∈ family,sign nu*w nu)*Z‖^2 = ∑ nu ∈ family,‖w nu*Z‖^2
  by_cases hex : ∃ nu ∈ family,w nu ≠ 0
  · obtain ⟨nu,hnu,hwn⟩ := hex
    have hz (eta : Nu) (he : eta ∈ family) (hne : eta ≠ nu) : w eta=0 := by
      by_contra hw
      exact hne (source_original_B26_RAW_weight_support_unique434 P J ell m hmJ
        blockA blockB hBlocks mu s t sigma tau S hS eta nu he hnu hw hwn)
    rw [Finset.sum_eq_single nu (fun eta he hne => by rw [hz eta he hne,mul_zero])
        (fun h => False.elim (h hnu)),
      Finset.sum_eq_single nu (fun eta he hne => by simp only [hz eta he hne,zero_mul,norm_zero,zero_pow (by omega : 2 ≠ 0)])
        (fun h => False.elim (h hnu))]
    rw [mul_assoc,norm_mul,source_original_B26_RAW_pattern_sign_unit434,one_mul]
  · have hz (nu : Nu) (hnu : nu ∈ family) : w nu=0 := by
      by_contra hn
      exact hex ⟨nu,hnu,hn⟩
    have h1 : (∑ nu ∈ family,sign nu*w nu)=0 :=
      Finset.sum_eq_zero (fun nu hnu => by rw [hz nu hnu,mul_zero])
    have h2 : (∑ nu ∈ family,‖w nu*Z‖^2)=0 :=
      Finset.sum_eq_zero (fun nu hnu => by simp only [hz nu hnu,zero_mul,norm_zero,zero_pow (by omega : 2 ≠ 0)])
    rw [h1,h2]
    simp

/-- Literal coherent RAW row after extracting the common true divisor
and the common numerical history. F is an arbitrary joint continuation;
it may include the original SMALL kernel and every OLD residue shift. -/
theorem source_original_B26_RAW_coherent_row434
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (nsmall : ℕ) (epsSrc epsTgt : Bool)
    (mu : (g : G) → BP g → ℝ) (s : A) (sigma tau : Perm) (S : Finset ℕ)
    (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (F : A → ℕ → Finset ℕ → ℂ) :
    (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 nsmall J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
        (if Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t) ∧
          sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val) J ell m hmJ nu tau t then
          originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
            (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau) o k *
          F t (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau)
            (S ∪ sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t)
         else 0)) =
    ∑ t : A,sourceOriginalB26RawCoherentCoefficient434 P J ell m hmJ blockA blockB
      nsmall epsSrc epsTgt mu s t sigma tau S *
      (originalEdgeScalar 1 zeta theta
        (sourceOriginalB26RawCommonDivisor434 P blockA J ell dsmall s t sigma tau) o k *
        F t (sourceOriginalB26RawCommonDivisor434 P blockA J ell dsmall s t sigma tau)
          (S ∪ sourceOriginalB26RawInventory434 P J ell t)) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  unfold sourceOriginalB26RawCoherentCoefficient434
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro nu hnu
  unfold sourceOriginalB26RawPatternWeight434 sourceOriginalB26RawPatternSign434
  by_cases hg : Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t) ∧
      sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val) J ell m hmJ nu tau t
  · simp only [if_pos hg]
    by_cases hz : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau = 0
    · simp only [hz,zero_mul,mul_zero]
    · rw [source_original_B26_RAW_common_divisor434 P blockA blockB hBlocks
        J ell m hmJ nu hnu dsmall mu s t sigma tau hz,
        source_original_B26_RAW_common_seen434 P J ell m hmJ nu
          mu s t sigma tau S hS hz,
        source_original_B26_RAW_scalar_sign434 _ zeta theta _ o k ho]
      ring
  · simp only [if_neg hg,mul_zero,zero_mul]

end Green64Analytic.CorrelationSquare

end

end

