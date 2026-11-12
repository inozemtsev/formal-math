module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology ContDiff

lemma cuspSeed_row_defect (a b : ℝ) (s c : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => c*cuspSeedProfile a b s (rowHeight u q)) p-
      s*(s-2)*(c*cuspSeedProfile a b s (rowHeight u p))=
        c*cuspSeedDefectProfile a b s (rowHeight u p) := by
  rw [axisLaplacian_const_mul,rowProfile_laplacian _ (cuspSeedProfile_contDiffAt a b s) u hu p hp]
  have h := cuspSeedProfile_laplace_defect a b s (rowHeight u p) (rowHeight_pos u hu p hp).ne'
  linear_combination c*h

theorem heightPoincare_cuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (heightPoincareField (cuspSeedProfile a b s)) p-
      s*(s-2)*heightPoincareField (cuspSeedProfile a b s) p=
        heightPoincareField (cuspSeedDefectProfile a b s) p := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  let f : CuspCosets → SpatialCoordinates → ℂ :=
    fun r q => (cosetCharacter r)⁻¹*cuspSeedProfile a b s (rowHeight (embeddedRow r) q)
  have heq : heightPoincareField (cuspSeedProfile a b s) =ᶠ[𝓝 p] (fun q => ∑r∈S,f r q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedProfile_zero a b s _ hab (le_trans ((hrows q hq).2 r hr).le ha.le),mul_zero]
  have hD : heightPoincareField (cuspSeedDefectProfile a b s) p=
      ∑r∈S,(cosetCharacter r)⁻¹*cuspSeedDefectProfile a b s (rowHeight (embeddedRow r) p) := by
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedDefectProfile_zero a b s _ hab (Or.inl (((hrows p hpU).2 r hr).trans ha)),mul_zero]
  have hreg : ∀r∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f r) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f r) q j)) (q j) := by
    intro r hr q hq j
    have hc : ∀v,0<v→ ContDiffAt ℝ ∞ (fun v => (cosetCharacter r)⁻¹*cuspSeedProfile a b s v) v :=
      fun v hv => contDiffAt_const.mul (cuspSeedProfile_contDiffAt a b s v hv)
    have h := rowProfile_axis_derivatives _ hc (embeddedRow r) (embeddedRow_ne_zero r) q hq j
    exact ⟨h.1.differentiableAt,h.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p heq,axisLaplacian_finset_sum S f hreg p hp,
    heq.eq_of_nhds,hD,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact cuspSeed_row_defect a b s (cosetCharacter r)⁻¹ (embeddedRow r) (embeddedRow_ne_zero r) p hp

def smoothCuspSeedField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeed a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

def smoothCuspSeedDefectField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeedDefect a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

lemma smoothCuspSeedField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedField a b s p=heightPoincareField (cuspSeedProfile a b s) p := by
  rw [smoothCuspSeedField,dite_eq_left hp,smoothCuspSeed_coordinate a b s ha hab p hp]
lemma smoothCuspSeedDefectField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefectField a b s p=heightPoincareField (cuspSeedDefectProfile a b s) p := by
  rw [smoothCuspSeedDefectField,dite_eq_left hp,smoothCuspSeedDefect_coordinate a b s ha hab p hp]

lemma actual_smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothCuspSeedField a b s) p := by
  have heq : smoothCuspSeedField a b s =ᶠ[𝓝 p] heightPoincareField (cuspSeedProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedField_eq a b s ha hab q hq
  exact (smoothCuspSeed_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

theorem actual_smoothCuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothCuspSeedField a b s) p-s*(s-2)*smoothCuspSeedField a b s p=
      smoothCuspSeedDefectField a b s p := by
  rw [axisLaplacian_congr_positive _ _ (fun q hq => smoothCuspSeedField_eq a b s ha hab q hq) p hp,
    smoothCuspSeedField_eq a b s ha hab p hp,smoothCuspSeedDefectField_eq a b s ha hab p hp]
  exact heightPoincare_cuspSeed_laplace_defect a b s ha hab p hp

lemma cuspSeedProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedProfile a b s v) := by
  unfold cuspSeedProfile positiveHeightPower logRatioPower
  fun_prop
lemma cuspSeedDefectProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedDefectProfile a b s v) := by
  unfold cuspSeedDefectProfile positiveHeightPower logRatioPower
  fun_prop

lemma cuspCutoffCorrection_parameter_entire (F : ℂ → ℝ → ℂ)
    (hF : ∀v,Differentiable ℂ (fun s => F s v)) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => cuspCutoffCorrection 1 (F s) w) := by
  let S := (high_cosets_finite 1 le_rfl w).toFinset
  have heq : (fun s => cuspCutoffCorrection 1 (F s) w)=
      (fun s => ∑r∈S,cuspCutoffTerm 1 (F s) r w) := by
    funext s
    apply tsum_eq_sum
    intro r hr
    have hh : ¬1<cosetHeight r w := by simpa only [S,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hr
    simp [cuspCutoffTerm,hh]
  rw [heq]
  apply Differentiable.fun_sum
  intro r hr
  unfold cuspCutoffTerm
  split_ifs
  · exact (differentiable_const _).mul (hF _)
  · exact differentiable_const _

theorem smoothCuspSeed_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeed a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedProfile_entire a b) w

theorem smoothCuspSeedDefect_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeedDefect a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedDefectProfile_entire a b) w

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sectorBadIdeal (E : fixedBadPrimes.powerset) : Ideal O := ∏ P ∈ E.val, P

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

theorem sectorBadIdeal_ne_zero_of_row (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) : sectorBadIdeal E ≠ 0 := by
  intro hz
  have hp := sector_bad_good_product I hI E hE
  rw [hz, zero_mul] at hp
  exact hI.ne_zero hp.symm

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPairTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (a j) * b k * unrestrictedPairCharacter (left j) (right k) (rows i) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedPairTerm_sector (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (i : m) (j : n) (k : p) :
    unrestrictedPairTerm rows left right a b i j k =
      originalTerm (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) 1 1 i j k := by
  classical
  by_cases hc : IsCoprime (left j) (right k)
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_true, one_dvd]
    have hp := unrestrictedPairCharacter_squarefree_bad_split (left j) (right k) (rows i)
      (hleft j) (hright k) (hray j k) (hrows i)
    have hs : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    rw [hp, hs]
    simp only [sectorBadIdeal, unrestrictedPairCharacter, star_mul,
      canonical_quadraticRow_star _ (hleft j)]
    ring
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_false]

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E)
    (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          (M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (sectorBadIdeal E) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (sectorBadIdeal E) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i) : ℝ) =
      (Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ) := by
    calc
      (Ideal.absNorm (rows i) : ℝ) =
          (Ideal.absNorm (sectorBadIdeal E * goodSquarefreePart (rows i)) : ℝ) :=
        congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
          (sector_bad_good_product (rows i) (hrows i) E (hE i)).symm
      _ = _ := by rw [map_mul, Nat.cast_mul]
  rw [hn]
  have harg : F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * ((Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ))) =
    F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ)) *
        ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  gcongr

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i) : ℝ) = Q * (Ideal.absNorm (good i) : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B / Q) / 2 ≤ (Ideal.absNorm (good i) : ℝ) ∧
        (Ideal.absNorm (good i) : ℝ) ≤ B / Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B / Q / 2 = (B / 2) / Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B / Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i) : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.unrestricted_dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      4 * dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ E : fixedBadPrimes.powerset,
        unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale := by
    unfold unrestrictedDualTruncatedMiddle
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ ≤
        dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
    apply hexp.dual_truncated_middle_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right
      (fun i k h => Subtype.ext (hr h)) hl hri (fun i => hrows i.val) a b W
      (fun i => Y i.val) (fun i => Z i.val) lengthScale hleft hright hray (fun i => hZ i.val) E
    exact fun i => i.property
  rw [hs]
  calc
    _ ≤ ∑ E : fixedBadPrimes.powerset,
        ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ _E : fixedBadPrimes.powerset, dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
        fixedBadPrimes_powerset_card]
      norm_num

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_fixed_mask (Ψ : O →* ℂ) (m g f y : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*g) f y H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondChildColumn p hp hcop hg Ψ m f y H U := by
  simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg U m g]
  ring

theorem fixedChildRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F A : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg (F\A) Ψ m H f y =
      fixedChildRow p hp hcop hg F Ψ (m*∏ i ∈ A,p i) H f y := by
  unfold fixedChildRow
  rw [sum_remove_common_pool p hg hinj F A]
  apply Finset.sum_congr rfl
  intro U hU
  exact (secondChildColumn_fixed_mask p hp hcop hg Ψ m _ f y H U).symm

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem childEnergy_fixed_pool (F A : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X : ℝ) (negative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hp hcop hg (F\A) Ψ m T V X negative rowNegative a b =
      childEnergy p hp hcop hg F Ψ (m*∏ i ∈ A,p i) T V X negative rowNegative a b := by
  simp only [childEnergy,idealChildRow,fixedChildRow_fixed_pool p hp hcop hg hinj]

theorem childGeometricMean_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : JointLogSeparation.Frequency) :
    childGeometricMean p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q =
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ q := by
  simp only [childGeometricMean,childEnergy_fixed_pool p hp hcop hg hinj]

theorem densityChildEnergy_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) :
    densityChildEnergy p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J =
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ J := by
  simp only [densityChildEnergy,childGeometricMean_fixed_pool p hp hcop hg hinj]

end

open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProductNorm)

theorem restored_child_mask_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (m b0 : O) (R A : Finset ι) :
    ‖eisEmbedding ((m*b0*primeSubsetGenerator (fun i => Ideal.span {p i}) R)*∏ i ∈ A,p i)‖^2 =
      ‖eisEmbedding m‖^2*‖eisEmbedding b0‖^2*primeProductNorm p R*primeProductNorm p A := by
  simp only [map_mul,norm_mul,mul_pow,SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm]

end SecondPassIntegration

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma element_norm_le_of_dvd {a b : O} (hb : b ≠ 0) (h : a ∣ b) :
    ‖eisEmbedding a‖^2 ≤ ‖eisEmbedding b‖^2 := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [map_mul, norm_mul, mul_pow]
  exact le_mul_of_one_le_right (sq_nonneg _) (element_norm_ge_one c hc)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma squarefreeLabel_active_bound (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖eisEmbedding (squarefreeLabel p B v)‖^2 ≤ primeProductNorm p (cubeActiveSupport B v ε₁ ε₂) := by
  let S := B.filter (fun i => parity (v i))
  have he : squarefreeLabel p B v = ∏ i ∈ S, p i := by
    unfold squarefreeLabel primeProduct S
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : parity (v i) <;> simp [bit,hb]
  have hsub : S ⊆ cubeActiveSupport B v ε₁ ε₂ := by
    intro i hi
    obtain ⟨hi,hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi,?_⟩
    change parity (v i) = true at hpi
    rw [hpi]
    cases h1 : ε₁ i <;> cases h2 : ε₂ i <;> decide
  rw [he]
  exact primeProductNorm_mono p hp hsub

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma jLabel_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [← primeProduct_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  dsimp only
  unfold bit
  split <;> have h := hv i hi <;> omega

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_square_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ^ 2 ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_jLabel_square (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)^2 =
      primeProduct p B v₁ * primeProduct p B v₂ * squarefreeLabel p B (fun i => v₁ i+v₂ i) := by
  rw [FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2,
    FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  ring

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cube_label_norm_bounds (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hb₁ : ‖eisEmbedding (primeProduct p B v₁)‖^2 ≤ B₀)
    (hb₂ : ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀) :
    let v := fun i => v₁ i+v₂ i
    ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 ≤ B₀^2 ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤ B₀ ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤
      B₀*‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂,p i)‖ /
        ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 := by
  dsimp only
  have hbb : ‖eisEmbedding (primeProduct p B v₁ * primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    rw [map_mul,norm_mul,mul_pow]
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hbb0 := mul_ne_zero (primeProduct_ne_zero p hp B v₁) (primeProduct_ne_zero p hp B v₂)
  have hJ := (element_norm_le_of_dvd hbb0 (jLabel_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  have hb0sq := (element_norm_le_of_dvd hbb0 (b0_square_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  simp only [map_pow,norm_pow] at hb0sq
  have hb0 : ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤ B₀ := by
    nlinarith [sq_nonneg ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖]
  refine ⟨hJ,hb0,?_⟩
  have heq := congrArg (fun a : O => ‖eisEmbedding a‖^2) (b0_jLabel_square p B v₁ v₂ ε₁ ε₂ hv)
  simp only [map_pow,map_mul,norm_pow,norm_mul,mul_pow] at heq
  have hs := squarefreeLabel_active_bound p hp B (fun i => v₁ i+v₂ i) ε₁ ε₂
  have hNprod : ‖eisEmbedding (primeProduct p B v₁)‖^2 * ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    simpa only [map_mul,norm_mul,mul_pow] using hbb
  have hmul := mul_le_mul hNprod hs (sq_nonneg _) (sq_nonneg B₀)
  change _ ≤ B₀^2*‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2 at hmul
  have hjpos : 0 < ‖eisEmbedding (jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 := by
    exact zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp B _))
  apply (le_div_iff₀ hjpos).mpr
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg _))).mp
  simp only [mul_pow]
  exact heq.trans_le hmul

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

theorem primeIdealProduct_exponents_eq
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : (∏ i ∈ B, P i ^ v i) = ∏ i ∈ C, P i ^ w i) : v = w := by
  funext i
  have he := congrArg (fun I => emultiplicity (P i) I) heq
  rw [primeIdealProduct_emultiplicity P hinj,primeIdealProduct_emultiplicity P hinj] at he
  have hB : (if i ∈ B then (v i : ℕ∞) else 0) = (v i : ℕ∞) := by
    by_cases h : i ∈ B <;> simp [h,hv i]
  have hC : (if i ∈ C then (w i : ℕ∞) else 0) = (w i : ℕ∞) := by
    by_cases h : i ∈ C <;> simp [h,hw i]
  rw [hB,hC] at he
  exact_mod_cast he

end

theorem primeProduct_span_exponents_eq {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : Ideal.span {FirstPassCubeLabels.primeProduct p B v} =
      Ideal.span {FirstPassCubeLabels.primeProduct p C w}) : v = w := by
  apply primeIdealProduct_exponents_eq (fun i => Ideal.span {p i}) hinj B C v w hv hw
  simpa only [FirstPassCubeLabels.primeProduct,FiniteGaussPhase.span_finset_prod,
    ←Ideal.span_singleton_pow] using heq

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem divisor_dyadic_sum_le (S T : Finset (Ideal O)) (N : ℝ)
    (f : Ideal O → Ideal O → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k : Fin (columnDyadicLength N + 1),
      (divisorDyadicBin S N j).Nonempty → (divisorDyadicBin T N k).Nonempty →
      (∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E) ≤ C) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) ≤ ((columnDyadicLength N + 1 : ℕ) : ℝ)^2 * C := by
  rw [sum_divisorDyadicRectangles S T N f]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases hS : (divisorDyadicBin S N j).Nonempty
      · by_cases hT : (divisorDyadicBin T N k).Nonempty
        · exact hb j k hS hT
        · simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, Finset.sum_const_zero] using hC
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def largePrincipalWindow (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ)*(Ideal.absNorm E : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalWindow_le (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) :
    largePrincipalWindow S T rows left right a b M P ≤
      principalCorrectionAt S T rows left right a b M := by
  classical
  unfold principalCorrectionAt
  rw [sum_two_subtype_pools S T (fun D E => ∑ i,
    (Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)))*
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)]
  unfold largePrincipalWindow
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

theorem HasSieveExponent.large_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M V : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hV : 0 ≤ V) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (V+Real.sqrt M*B^(α-1/2)) := by
  classical
  by_cases hc : Real.sqrt (M/B)*N ≤ V*(D₁*D₂)
  · exact (largePrincipalWindow_le S T rows left right a b M P).trans
      (HasSieveExponent.large_principal_correction ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
        rows left right hr hl hri hrows hleft hright a b hexp deltaLoss hδ hD₁N hD₂N V hc)
  · have hz : largePrincipalWindow S T rows left right a b M P = 0 := by
      unfold largePrincipalWindow
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        have hlo := hP D hD E hE i hp
        have hhi : (Ideal.absNorm (D*E):ℝ) ≤ 4*(D₁*D₂) := by
          rw [map_mul, Nat.cast_mul]
          calc
            _ ≤ (2*D₁)*(2*D₂) := mul_le_mul (hS D hD).2 (hT E hE).2 (by positivity) (by linarith)
            _ = _ := by ring
        nlinarith
      simp only [hn, ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.large_principal_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  classical
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.large_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M V
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hV
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P
      (fun D hD E hE i hp => hP D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem finite_principal_triangle
    {m n p D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d‖ ≤
      ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d) =
      ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalDivisorCorrection (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

def largePrincipalProductAt (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalProductAt_le_window (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    largePrincipalProductAt K rows left right a b M P ≤
      largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P
    (fun d i _ _ => ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ))
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  unfold largePrincipalWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : D*E ∈ K
  · by_cases hi : P (D*E) i
    · simp only [hd, hi, and_self, ite_true, map_mul, Nat.cast_mul]
      simp only [←Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/
          ((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)) by positivity)]
      ring
    · simp only [hd, hi, and_false, ite_true, ite_false]
  · simp only [hd, false_and, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma principalDivisorCorrection_le_product (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hK : ∀ j k d, d ∣ left j*right k → d ∈ K) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      largePrincipalProductAt K rows left right a b M P := by
  classical
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d.val:ℝ):ℝ):ℂ) else 0 else 0
  have he : principalDivisorCorrection rows left right a b M P =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ)*A i j k d := by
    unfold principalDivisorCorrection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  unfold largePrincipalProductAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then
    if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.principal_divisor_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
      (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure CubeCoordinates (ι : Type*) where
  leftExponent : ι →₀ ℕ
  rightExponent : ι →₀ ℕ
  leftDivisor : Finset ι
  rightDivisor : Finset ι

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

def support (x : CubeCoordinates ι) : Finset ι :=
  x.leftExponent.support ∪ x.rightExponent.support

def leftBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.leftDivisor)
def rightBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.rightDivisor)

def Admissible (x : CubeCoordinates ι) : Prop :=
  x.leftDivisor ⊆ x.support ∧ x.rightDivisor ⊆ x.support

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

theorem left_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.leftExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))

theorem right_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.rightExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))

theorem aLabel_left (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]

end CubeCoordinates

@[ext] structure GlobalSecondData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
  source : SecondExpansionData ι

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def globalSecondTuple (x : GlobalSecondData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source.frequency

def globalSecondFixedTriple (x : GlobalSecondData ι) : Ideal O × Ideal O × Ideal O :=
  (Ideal.span {(b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)},
   ∏ i ∈ x.firstCommon,Ideal.span {p i},
   ∏ i ∈ x.source.sourceCommon\x.source.divisor,Ideal.span {p i})

def GlobalSecondAdmissible (x : GlobalSecondData ι) : Prop :=
  x.cube.Admissible ∧ x.source.divisor ⊆ x.source.sourceCommon ∧
  Disjoint x.common x.cube.support ∧ x.firstDivisor ⊆ x.common∪x.cube.support

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondTuple_valid (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x) :
    SecondPassFiber.Valid (globalSecondTuple p x)
      (SecondPassFiber.newLabel (globalSecondTuple p x))
      (globalSecondFixedTriple p x).1
      (SecondPassFiber.newRow (globalSecondTuple p x)) :=
  actualSecondTuple_valid p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    hx.2.2.1 hx.2.2.2 x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos x.source.frequency

theorem globalSecondFixedTriple_nonzero (hp : ∀ i,p i ≠ 0) (x : GlobalSecondData ι) :
    (globalSecondFixedTriple p x).1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.2 ≠ ⊥ := by
  refine ⟨sector_b0_ne_bot p hp _ _ _ _ _,?_,?_⟩ <;>
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondFixedTriple_norm_bounds (hp : ∀ i,p i ≠ 0)
    (x : GlobalSecondData ι) (B H J T R : ℝ) (hB : 0 ≤ B) (hJ : 0 < J)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : primeProductNorm p x.firstCommon ≤ T)
    (hr : primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*H/J ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ T ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ R := by
  obtain ⟨_,_,hb0⟩ := cube_label_norm_bounds p hp x.cube.support
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos B hB hb₁ hb₂
  refine ⟨?_,?_,?_⟩
  · change (Ideal.absNorm (Ideal.span {_}) : ℝ) ≤ _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    apply hb0.trans
    exact div_le_div₀ (mul_nonneg hB ((norm_nonneg _).trans hactive))
      (mul_le_mul_of_nonneg_left hactive hB) hJ hlabel
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ ht
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ hr

theorem globalSecondFixedTriple_count (hp : ∀ i,p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (B H J T R : ℝ)
    (hB : 0 ≤ B) (hJ : 0 < J) (hscale : 1 ≤ B*H/J) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hb₁ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ∀ x∈s, ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : ∀ x∈s, J ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : ∀ x∈s, primeProductNorm p x.firstCommon ≤ T)
    (hr : ∀ x∈s, primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤ 128^3*(B*H/J)*T*R := by
  apply DescentFiberCost.fixed_triple_count _ _ _ _ hscale hT hR
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_nonzero p hp x
  · intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact globalSecondFixedTriple_norm_bounds p hp x B H J T R hB hJ
      (hb₁ x hx) (hb₂ x hx) (hactive x hx) (hlabel x hx) (ht x hx) (hr x hx)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalSecondFixedTriple {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x = ∑ q∈s.image (globalSecondFixedTriple p),
      ∑ x∈s with globalSecondFixedTriple p x=q,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) f

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem globalSecondTuple_cube_eq {x y : GlobalSecondData ι}
    (hx : x.cube.Admissible) (hy : y.cube.Admissible)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x.cube=y.cube := by
  have h₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 4) h
  have h₂ := congrArg SecondPassFiber.OldTuple.b2 h
  have hA₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 5) h
  have hA₂ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 6) h
  change Ideal.span {primeProduct p x.cube.support x.cube.leftExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.leftExponent} at h₁
  change Ideal.span {primeProduct p x.cube.support x.cube.rightExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.rightExponent} at h₂
  have hv₁ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.leftExponent y.cube.leftExponent x.cube.left_off y.cube.left_off h₁
  have hv₂ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.rightExponent y.cube.rightExponent x.cube.right_off y.cube.right_off h₂
  change Ideal.span {aLabel p x.cube.support x.cube.leftBit} =
    Ideal.span {aLabel p y.cube.support y.cube.leftBit} at hA₁
  change Ideal.span {aLabel p x.cube.support x.cube.rightBit} =
    Ideal.span {aLabel p y.cube.support y.cube.rightBit} at hA₂
  rw [CubeCoordinates.aLabel_left p x.cube hx,CubeCoordinates.aLabel_left p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₁
  rw [CubeCoordinates.aLabel_right p x.cube hx,CubeCoordinates.aLabel_right p y.cube hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA₂
  apply CubeCoordinates.ext
  · exact Finsupp.ext (congrFun hv₁)
  · exact Finsupp.ext (congrFun hv₂)
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₁
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hA₂

theorem globalSecondEncoding_injective {x y : GlobalSecondData ι}
    (hx : GlobalSecondAdmissible x) (hy : GlobalSecondAdmissible y)
    (ht : globalSecondFixedTriple p x=globalSecondFixedTriple p y)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x=y := by
  have hc := globalSecondTuple_cube_eq p hinj hx.1 hy.1 h
  have hA := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.1) ht
  have hR := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.2) ht
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  have hA' : x.firstCommon=y.firstCommon := FirstCauchyArithmetic.family_product_injective _ hinj hA
  have hC' : x.common=y.common := FirstCauchyArithmetic.family_product_injective _ hinj hC
  have hD' : x.firstDivisor=y.firstDivisor := FirstCauchyArithmetic.family_product_injective _ hinj hD
  have hE' : x.source.divisor=y.source.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hV' : x.source.overlap=y.source.overlap := FirstCauchyArithmetic.family_product_injective _ hinj hV
  have hR' : x.source.sourceCommon\x.source.divisor=y.source.sourceCommon\y.source.divisor :=
    FirstCauchyArithmetic.family_product_injective _ hinj hR
  have hG : x.source.sourceCommon=y.source.sourceCommon := by
    calc
      _ = x.source.divisor ∪ (x.source.sourceCommon\x.source.divisor) :=
        (Finset.union_sdiff_of_subset hx.2.1).symm
      _ = y.source.divisor ∪ (y.source.sourceCommon\y.source.divisor) := by rw [hR',hE']
      _ = _ := Finset.union_sdiff_of_subset hy.2.1
  exact GlobalSecondData.ext hc hA' hC' hD' (SecondExpansionData.ext hG hE' hV' hk)

theorem globalSecond_fiber_card (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (GlobalSecondData ι))
      (q : Ideal O × Ideal O × Ideal O) (f : Ideal O) (y : O),
      (∀ x∈s,GlobalSecondAdmissible x) → f ≠ ⊥ → q.1 ≠ ⊥ →
      (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,SecondPassFiber.newLabel (globalSecondTuple p x)=f) →
      (∀ x∈s,SecondPassFiber.newRow (globalSecondTuple p x)=y) →
      (s.card : ℝ) ≤ C*((Ideal.absNorm f : ℝ)*Ideal.absNorm q.1)^ε := by
  obtain ⟨C,hC,hbound⟩ := SecondPassFiber.valid_tuple_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s q f y hs hf hq htr hlabel hrow
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx z hz he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs z hz)
      ((htr x hx).trans (htr z hz).symm) he
  rw [← Finset.card_image_of_injOn hi]
  apply hbound _ f q.1 y hf hq
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hv := globalSecondTuple_valid p x (hs x hx)
  simpa only [htr x hx,hlabel x hx,hrow x hx] using hv

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem middleTruncation_coprime_common_mask
    (G C : Ideal O) (hG : Squarefree G) (hC : Squarefree C) (hGC : IsCoprime G C)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G * C} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        middleTruncation (fun P : primePool {C} => P.val) Finset.univ W
          (X / (Ideal.absNorm q : ℝ)) (Y / (Ideal.absNorm q : ℝ)) (Z / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hprod : Squarefree (G * C) := squarefree_mul_iff.mpr ⟨hGC.isRelPrime, hG, hC⟩
  rw [middleTruncation_eq_ideal_frequencies _ hprod]
  simp_rw [middleTruncation_eq_ideal_frequencies C hC]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := idealDivisors G) (t := rowNormDisk ⌊lengthScale⌋₊)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG.ne_zero hC.ne_zero hGC]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG.ne_zero).mp hq
  have hdC := (mem_idealDivisors hC.ne_zero).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
  have hNq : 0 < (Ideal.absNorm q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hqd := (hGC.mono hqG hdC).isRelPrime
  have hlow : Y < (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ↔
      Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) := by
    constructor
    · intro hy
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hy
    · intro hy
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hy
  have hhigh : (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ≤ Z ↔
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ) := by
    constructor
    · intro hz
      apply (le_div_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (le_div_iff₀ hNq).mp hz
  simp only [map_mul, Nat.cast_mul, hlow, hhigh, hqd.moebius_mul, Int.cast_mul]
  by_cases hp : Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) ∧
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ)
  · simp only [hp, and_self, ite_true]
    have harg : X * ‖eisEmbedding h‖ ^ 2 / ((Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ)) =
        (X / (Ideal.absNorm q : ℝ)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem sqrt_norm_divisor_scale (M B q : ℝ) (hM : 0 ≤ M) (_hB : 0 ≤ B) (hq : 0 < q) :
    Real.sqrt (M / B) / q = Real.sqrt ((M / q ^ 2) / B) := by
  rw [Real.sqrt_div hM, Real.sqrt_div (by positivity : 0 ≤ M / q ^ 2), Real.sqrt_div hM, Real.sqrt_sq hq.le]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMaskedTruncatedMiddle (G : Ideal O) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMaskedTruncatedMiddle_eq_divisors
    (G : Ideal O) (hG : Squarefree G) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k)) :
    originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
          (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hp (i : m) (j : n) (k : p) :
      originalTerm rows left right a b 1 1 i j k *
        middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        (originalTerm rows left right a b 1 1 i j k *
          middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
            (Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)))
            (Y i / (Ideal.absNorm q : ℝ)) (Z i / (Ideal.absNorm q : ℝ)) lengthScale) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j * right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
      rw [middleTruncation_coprime_common_mask G _ hG hsq ((hGl j).mul_right (hGr k)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqG := (mem_idealDivisors hG.ne_zero).mp hq
      have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
      have hNq : 0 < (Ideal.absNorm q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
      rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
      ring
    · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
      simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero]
  unfold originalMaskedTruncatedMiddle
  simp_rw [hp]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset m)) (t := idealDivisors G)]
  simp only [originalTruncatedMiddle, Finset.mul_sum]

theorem HasSieveExponent.original_masked_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (hG : Squarefree G)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k))
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))) := by
  let V := ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
        (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ ≤ V := by
    have hqG := (mem_idealDivisors hG.ne_zero).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
    have hq1 : (1 : ℝ) ≤ Ideal.absNorm q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : (0 : ℝ) < Ideal.absNorm q := by linarith
    have hZq (i : m) : Z i / (Ideal.absNorm q : ℝ) ≤
        U * Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)) := by
      calc
        _ ≤ (U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) / (Ideal.absNorm q : ℝ) :=
          div_le_div_of_nonneg_right (hZ i) hqpos.le
        _ = U * (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm q : ℝ)) := by ring
        _ = _ := by rw [sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
    have hb := hexp.original_truncated_middle deltaLoss hδ ε hε B N (M / (Ideal.absNorm q : ℝ) ^ 2) U
      hB hN (by positivity) hU rows left right hr hl hri hrows a b W
      (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale hleft hright hZq
    apply hb.trans
    dsimp only [V]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a b
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [originalMaskedTruncatedMiddle_eq_divisors G hG W rows left right a b M hM.le Y Z lengthScale
    (fun j => (hleft j).1) (fun k => (hright k).1) hGl hGr]
  calc
    _ ≤ ∑ q ∈ idealDivisors G,
        ‖(UniqueFactorizationMonoid.moebius q : ℂ) *
          originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
            (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticInitialBound.norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V]

end

open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

theorem HasSieveExponent.actual_principal_difference {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → Ideal O) (_hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      (∀ j k, columnRay (cols j) = columnRay (cols k)) →
      ∀ (a : n → ℂ) (G : Ideal O), Squarefree G →
      (∀ P ∈ fixedBadPrimes, P ∣ G) → ∀ (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * actualPrincipalDifference cols a G K‖ ≤
        ((idealDivisors G).card : ℝ)^2 * (supportConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hexp.reverse deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro n _ _ cols hinj M N K hM hN hK hcols hray a G hG hbad ε hε
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 < K := by linarith
  have hs := actualPrincipalDifference_bound cols hinj N (by linarith) hcols hray a G hG hbad K hK0 ε hε
  have hsupp := (supportConstant_pos ε hε).le
  have hb := hbound K N hK hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*sieveNorm K N*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*(C*(K*N)^deltaLoss*(N+K^α))*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) := by
      gcongr
    _ = ((idealDivisors G).card : ℝ)^2*(supportConstant ε hε*N^ε)*C*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*(N+K^α))*∑ j, ‖a j‖^2 := by
      rw [Real.sqrt_div hM0]
      ring
    _ = _ := by
      rw [mul_add, sqrt_div_mul_rpow M K α hM0 hK0]

end CanonicalQuadraticSieve

namespace ShortDraftDescent
open MeasureTheory Filter

theorem integral_geometric_descent
    {Node Parameter : Type*} [MeasurableSpace Parameter]
    (rank : Node → ℕ) (energy mass terminal : Node → ℝ)
    (left right : Node → Parameter → Node)
    (measure : Node → Measure Parameter) (weight : Node → Parameter → ℝ)
    (hweight : ∀ x, ∀ᵐ t ∂measure x, 0 ≤ weight x t)
    (hintegrable : ∀ x, Integrable (fun t => weight x t *
      Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t))) (measure x))
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hchildren : ∀ x, rank x ≠ 0 → ∀ᵐ t ∂measure x,
      rank (left x t) < rank x ∧ rank (right x t) < rank x)
    (hstep : ∀ x, rank x ≠ 0 → energy x ≤ terminal x +
      ∫ t, weight x t * Real.sqrt (energy (left x t)) * Real.sqrt (energy (right x t)) ∂measure x)
    (hbudget : ∀ x, rank x ≠ 0 → terminal x +
      (∫ t, weight x t * Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t)) ∂measure x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have h : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      have hx0 : rank x ≠ 0 := by omega
      have hmono : (∫ t, weight x t * Real.sqrt (energy (left x t)) *
          Real.sqrt (energy (right x t)) ∂measure x) ≤
          ∫ t, weight x t * Real.sqrt (mass (left x t)) *
          Real.sqrt (mass (right x t)) ∂measure x := by
        refine integral_mono_of_nonneg ?_ (hintegrable x) ?_
        · filter_upwards [hweight x] with t ht
          exact mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · filter_upwards [hweight x, hchildren x hx0] with t ht hr
          have hl := ih (rank (left x t)) (by omega) (left x t) rfl
          have hh := ih (rank (right x t)) (by omega) (right x t) rfl
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) ht)
            (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _)
            (mul_nonneg ht (Real.sqrt_nonneg _))
      exact (hstep x hx0).trans ((add_le_add le_rfl hmono).trans (hbudget x hx0))
  intro x
  exact h (rank x) x rfl

end ShortDraftDescent

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic FourierBridge

def halfShellFactor (N q : ℝ) : ℝ := Real.sqrt (N/2) / Real.sqrt q

lemma halfShellFactor_nonneg (N q : ℝ) : 0 ≤ halfShellFactor N q := by
  unfold halfShellFactor
  positivity

lemma halfShellFactor_le_one (N q : ℝ) (hq : 0 < q) (h : N/2 ≤ q) :
    halfShellFactor N q ≤ 1 := by
  unfold halfShellFactor
  exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.sqrt_le_sqrt h)

lemma halfShellFactor_pair (M F N i j : ℝ) (hN : 0 < N) (hi : 0 < i) (hj : 0 < j)
    (hF : 0 < F) :
    (2*M/(F*N))*halfShellFactor N i*halfShellFactor N j =
      M/(Real.sqrt (i*j)*F) := by
  unfold halfShellFactor
  rw [Real.sqrt_mul hi.le]
  have hs := Real.sq_sqrt (show 0 ≤ N/2 by positivity)
  have hsi := (Real.sqrt_pos.mpr hi).ne'
  have hsj := (Real.sqrt_pos.mpr hj).ne'
  field_simp
  rw [hs]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def smallPrincipalCorrection (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) : ℝ :=
  ∑ D ∈ S, ∑ E ∈ T, ∑ i,
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k *
      ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ)‖

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma originalTerm_real_scaling
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (u : n → ℝ) (v : p → ℝ)
    (D E : Ideal O) (i : m) (j : n) (k : p) :
    originalTerm rows left right (fun j => a j*(u j:ℂ)) (fun k => b k*(v k:ℂ)) D E i j k =
      originalTerm rows left right a b D E i j k * (u j:ℂ) * (v k:ℂ) := by
  unfold originalTerm
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hd : D ∣ left j <;> by_cases he : E ∣ right k <;>
    simp only [hc,hd,he,ite_true,ite_false,mul_zero,zero_mul,star_zero,star_mul,Complex.star_def,
      Complex.conj_ofReal] ; ring

theorem smallPrincipalCorrection_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      (2*M/(F*N))*Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hN0 : 0 < N := by linarith
  let u := fun j => halfShellFactor N (Ideal.absNorm (left j) : ℝ)
  let v := fun k => halfShellFactor N (Ideal.absNorm (right k) : ℝ)
  let a' := fun j => a j*(u j:ℂ)
  let b' := fun k => b k*(v k:ℂ)
  have hu (j) : 0 ≤ u j ∧ u j ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hleft j).2.1]) (hleft j).2.1⟩
  have hv (k) : 0 ≤ v k ∧ v k ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hright k).2.1]) (hright k).2.1⟩
  have ha (j) : ‖a' j‖ ≤ ‖a j‖ := by
    simp only [a',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu j).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hu j).2
  have hb (k) : ‖b' k‖ ≤ ‖b k‖ := by
    simp only [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv k).2
  have ht (D E : Ideal O) (i j k) :
      originalTerm rows left right a b D E i j k *
        ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ) =
      ((2*M/(F*N):ℝ):ℂ)*originalTerm rows left right a' b' D E i j k := by
    have hid := halfShellFactor_pair M F N (Ideal.absNorm (left j) : ℝ) (Ideal.absNorm (right k) : ℝ)
      hN0 (by linarith [(hleft j).2.1]) (by linarith [(hright k).2.1]) hF
    rw [←hid, show originalTerm rows left right a' b' D E i j k =
      originalTerm rows left right a b D E i j k*(u j:ℂ)*(v k:ℂ) from
      originalTerm_real_scaling rows left right a b u v D E i j k]
    push_cast
    dsimp only [u,v]
    ring
  have hblock := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows (fun j => ⟨(hleft j).1,(hleft j).2.2⟩)
      (fun k => ⟨(hright k).1,(hright k).2.2⟩) a' b' (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add,logPhase_zero,mul_one] at hblock
  have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N (by linarith) (by linarith) a' a b' b ha hb
  have heq : smallPrincipalCorrection S T rows left right a b M F =
      (2*M/(F*N))*(∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a' b' D E i j k‖) := by
    unfold smallPrincipalCorrection
    simp_rw [ht,←Finset.mul_sum]
    simp only [norm_mul,Complex.norm_of_nonneg (show 0 ≤ 2*M/(F*N) by positivity)]
    simp_rw [←Finset.mul_sum]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hblock.trans (Real.sqrt_le_sqrt hcost)) (by positivity)

end

open ActualEisensteinCubic

theorem HasSieveExponent.small_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (hcut : D₁*D₂ ≤ U*(N*Real.sqrt (F/(M*B)))) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+U*Real.sqrt (M/F)*B^(α-1/2)) := by
  have hb := smallPrincipalCorrection_bound ε hε S T D₁ D₂ B N M F hD₁ hD₂ hN hM hF hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hC := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2*M/(F*N))*(divisorEnergyFactor ε hε N a b*
        (divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss*(N+B^α*(D₁*D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss))*
        ((M/(F*N))*(N+B^α*(D₁*D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁*D₂) U α hM hF (by linarith) (by linarith) hcut)
      (by positivity)

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem truncationError_symmetric_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError P S W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ι _ P _ hinj S W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hp := hb P hinj S W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  calc
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hp
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem primePool_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (_hG : G ≠ 0)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError (fun P : primePool {G} => P.val) Finset.univ W
          X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (supportConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  have hh := hb (fun P : primePool {G} => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe, primePool_singleton_eq_primeSupport] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (support_card_bound ε hε G hG) (by positivity)) (by positivity)

theorem lowPrincipal_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖lowPrincipalError I J W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipalError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ε hε I J hI hJ W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hh := hb ε hε I J hI hJ W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  have hc := (supportConstant_pos ε hε).le
  calc
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hh
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem originalTerm_one_norm_le {m n p : Type*}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖originalTerm rows left right a b 1 1 i j k‖ ≤ ‖a j‖ * ‖b k‖ := by
  classical
  unfold originalTerm
  simp only [one_dvd, ite_true]
  split_ifs with hc
  · simp only [norm_mul, norm_star]
    calc
      _ ≤ (1 * ‖a j‖) * (1 * ‖b k‖) := mul_le_mul
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (by positivity) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem actual_pair_error_energy {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖originalTerm rows cols cols a a 1 1 i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (originalTerm_one_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem finite_ideal_family_card_bound {m : Type*} [Fintype m]
    (I : m → Ideal O) (hI : Function.Injective I) (B : ℝ) (hB : 1 ≤ B)
    (hzero : ∀ i, I i ≠ 0) (hNorm : ∀ i, (Ideal.absNorm (I i) : ℝ) ≤ B) :
    (Fintype.card m : ℝ) ≤ 128 * B := by
  classical
  have hb := DescentFiberCost.finite_ideal_count_real (Finset.univ.image I) B hB
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hzero i)
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hNorm i)
  simpa only [Finset.card_image_of_injective _ hI, Finset.card_univ] using hb

theorem actual_pair_error_ideal_bound {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (actual_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI

end

